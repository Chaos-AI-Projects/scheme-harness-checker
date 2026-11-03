// Phase 2b of termination.ss (HC-17): higher-order call edges from 0CFA. buildCallGraph sees a call
// only when its operator names a definition. cfaAnalyzeProgram makes every other call visible to it,
// and to Phases 5 and 6, by rewriting the program: at each call site where 0CFA finds a lambda the
// name lookup misses, it inserts a synthesized call to that lambda's owner, in place, so the
// decreasing and base-case checks see it in its real branch. The rewritten program is for analysis
// only and is never run.
//
// The owner of a lambda is the nearest enclosing define or letrec binding. An anonymous lambda with
// none owns itself; it is wrapped as (letrec ((lambda@N <lambda>)) lambda@N) so it becomes a
// definition. A call into an anonymous lambda owned by the caller is a nested helper and adds no edge.

import { car, Dotted, elements, equal, isList, isPair, isSym, sym, type Datum, type Sym } from "../sexp.ts";
import { tarjanScc } from "./callgraph.ts";
import { cfaAnalyze, cfaLambdaRef, type CfaLambda, type CfaOptions, type CfaResult, type CfaSite, type Callee, type Via } from "./cfa.ts";
import { bodyBinders, exprReferencesAny, guardsAt, namesShadowedAt } from "./guards.ts";
import { acyclic } from "./mutualrec.ts";
import { hasBaseCaseBy } from "./namedlet.ts";
import { callScGraph, cfaFullFormals, makeBoundOk, scCheckMembers, setTargets, unassignedFormals } from "./sizechange.ts";
import type { ScGraph } from "./sct.ts";
import type { TerminationKind, TerminationViolation } from "./violation.ts";

/**
 * termination.ss:460 cfa-element-marker: head of the synthesized argument meaning "an element of
 * this list". It is not on the whitelist, so no checked program can contain it.
 */
export const CFA_ELEMENT_MARKER = sym("%cfa-element");
/** termination.ss:464 cfa-spread-marker: an element of apply's trailing list, called once. */
export const CFA_SPREAD_MARKER = sym("%cfa-spread");

const S = {
  quote: sym("quote"),
  begin: sym("begin"),
  letrec: sym("letrec"),
  lambda: sym("lambda"),
  arrow: sym("=>"),
  foldLeft: sym("fold-left"),
  foldRight: sym("fold-right"),
};

/**
 * termination.ss:473 cfa-list-hof-names: list HOFs whose callback receives list elements. Vector and
 * string HOFs are left out, since vector-set! can make a vector contain itself.
 */
const CFA_LIST_HOF_NAMES: ReadonlySet<Sym> = new Set(
  "map for-each filter remove remp fold-left fold-right find exists for-all memp partition".split(" ").map(sym),
);

/**
 * termination.ss:484 cfa-hof-callback-args: the synthesized arguments of a built-in HOF's callback
 * invocation at site e, for a callback with n formals. Position i gets (%cfa-element <list>) when it
 * receives elements of a syntactic list argument, else false. The site's arguments are trusted only
 * when its head is the HOF 0CFA resolved the operator to, so (let ((map fold-left)) ...) proves
 * nothing.
 */
export function cfaHofCallbackArgs(e: Datum, name: string | null, n: number): Datum[] {
  const h = isList(e) && e.length > 0 ? e[0]! : null;
  const args = isList(e) && h !== null && isSym(h) && name !== null && h.name === name && CFA_LIST_HOF_NAMES.has(h) ? e.slice(1) : null;
  const elementOf = (k: number): Datum => (args !== null && k < args.length ? [CFA_ELEMENT_MARKER, args[k]!] : false);
  const out: Datum[] = [];
  for (let i = 0; i < n; i++) {
    if (args === null) out.push(false);
    // (fold-left f init l ...): the callback gets (acc e ...).
    else if (h === S.foldLeft) out.push(i === 0 ? false : elementOf(i + 1));
    // (fold-right f init l ...): the callback gets (e ... acc).
    else if (h === S.foldRight) out.push(i + 2 < args.length ? elementOf(i + 2) : false);
    else out.push(elementOf(i + 1));
  }
  return out;
}

/** termination.ss:509 cfa-apply-args: (apply f a ... lst) gives leading arguments, then elements of lst. */
export function cfaApplyArgs(e: Datum, n: number): Datum[] {
  if (!isList(e) || e.length < 3) return [];
  const more = e.slice(2);
  const lst = more[more.length - 1]!;
  const leading = more.slice(0, -1);
  const out: Datum[] = [];
  for (let i = 0; i < n; i++) out.push(i < leading.length ? leading[i]! : [CFA_SPREAD_MARKER, lst]);
  return out;
}

/** termination.ss:523 cfa-anon-node-name. */
export function cfaAnonNodeName(label: number): Sym {
  return sym(`lambda@${label}`);
}

// A walk of x by car and cdr, as the Scheme's (memq x sites) recursion is: every tail of a list is a
// candidate of its own, and a tail that reads (quote ...) hides the rest of the list.
function containsAny(x: Datum, targets: ReadonlySet<Datum>): boolean {
  if (targets.has(x)) return true;
  if (!isPair(x)) return false;
  const items = x instanceof Dotted ? x.items : x;
  const tail: Datum = x instanceof Dotted ? x.tail : [];
  for (const head of items) {
    if (head === S.quote) return false;
    if (containsAny(head, targets)) return true;
  }
  return containsAny(tail, targets);
}

export interface CfaProgramAnalysis {
  /** The program with synthesized calls; the input array itself when nothing was synthesized. */
  rewritten: readonly Datum[];
  violations: TerminationViolation[];
}

/** termination.ss:526 cfa-rewrite-program. */
export function cfaRewriteProgram(exprs: readonly Datum[]): readonly Datum[] {
  return cfaAnalyzeProgram(exprs).rewritten;
}

/**
 * termination.ss:534 cfa-analyze-program: the rewritten program, and the violations 0CFA finds that
 * the rewrite cannot express. Those are call sites whose operator 0CFA cannot follow
 * (unresolved-call), cycles made only of anonymous lambdas, which have no definition to carry a call
 * edge, and calls into a named let other than by its name.
 */
export function cfaAnalyzeProgram(exprs: readonly Datum[], options: CfaOptions = {}): CfaProgramAnalysis {
  const result: CfaResult = cfaAnalyze(exprs, options);
  const siteSynth = new Map<Datum, Datum[][]>();
  const wrap = new Map<Datum, Sym>();

  const lam = (label: number): CfaLambda => cfaLambdaRef(result, label)!;
  const named = (l: CfaLambda): boolean => l.kind === "define" || l.kind === "letrec";

  const namedOwner = (label: number | null): Sym | null => {
    if (label === null) return null;
    const l = lam(label);
    return named(l) ? l.name : namedOwner(l.parent);
  };

  // An anonymous lambda can own itself only when its source is a lambda form we can wrap.
  const anonNode = (label: number): boolean => {
    const l = lam(label);
    if (l.kind !== "lambda" || namedOwner(label) !== null) return false;
    return isPair(l.expr) && isList(l.expr) && l.expr[0] === S.lambda;
  };

  const nodeLambda = (label: number): boolean => named(lam(label)) || anonNode(label);

  // The owner node's name, or null for top-level code and top-level named lets. A named let runs
  // inside the lambda that encloses it, so it shares that lambda's owner, anonymous node included.
  const owner = (label: number | null): Sym | null => {
    if (label === null) return null;
    const n = namedOwner(label);
    if (n !== null) return n;
    if (anonNode(label)) {
      wrap.set(lam(label).expr, cfaAnonNodeName(label));
      return cfaAnonNodeName(label);
    }
    if (lam(label).kind === "named-let") return owner(lam(label).parent);
    return null;
  };

  // A lambda is a leaf when no call site inside it, at any depth, can invoke a lambda. Calling a
  // leaf cannot re-enter any definition, so it adds no edge.
  const inside = (label: number | null, ancestor: number): boolean =>
    label !== null && (label === ancestor || inside(lam(label).parent, ancestor));

  const leafLambda = (label: number): boolean =>
    !result.sites.some((site) => inside(site.caller, label) && (site.callees.length > 0 || site.unresolved));

  const synthArgs = (e: Datum, via: Via, l: CfaLambda): Datum[] => {
    const n = l.formals.length;
    if (typeof via === "object") return cfaHofCallbackArgs(e, via.hof, n);
    if (via === "direct") return isList(e) ? e.slice(1) : [];
    if (via === "cond-arrow") return [car(e)];
    if (via === "apply") return cfaApplyArgs(e, n);
    return [];
  };

  const synthCalls = (site: CfaSite): Datum[][] => {
    const e = site.expr;
    const from = owner(site.caller);
    if (from === null) return [];
    const acc: Datum[][] = [];
    for (const { label, via } of site.callees) {
      const to = owner(label);
      let call: Datum[] | null;
      if (to === null) call = null;
      // A nested helper of the caller: intraprocedural.
      else if (!nodeLambda(label) && to === from) call = null;
      else if (!nodeLambda(label) && leafLambda(label)) call = null;
      // A lambda inside another definition: an edge to that owner whose arguments prove nothing.
      else if (!nodeLambda(label)) call = [to];
      // Already a call by name.
      else if (via === "direct" && isList(e) && e.length > 0 && e[0] === to) call = null;
      else call = [to, ...synthArgs(e, via, lam(label))];
      if (call !== null && !acc.some((c) => equal(c, call))) acc.unshift(call);
    }
    return acc;
  };

  const condArrowClause = (e: Datum): boolean => isList(e) && e.length === 3 && e[1] === S.arrow;

  const rw = (e: Datum): Datum => {
    if (!isPair(e) || (isList(e) && e[0] === S.quote)) return e;
    const e2 = rwList(e);
    const synth = siteSynth.get(e);
    let e3: Datum;
    if (synth === undefined) e3 = e2;
    else if (condArrowClause(e)) e3 = [...(e2 as Datum[]), ...[...synth].reverse()];
    else e3 = [S.begin, e2, ...[...synth].reverse()];
    const w = wrap.get(e);
    return w === undefined ? e3 : [S.letrec, [[w, e3]], w];
  };

  const rwList = (e: Datum): Datum => {
    if (e instanceof Dotted) return new Dotted(e.items.map(rw), e.tail);
    return (e as Datum[]).map(rw);
  };

  const violation = (kind: TerminationKind, fn: Sym | null, expr: Datum, reason: string): TerminationViolation => ({
    kind,
    function: fn,
    expr,
    reason,
  });

  // A call site whose operator set can hold a value 0CFA cannot follow.
  const unresolvedViolations = (): TerminationViolation[] => {
    const acc: TerminationViolation[] = [];
    for (const site of result.sites) {
      if (site.unresolved) {
        acc.unshift(
          violation("unresolved-call", owner(site.caller), site.expr, "operator may be a value the control-flow analysis cannot follow"),
        );
      }
    }
    return acc;
  };

  // A call from a definition into a lambda that has no owner: a top-level case-lambda clause or
  // named let. No edge can be drawn to it, so unless it is a leaf it may call back into the caller
  // unseen, and the call fails closed.
  const unownedCalleeViolations = (): TerminationViolation[] => {
    const acc: TerminationViolation[] = [];
    for (const site of result.sites) {
      const from = owner(site.caller);
      if (from !== null && site.callees.some(({ label }) => owner(label) === null && !leafLambda(label))) {
        acc.unshift(
          violation("unresolved-call", from, site.expr, "calls a top-level case-lambda clause or named let that may call back"),
        );
      }
    }
    return acc;
  };

  // Anonymous lambdas that no rewrite turns into a definition: those nested in a definition, and
  // top-level case-lambda clauses. Calls among them carry no edge in the definition graph, so a cycle
  // made only of them is checked here, on the lambda-level graph, with the same size-change check as
  // definition SCCs.
  const anonMember = (label: number): boolean => lam(label).kind === "lambda" && !anonNode(label);

  // A named let's body runs inside the lambda that encloses it, so a call made from a named let is a
  // call by that lambda. Its own loop calls are Phase 4's; calls out of it must not drop off the graph.
  const effectiveCaller = (label: number | null): number | null => {
    if (label === null) return null;
    return lam(label).kind === "named-let" ? effectiveCaller(lam(label).parent) : label;
  };

  type AnonEdge = readonly [caller: number, callee: number, site: CfaSite, entry: Callee];

  const anonCycleViolations = (): TerminationViolation[] => {
    // (caller callee site entry) among anonymous lambdas of one owner, newest first.
    const edges: AnonEdge[] = [];
    for (const site of result.sites) {
      const c = effectiveCaller(site.caller);
      if (c === null || !anonMember(c)) continue;
      for (const entry of site.callees) {
        const b = entry.label;
        if (anonMember(b) && namedOwner(b) === namedOwner(c)) edges.unshift([c, b, site, entry]);
      }
    }
    // The Scheme builds this from an eqv-hashtable, whose entry order is its own; the SCCs are the
    // same sets either way, and violations compare as sets.
    const succ = new Map<number, number[]>();
    for (const [c, b] of edges) {
      const ss = succ.get(c) ?? [];
      if (!ss.includes(b)) succ.set(c, [b, ...ss]);
    }
    const sccs = tarjanScc([...succ.entries()]);
    const sccOf = (label: number): number[] | undefined => sccs.find((scc) => scc.includes(label));
    const inCycle = (e: AnonEdge): boolean => {
      const scc = sccOf(e[0]);
      return scc !== undefined && scc.includes(e[1]) && (scc.length > 1 || e[0] === e[1]);
    };
    // The size-change graph of one intra-cycle call. An argument that mentions a name rebound around
    // the call site proves nothing, nor does any argument when the site is not found.
    const edgeScGraph = (numericStrict: boolean, e: AnonEdge): ScGraph => {
      const caller = lam(e[0]);
      const callerBody = elements(caller.body);
      const siteExpr = e[2].expr;
      const shadowed = namesShadowedAt(callerBody, siteExpr);
      const args = synthArgs(siteExpr, e[3].via, lam(e[1])).map((a) =>
        shadowed !== null && !exprReferencesAny(a, shadowed) ? a : false,
      );
      return callScGraph(
        e[0],
        unassignedFormals(caller.formals, caller.body),
        [],
        [e[1], ...args],
        lam(e[1]).formals,
        numericStrict,
        guardsAt(callerBody, siteExpr) ?? [],
        makeBoundOk(cfaFullFormals(caller), null, setTargets(exprs as Datum[]), bodyBinders(callerBody)),
      );
    };
    // Numeric descent stops only at a base-case test, so every cycle needs a member with a branch,
    // guarded by a test on its formals, that makes none of the cycle's calls.
    const sccBaseCase = (scc: readonly number[], es: readonly AnonEdge[]): boolean => {
      const sites = new Set<Datum>(es.map((e) => e[2].expr));
      const callsCycle = (x: Datum): boolean => containsAny(x, sites);
      const unbased = scc.filter((label) => {
        const l = lam(label);
        return !hasBaseCaseBy(elements(l.body), l.formals, callsCycle);
      });
      return acyclic(unbased, (label) =>
        es.filter((e) => e[0] === label).map((e) => e[1]).filter((c) => unbased.includes(c)),
      );
    };
    // Each cyclic SCC must pass the size-change check, like a definition SCC in Phases 5 and 6, and
    // have a base case.
    const acc: TerminationViolation[] = [];
    for (const scc of sccs) {
      const es = edges.filter((e) => inCycle(e) && scc.includes(e[0]));
      if (es.length === 0) continue;
      const e = es[0]!;
      let progress: string = scCheckMembers((numericStrict) => es.map((x) => edgeScGraph(numericStrict, x)), scc.length);
      if (progress === "terminates" && !sccBaseCase(scc, es)) progress = "no-base-case";
      if (progress === "terminates") continue;
      acc.unshift(
        violation(
          progress === "limit" ? "size-change-limit" : progress === "no-base-case" ? "no-base-case" : "no-decreasing-arg",
          namedOwner(e[0]) ?? cfaAnonNodeName(e[0]),
          e[2].expr,
          progress === "no-base-case"
            ? "anonymous lambda recursion with no base case"
            : "anonymous lambda recursion with no decreasing argument",
        ),
      );
    }
    return acc;
  };

  // Phase 4 sees a named let's recursion only as calls by its name. Any other call into a named let
  // that can call a lambda, through an alias, a HOF or apply, may re-enter the loop unseen, so it
  // fails closed.
  const namedLetAliasViolations = (): TerminationViolation[] => {
    const acc: TerminationViolation[] = [];
    for (const site of result.sites) {
      const e = site.expr;
      for (const { label, via } of site.callees) {
        const l = lam(label);
        if (
          l.kind === "named-let" &&
          via !== "named-let" &&
          via !== "escape" &&
          !(via === "direct" && isList(e) && e.length > 0 && e[0] === l.name) &&
          !leafLambda(label)
        ) {
          acc.unshift(violation("named-let-alias", owner(site.caller), e, `named-let "${l.name!.name}" called other than by its name`));
        }
      }
    }
    return acc;
  };

  for (const site of result.sites) {
    const calls = synthCalls(site);
    if (calls.length > 0) siteSynth.set(site.expr, calls);
  }

  const violations = [
    ...unresolvedViolations(),
    ...unownedCalleeViolations(),
    ...anonCycleViolations(),
    ...namedLetAliasViolations(),
  ];
  return { rewritten: siteSynth.size === 0 ? exprs : exprs.map(rw), violations };
}
