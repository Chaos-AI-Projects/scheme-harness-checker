// The size-change layer of Phases 5 and 6, ported from src/harness-checker/termination.ss (HC-16).
//
// Each intra-SCC call gets a size-change graph (see sct.ts) with an arc from caller formal x to
// callee formal y when the argument passed for y is no larger than x: strict when it is an
// sc-decreasing expression of x, non-strict when it is x itself. In a single-function SCC, the
// measure "bound minus x" also gets arcs for each formal x that boundedFormals accepts: strict when
// the argument is an increasing expression of x.
//
// Structural descent (cdr, car, an element) is well-founded, so its arcs may cross argument
// positions. Numeric descent and ascent are bounded only by a base-case test on that parameter, so
// their arcs are kept only when x and y sit in the same position. Without that, (f y (- x 1)) under
// (= x 0) would pass by swapping a negative x out from under its test.
//
// The Scheme threads a type-env through call-sc-graph to reach decreasing-expr?'s record-accessor
// branch. That branch belongs to the types port (HC-18), so no type-env appears here.
//
// collect-intra-scc-calls comes from Phase 6 (termination.ss:2440) because scc-size-change needs it.

import { Dotted, Sym, car, cdr, cadr, cddr, isList, isPair, isSym, sym, type Datum } from "../sexp.ts";
import { cfaHofCallbackPosition } from "./cfa.ts";
import { properPrefix } from "./callgraph.ts";
import type { CfaLambda } from "./cfa.ts";
import { makeScGraph, scCheck, type Arc, type ScGraph, type ScVerdict } from "./sct.ts";
import {
  ascentGuarded,
  bodyBinders,
  decreasingExpr,
  defineNames,
  descentGuarded,
  exprReferencesAny,
  formBinds,
  formalNames,
  guardUpperBoundPairs,
  guardsAt,
  increasingExpr,
  namesBoundAround,
  numericStep,
  upperBoundBaseCases,
  type BoundOk,
  type BoundPair,
  type Guard,
} from "./guards.ts";

export { NUMERIC_STEP_NAMES, numericStep } from "./guards.ts";

const QUOTE = sym("quote");
const SET = sym("set!");
const CAR = sym("car");
const BOUND = sym("bound");

/** termination.ss:1718 size-change-cap. */
export const SIZE_CHANGE_CAP = 1000;

/**
 * termination.ss:1725 sc-decreasing-expr?: decreasingExpr, plus (car e) where e is var or
 * decreases var. Pairs are immutable here, so car, like cdr, shrinks a value. The Scheme's var-type
 * argument is HC-18's; see decreasingExpr.
 */
export function scDecreasingExpr(expr: Datum, v: Datum): boolean {
  if (decreasingExpr(expr, v)) return true;
  if (!(Array.isArray(expr) && expr.length === 2 && expr[0] === CAR)) return false;
  const e = expr[1]!;
  return e === v || scDecreasingExpr(e, v);
}

/** termination.ss:1734 bound-measure: the "bound minus x" measure, (bound . x). */
export function boundMeasure(x: Datum): Datum {
  return new Dotted([BOUND], x);
}

/** termination.ss:1738 set!-targets: every symbol a set! in expr assigns. Shadowing is ignored. */
export function setTargets(expr: Datum): Datum[] {
  if (!isPair(expr)) return [];
  const head = car(expr);
  if (head === QUOTE) return [];
  if (head === SET && isPair(cdr(expr)) && isSym(cadr(expr))) return [cadr(expr), ...setTargets(cddr(expr))];
  return [...setTargets(head), ...setTargets(cdr(expr))];
}

/**
 * termination.ss:1750 unassigned-formals: formals with each one body assigns replaced by a fresh,
 * uninterned symbol, keeping positions. No size-change arc may start from an assigned formal.
 */
export function unassignedFormals(formals: readonly Datum[], body: Datum): Datum[] {
  const targets = setTargets(body);
  return formals.map((f) => (targets.includes(f) ? new Sym(isSym(f) ? `${f.name}%` : "g") : f));
}

/** termination.ss:1756 cfa-full-formals: a cfa lambda's formals with its rest formal as the tail. */
export function cfaFullFormals(l: Pick<CfaLambda, "formals" | "rest">): Datum {
  if (l.rest === null) return [...l.formals];
  if (l.formals.length === 0) return l.rest;
  if (Array.isArray(l.rest)) return [...l.formals, ...l.rest];
  if (l.rest instanceof Dotted) return new Dotted([...l.formals, ...l.rest.items], l.rest.tail);
  return new Dotted([...l.formals], l.rest);
}

/** termination.ss:1760 proper-formals: the proper prefix of a formals list. */
export function properFormals(formals: Datum): Datum[] {
  return [...properPrefix(formals)];
}

/** A call's guards from guardsAt, or "any" to trust numeric arcs unguarded. */
export type CallGuards = readonly Guard[] | "any";

/**
 * termination.ss:1775 call-sc-graph: the size-change graph of one call (callee arg ...).
 * numericStrict false demotes numeric-step arcs to non-strict. bounded: the formals whose "bound
 * minus x" measure gets arcs. guards: the branch tests at the call site. boundOk judges a guard's
 * bound.
 */
export function callScGraph(
  caller: Datum,
  callerFormals: readonly Datum[],
  bounded: readonly Datum[],
  call: readonly Datum[],
  calleeFormals: readonly Datum[],
  numericStrict: boolean,
  guards: CallGuards,
  boundOk: BoundOk,
): ScGraph {
  const guarded = (ok: (x: Datum, gs: readonly Guard[], b: BoundOk) => boolean, x: Datum): boolean =>
    guards === "any" || ok(x, guards, boundOk);
  // The Scheme conses each argument's arcs onto the front; makeScGraph sorts them anyway.
  let acc: Arc[] = [];
  const args = call.slice(1);
  for (let j = 0; j < args.length && j < calleeFormals.length; j++) {
    const a = args[j]!;
    const y = calleeFormals[j]!;
    callerFormals.forEach((x, i) => {
      const placed = i === j || !numericStep(a);
      const arcs: Arc[] = [];
      if (placed && scDecreasingExpr(a, x)) {
        arcs.push([x, y, !numericStep(a) || (numericStrict && guarded(descentGuarded, x))]);
      } else if (a === x) {
        arcs.push([x, y, false]);
      }
      if (bounded.includes(x) && bounded.includes(y)) {
        if (i === j && increasingExpr(a, x)) {
          arcs.push([boundMeasure(x), boundMeasure(y), guarded(ascentGuarded, x)]);
        } else if (a === x) {
          arcs.push([boundMeasure(x), boundMeasure(y), false]);
        }
      }
      acc = [...arcs, ...acc];
    });
  }
  return makeScGraph(caller, call[0]!, acc);
}

/**
 * termination.ss:1812 pure-bound-ops: operators a stable bound may apply, whose result is fixed by
 * their arguments. vector-ref is not one, since vector-set! can raise it.
 */
export const PURE_BOUND_OPS: readonly Sym[] = [
  "length", "vector-length", "string-length", "+", "-", "*", "quotient", "remainder", "modulo", "abs",
  "min", "max", "car", "cdr", "cadr", "cddr",
].map(sym);

/**
 * termination.ss:1830 make-bound-ok?: judges a bound of a self-recursive function stable. It may
 * apply only PURE_BOUND_OPS; every formal it mentions must be passed unchanged in place on every
 * call in calls; no name in it may be in assigned; any other name must not be in local, the names
 * the body binds. calls null: no formal is stable (a mutual SCC or an anonymous cycle). A rest
 * formal is never stable.
 */
export function makeBoundOk(
  formals: Datum,
  calls: readonly (readonly Datum[])[] | null,
  assigned: readonly Datum[],
  local: readonly Datum[],
): BoundOk {
  const proper = properFormals(formals);
  const names: Datum[] = formalNames(formals);
  const inPlace = (z: Datum): boolean => {
    if (calls === null) return false;
    const i = proper.indexOf(z);
    return calls.every((call) => {
      const args = properPrefix(call as Datum[]).slice(1);
      return i < args.length && args[i] === z;
    });
  };
  const stable = (e: Datum): boolean => {
    if (isSym(e)) {
      if (assigned.includes(e)) return false;
      return names.includes(e) ? proper.includes(e) && inPlace(e) : !local.includes(e);
    }
    if (isPair(e)) {
      const head = car(e);
      if (head === QUOTE) return true;
      return isSym(head) && PURE_BOUND_OPS.includes(head) && isList(e) && e.slice(1).every(stable);
    }
    return true;
  };
  return stable;
}

/**
 * termination.ss:1855 bounded-formals: the formals x, from the (x . bound) pairs, whose bound is
 * stable. Newest first, each once.
 */
export function boundedFormals(pairs: readonly BoundPair[], formals: readonly Datum[], stable: BoundOk): Datum[] {
  const acc: Datum[] = [];
  for (const [x, bound] of pairs) {
    if (formals.includes(x) && !acc.includes(x) && stable(bound)) acc.unshift(x);
  }
  return acc;
}

/**
 * termination.ss:1939 sc-check-members: size-change check of one SCC. graphsOf maps numericStrict
 * to the SCC's call graphs. A mutual SCC passes on structural descent alone (numeric arcs demoted)
 * unless every call has a strict arc.
 */
export function scCheckMembers(graphsOf: (numericStrict: boolean) => readonly ScGraph[], memberCount: number): ScVerdict {
  const gs = graphsOf(true);
  const full = scCheck(gs, SIZE_CHANGE_CAP);
  if (full !== "terminates" || memberCount === 1) return full;
  if (gs.every((g) => g.arcs.some((a) => a[2]))) return "terminates";
  return scCheck(graphsOf(false), SIZE_CHANGE_CAP);
}

// ---------------------------------------------------------------
// Intra-SCC calls (Phase 6) and the per-SCC check
// ---------------------------------------------------------------

/** One call collectIntraSccCalls found: the callee, then each argument or false when opaque. */
export type SccCall = readonly Datum[];

// Each call collectIntraSccCalls returns, mapped to the expression it was built from, so guardsAt
// can find its site. The Scheme's weak eq-hashtable call-sites.
const callSites = new WeakMap<SccCall, Datum>();

/** The source expression a collected call was built from. termination.ss:2438 call-sites. */
export function callSiteOf(call: SccCall): Datum | undefined {
  return callSites.get(call);
}

const S = {
  lambda: sym("lambda"),
  caseLambda: sym("case-lambda"),
  define: sym("define"),
  cond: sym("cond"),
  case: sym("case"),
  do: sym("do"),
  let: sym("let"),
  letStar: sym("let*"),
  dynamicWind: sym("dynamic-wind"),
  callWithValues: sym("call-with-values"),
};

const isLambdaForm = (e: Datum): boolean => isPair(e) && (car(e) === S.lambda || car(e) === S.caseLambda);

/**
 * termination.ss:2440 collect-intra-scc-calls: every call in bodyExprs whose operator is one of
 * sccMembers, newest first. An argument that mentions a name rebound around the call is false: it
 * need not decrease the formal. Inside a closure that may run in a later activation, every argument
 * is false. userNames are names the program binds outside bodyExprs: a built-in HOF's name bound
 * there is not that HOF.
 */
export function collectIntraSccCalls(
  bodyExprs: readonly Datum[],
  sccMembers: readonly Datum[],
  userNames: readonly Datum[],
): SccCall[] {
  const calls: SccCall[] = [];

  function opaqueArgs(expr: Datum[], shadowed: readonly Datum[], captured: boolean): SccCall {
    const call = [expr[0]!, ...expr.slice(1).map((a) => (captured || exprReferencesAny(a, shadowed) ? false : a))];
    callSites.set(call, expr);
    return call;
  }

  // Indices of the arguments a built-in calls during this very call.
  function callbackIndices(expr: Datum[], shadowed: readonly Datum[]): number[] {
    const head = expr[0]!;
    if (!isSym(head) || shadowed.includes(head) || userNames.includes(head)) return [];
    if (head === S.dynamicWind) return [0, 1, 2];
    if (head === S.callWithValues) return [0, 1];
    const pos = cfaHofCallbackPosition(head);
    return pos === null ? [] : [pos];
  }

  // An expression whose value may outlive this activation: a lambda there is captured.
  const walkValue = (e: Datum, shadowed: readonly Datum[], captured: boolean): void => {
    if (isPair(e)) walk(e, shadowed, captured || isLambdaForm(e));
  };
  const walkValues = (es: Datum, shadowed: readonly Datum[], captured: boolean): void => {
    for (const e of properPrefix(es)) walkValue(e, shadowed, captured);
  };

  // True when every use of name in exprs is the operator of a call outside any lambda, define,
  // named let, cond, case or do, and nothing there rebinds name.
  function calledInPlaceOnly(name: Datum, exprs: readonly Datum[]): boolean {
    const ok = (e: Datum): boolean => {
      if (isSym(e)) return e !== name;
      if (!isPair(e)) return true;
      if (car(e) === QUOTE) return true;
      if (!isList(e)) return !exprReferencesAny(e, [name]);
      const head = e[0]!;
      if (
        isSym(head) &&
        (head === S.lambda || head === S.caseLambda || head === S.define || head === S.cond || head === S.case ||
          head === S.do || (head === S.let && e.length > 1 && isSym(e[1]!)) || formBinds(e).includes(name as Sym))
      ) {
        return !exprReferencesAny(e, [name]);
      }
      if (head === name) return e.slice(1).every(ok);
      return e.every(ok);
    };
    return exprs.every(ok);
  }

  // (let ((g (lambda ...)) ...) body ...) and let*: a binding's lambda runs here when g is only
  // called in place in its scope.
  function walkLetBindings(
    bindings: Datum[],
    scopeOf: (later: Datum[]) => Datum[],
    shadowed: readonly Datum[],
    captured: boolean,
  ): void {
    bindings.forEach((b, k) => {
      if (!(Array.isArray(b) && b.length === 2)) return;
      const init = b[1]!;
      if (isSym(b[0]!) && isLambdaForm(init) && calledInPlaceOnly(b[0], scopeOf(bindings.slice(k + 1)))) {
        walk(init, shadowed, captured);
      } else {
        walkValue(init, shadowed, captured);
      }
    });
  }

  function walk(expr: Datum, outer: readonly Datum[], captured: boolean): void {
    if (!(Array.isArray(expr) && expr.length > 0) || expr[0] === QUOTE) return;
    const head = expr[0]!;
    const shadowed = isSym(head) ? [...formBinds(expr), ...outer] : outer;
    const keyword = isSym(head) && !shadowed.includes(head) && !userNames.includes(head) ? head : null;
    const cbs = callbackIndices(expr, shadowed);
    if (isSym(head) && sccMembers.includes(head)) calls.unshift(opaqueArgs(expr, shadowed, captured));
    if (keyword === S.cond) {
      // Clauses are not applications: every element of one is an expression.
      for (const c of expr.slice(1)) if (isList(c)) walkValues(c, shadowed, captured);
    } else if (keyword === S.case && expr.length > 1) {
      walkValue(expr[1]!, shadowed, captured);
      for (const c of expr.slice(2)) if (isList(c) && c.length > 0) walkValues(c.slice(1), shadowed, captured);
    } else if (keyword === S.do && expr.length > 2) {
      const specs = expr[1]!;
      if (isList(specs)) {
        for (const spec of specs) if (isList(spec)) walkValues(spec.length > 0 ? spec.slice(1) : [], shadowed, captured);
      }
      if (isList(expr[2]!)) walkValues(expr[2]!, shadowed, captured);
      walkValues(expr.slice(3), shadowed, captured);
    } else if ((keyword === S.let || keyword === S.letStar) && expr.length > 1 && isList(expr[1]!)) {
      const body = expr.slice(2);
      walkLetBindings(
        expr[1] as Datum[],
        keyword === S.let
          ? () => body
          : (later) => [
              ...later.map((b) => (Array.isArray(b) && b.length > 1 ? b[1]! : b)),
              ...body,
            ],
        shadowed,
        captured,
      );
      walkValues(body, shadowed, captured);
    } else {
      // A lambda runs in this activation only when applied on the spot or handed to a built-in
      // HOF's callback slot.
      expr.forEach((sub, k) => {
        const i = k - 1;
        if (isPair(sub)) walk(sub, shadowed, captured || (isLambdaForm(sub) && i !== -1 && !cbs.includes(i)));
      });
    }
  }

  const top = defineNames(bodyExprs);
  for (const e of bodyExprs) walk(e, top, false);
  return calls;
}

/** scc-size-change's verdict: sct's, or "unguarded" when only an unguarded numeric descent exists. */
export type SccVerdict = ScVerdict | "unguarded";

/**
 * termination.ss:1874 scc-size-change: the verdict for the SCC sccNames. formalsOf and bodyOf map
 * a member to its formals (null when they cannot be extracted) and its body expressions. exprs is
 * the whole program, for the names bound around each body. The Scheme's type-env-of argument feeds
 * HC-18's record-accessor descent and is absent here.
 *
 * In a mutual SCC, numeric descent gets no more trust than the per-edge rule gave it, so the SCC
 * passes on structural descent alone or when every call has a strict arc. "unguarded" means descent
 * exists but no test on the descending formal guards it.
 */
export function sccSizeChange(
  sccNames: readonly Sym[],
  formalsOf: (name: Datum) => Datum | null,
  bodyOf: (name: Datum) => readonly Datum[],
  exprs: readonly Datum[],
): SccVerdict {
  const single = sccNames.length === 1;
  const callsOf = (caller: Datum): SccCall[] =>
    collectIntraSccCalls(bodyOf(caller), sccNames, [
      ...formalNames(formalsOf(caller) ?? []),
      ...namesBoundAround(exprs, bodyOf(caller)),
    ]);
  // A guard's bound must not move between calls. In a mutual SCC a formal sits in different
  // positions per member, so none is stable.
  const boundOkOf = (caller: Datum): BoundOk =>
    makeBoundOk(formalsOf(caller) ?? [], single ? callsOf(caller) : null, setTargets([...exprs]), bodyBinders(bodyOf(caller)));
  // The Scheme looks up a missing site as #f, which guardsAt then searches for.
  const guardsOfCall = (caller: Datum, call: SccCall): Guard[] => guardsAt(bodyOf(caller), callSiteOf(call) ?? false) ?? [];

  let bounded: Datum[] = [];
  const first = sccNames[0]!;
  const firstFormals = formalsOf(first);
  if (single && firstFormals !== null) {
    const formals = properFormals(firstFormals);
    // Candidates: the upper-bound base cases, and the upper-bound tests guarding each call (HC-7).
    bounded = boundedFormals(
      [
        ...upperBoundBaseCases(bodyOf(first), first, formals),
        ...callsOf(first).flatMap((call) => guardUpperBoundPairs(guardsOfCall(first, call), formals)),
      ],
      formals,
      boundOkOf(first),
    );
  }

  const graphs = (guarded: boolean) => (numericStrict: boolean): ScGraph[] =>
    sccNames.flatMap((caller) => {
      const callerFormals = unassignedFormals(properFormals(formalsOf(caller) ?? []), [...bodyOf(caller)]);
      return callsOf(caller).map((call) =>
        callScGraph(
          caller,
          callerFormals,
          bounded,
          call,
          properFormals(formalsOf(call[0]!) ?? []),
          numericStrict,
          guarded ? guardsOfCall(caller, call) : "any",
          boundOkOf(caller),
        ),
      );
    });

  const result = scCheckMembers(graphs(true), sccNames.length);
  if (result === "no-descent" && scCheckMembers(graphs(false), sccNames.length) === "terminates") return "unguarded";
  return result;
}
