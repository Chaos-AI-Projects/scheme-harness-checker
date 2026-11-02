// Phase 6 of termination.ss (HC-17): mutual recursion. Every SCC of two or more definitions must make
// size-change progress round each of its cycles, and every cycle must pass through a member with a
// base case of its own.

import { car, caddr, cadr, cddr, cdddr, cdr, Dotted, isPair, isSym, sym, type Datum, type Sym } from "../sexp.ts";
import { buildCallGraph, callGraphEdges, extractDefinitions, properPrefix, tarjanScc, type CallGraph } from "./callgraph.ts";
import { findDefinitionForm, findFormalsFor } from "./directrec.ts";
import { equalityStopHint, exprReferencesAny, formalNames, numericallyStepped, safeIntegerHint } from "./guards.ts";
import { baseCaseTest, condFallThroughTest, negatedBaseCaseTest } from "./namedlet.ts";
import { sccSizeChange } from "./sizechange.ts";
import type { TerminationKind, TerminationViolation } from "./violation.ts";

const S = {
  quote: sym("quote"),
  define: sym("define"),
  if: sym("if"),
  cond: sym("cond"),
  when: sym("when"),
  unless: sym("unless"),
  else: sym("else"),
  ellipsis: sym("..."),
};

/**
 * termination.ss:2602 contains-scc-call?, walked by car and cdr as the Scheme walks it. Each tail of
 * a list is tested as a form in its own right, so a member's name anywhere in a list counts, and a
 * tail that reads (quote ...) hides the rest of the list.
 */
export function containsSccCall(expr: Datum, members: readonly Datum[]): boolean {
  if (!isPair(expr)) return false;
  const items = expr instanceof Dotted ? expr.items : expr;
  const tail: Datum = expr instanceof Dotted ? expr.tail : [];
  for (let i = 0; i < items.length; i++) {
    const head = items[i]!;
    if (head === S.quote) return false;
    if (isSym(head) && members.includes(head)) return true;
    if (containsSccCall(head, members)) return true;
  }
  return containsSccCall(tail, members);
}

/**
 * termination.ss:2701 acyclic?: whether the graph over nodes, with successors succ, has no cycle.
 */
export function acyclic<N>(nodes: readonly N[], succ: (n: N) => readonly N[]): boolean {
  const state = new Map<N, "active" | "done">();
  const visit = (n: N): boolean => {
    const st = state.get(n);
    if (st === "active") return false;
    if (st === "done") return true;
    state.set(n, "active");
    const ok = succ(n).every(visit);
    state.set(n, "done");
    return ok;
  };
  return nodes.every(visit);
}

/**
 * termination.ss:2596 scc-has-base-case?: whether every cycle in the SCC passes through a member
 * with a base case of its own, a branch that calls no member. Its tests must be base-case tests on
 * some member's formals.
 */
export function sccHasBaseCase(exprs: readonly Datum[], members: readonly Sym[], graph: CallGraph): boolean {
  const vars = members.flatMap((m) => findFormalsFor(exprs, m) ?? []);
  const calls = (e: Datum): boolean => containsSccCall(e, members);
  let found = false;

  function walk(expr: Datum): void {
    if (found || !isPair(expr) || car(expr) === S.quote) return;
    const head = car(expr);
    if (head === S.if) {
      if (!isPair(cdr(expr)) || !isPair(cddr(expr))) return;
      const test = cadr(expr);
      const consequent = caddr(expr);
      const alternative = isPair(cdddr(expr)) ? car(cdddr(expr)) : null;
      if (
        !calls(test) &&
        ((baseCaseTest(test, vars) && !calls(consequent)) ||
          (negatedBaseCaseTest(test, vars) && !(alternative !== null && alternative !== false && calls(alternative))))
      ) {
        found = true;
      }
      walk(consequent);
      if (alternative !== null && alternative !== false) walk(alternative);
    } else if (head === S.cond) {
      for (const clause of properPrefix(cdr(expr))) {
        if (!isPair(clause) || !isPair(cdr(clause))) continue;
        const body = cdr(clause);
        if ((car(clause) === S.else || baseCaseTest(car(clause), vars)) && !calls(body)) found = true;
        properPrefix(body).forEach(walk);
      }
      const test = condFallThroughTest(expr);
      if (test !== null && !calls(test) && negatedBaseCaseTest(test, vars)) found = true;
    } else if (head === S.when || head === S.unless) {
      if (!isPair(cdr(expr))) return;
      const test = cadr(expr);
      const body = cddr(expr);
      // The test must mention a formal, or the implicit void branch may be unreachable.
      if (calls(body) && !calls(test) && exprReferencesAny(test, vars)) found = true;
      properPrefix(body).forEach(walk);
    } else {
      if (isPair(head)) walk(head);
      for (const sub of properPrefix(cdr(expr))) if (isPair(sub)) walk(sub);
    }
  }

  const defs = extractDefinitions(exprs);
  const unbased = members.filter((m) => {
    found = false;
    const entry = defs.find(([n]) => n === m);
    if (entry) entry[1].forEach(walk);
    return !found;
  });
  return acyclic(unbased, (m) => callGraphEdges(graph, m).filter((c) => unbased.includes(c)));
}

// termination.ss:2826 sort-symbols*, joined as the violation reasons show the group.
function groupString(names: readonly Sym[]): string {
  const sorted = [...names].sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
  return `(${sorted.map((n) => n.name).join(", ")})`;
}

/**
 * termination.ss:2726 analyze-mutual-recursion: the violations of every SCC of two or more
 * definitions, one per member, in SCC order. The Scheme's type-env and param-types arguments scope
 * record types for HC-18 and are absent here.
 */
export function analyzeMutualRecursion(exprs: readonly Datum[]): TerminationViolation[] {
  const graph = buildCallGraph(exprs);
  const defs = extractDefinitions(exprs);
  const violations: TerminationViolation[] = [];
  const add = (kind: TerminationKind, name: Sym, reason: (form: Datum | null) => string): void => {
    const form = findDefinitionForm(exprs, name);
    violations.push({ kind, function: name, expr: form ?? [S.define, name, S.ellipsis], reason: reason(form) });
  };
  const formalsOf = (name: Datum): Datum[] | null => findFormalsFor(exprs, name as Sym);
  const bodyOf = (name: Datum): Datum[] => defs.find(([n]) => n === name)?.[1] ?? [];

  for (const scc of tarjanScc(graph)) {
    if (scc.length < 2) continue;
    // A member without formals cannot be checked: fail closed.
    const progress = scc.some((n) => (formalsOf(n)?.length ?? 0) === 0)
      ? "no-descent"
      : sccSizeChange(scc, formalsOf, bodyOf, exprs);
    const allEdgesDecrease =
      progress === "terminates" || (progress === "unguarded" && !sccHasBaseCase(exprs, scc, graph));
    const group = groupString(scc);
    if (progress === "limit") {
      for (const n of scc) add("size-change-limit", n, () => "mutual recursion group exceeds the size-change analysis limit");
    } else if (!allEdgesDecrease) {
      for (const n of scc) {
        add(
          "no-decreasing-arg",
          n,
          (form) => `mutual recursion group ${group} has no decreasing argument across call edges${
            equalityStopHint(form ?? false) || safeIntegerHint(numericallyStepped([form ?? false], formalsIn(form ?? false)))}`,
        );
      }
    } else if (!sccHasBaseCase(exprs, scc, graph)) {
      for (const n of scc) add("no-base-case", n, () => `mutual recursion group ${group} has no reachable base case`);
    }
  }
  return violations;
}

// The formals of a (define (f x ...) ...) form, for safeIntegerHint.
function formalsIn(form: Datum): Datum[] {
  return Array.isArray(form) && form.length > 1 && Array.isArray(form[1]) ? formalNames(form[1].slice(1)) : [];
}
