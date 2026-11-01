// Phase 5 of termination.ss (HC-17): direct recursion. A definition whose SCC is itself alone, with a
// self-edge, must make size-change progress on its formals and must have a branch that does not
// recurse.

import { caadr, car, cadr, caddr, cdadr, cddr, cdr, isList, isPair, isSym, sym, type Datum, type Sym } from "../sexp.ts";
import { buildCallGraph, callGraphEdges, extractDefinitions, properPrefix, tarjanScc } from "./callgraph.ts";
import { equalityStopHint } from "./guards.ts";
import { hasBaseCase } from "./namedlet.ts";
import { sccSizeChange } from "./sizechange.ts";
import type { TerminationKind, TerminationViolation } from "./violation.ts";

const DEFINE = sym("define");
const LAMBDA = sym("lambda");
const LETREC = sym("letrec");
const LETREC_STAR = sym("letrec*");
const ELLIPSIS = sym("...");

const isLambdaWithList = (d: Datum): boolean => isPair(d) && car(d) === LAMBDA && isPair(cdr(d)) && isList(cadr(d));

/**
 * termination.ss:1957 extract-formals: the formals of (define (name . formals) ...), of
 * (define name (lambda formals ...)), or of the letrec binding (name (lambda formals ...)). Null when
 * they are not a proper list, so a rest argument proves no descent.
 */
export function extractFormals(expr: Datum): Datum[] | null {
  if (!isPair(expr)) return null;
  const head = car(expr);
  const rest = cdr(expr);
  if (head === DEFINE && isPair(rest) && isPair(car(rest)) && isSym(caadr(expr))) {
    const formals = cdadr(expr);
    return isList(formals) ? formals : null;
  }
  if (head === DEFINE && isPair(rest) && isSym(car(rest)) && isPair(cddr(expr)) && isLambdaWithList(caddr(expr))) {
    return cadr(caddr(expr)) as Datum[];
  }
  if (isSym(head) && isPair(rest) && isLambdaWithList(car(rest))) return cadr(car(rest)) as Datum[];
  return null;
}

/**
 * The result for the first form in exprs that defines name, searched as termination.ss:1994
 * find-definition-form and 2039 find-formals-for both search: a define of it, or a letrec binding it,
 * in walk order with operator positions included. onDefine and onBinding give the result for each
 * kind of match. As in the Scheme, a null result does not end the search, and quoted data is not
 * skipped.
 */
function searchDefinition<T>(
  exprs: readonly Datum[],
  name: Sym,
  onDefine: (form: Datum) => T,
  onBinding: (letrec: Datum, binding: Datum) => T,
  defineByName: (form: Datum) => boolean,
): T | null {
  let result: T | null = null;
  const set = (value: T): void => {
    result = value;
  };
  function search(expr: Datum): void {
    if (result !== null || !isPair(expr)) return;
    const head = car(expr);
    const rest = cdr(expr);
    if (head === DEFINE && isPair(rest) && isPair(car(rest)) && car(car(rest)) === name) {
      set(onDefine(expr));
    } else if (head === DEFINE && isPair(rest) && car(rest) === name && defineByName(expr)) {
      set(onDefine(expr));
    } else if ((head === LETREC || head === LETREC_STAR) && isPair(rest) && isPair(car(rest))) {
      for (const binding of properPrefix(car(rest))) {
        if (result === null && isPair(binding) && car(binding) === name) set(onBinding(expr, binding));
      }
      for (const binding of properPrefix(car(rest))) {
        if (isPair(binding) && isPair(cdr(binding))) search(cadr(binding));
      }
      searchAll(cddr(expr));
    } else {
      searchAll(expr);
    }
  }
  function searchAll(lst: Datum): void {
    for (const sub of properPrefix(lst)) if (isPair(sub)) search(sub);
  }
  exprs.forEach(search);
  return result;
}

/** termination.ss:1994 find-definition-form: the form defining name, a letrec for a binding. */
export function findDefinitionForm(exprs: readonly Datum[], name: Sym): Datum | null {
  return searchDefinition(exprs, name, (form) => form, (letrec) => letrec, () => true);
}

/**
 * termination.ss:2039 find-formals-for: the formals of name's first definition whose formals can be
 * extracted, or null.
 */
export function findFormalsFor(exprs: readonly Datum[], name: Sym): Datum[] | null {
  return searchDefinition<Datum[] | null>(
    exprs,
    name,
    extractFormals,
    (_letrec, binding) => extractFormals(binding),
    (form) => isPair(cddr(form)),
  );
}

/**
 * termination.ss:2091 analyze-direct-recursion: the violations of every directly recursive
 * definition, in SCC order. The Scheme's type-env and param-types arguments scope record types for
 * HC-18 and are absent here.
 */
export function analyzeDirectRecursion(exprs: readonly Datum[]): TerminationViolation[] {
  const graph = buildCallGraph(exprs);
  const definitions = extractDefinitions(exprs);
  const violations: TerminationViolation[] = [];
  const add = (kind: TerminationKind, name: Sym, expr: Datum, reason: string): void => {
    violations.push({ kind, function: name, expr, reason });
  };

  for (const scc of tarjanScc(graph)) {
    const name = scc[0]!;
    if (scc.length !== 1 || !callGraphEdges(graph, name).includes(name)) continue;
    const formals = findFormalsFor(exprs, name);
    const body = definitions.find(([n]) => n === name)?.[1] ?? [];
    const form = findDefinitionForm(exprs, name) ?? [DEFINE, name, ELLIPSIS];
    // Formals that cannot be extracted (case-lambda, rest arguments) prove no descent, so they fail
    // closed.
    const progress =
      formals === null || formals.length === 0
        ? "no-descent"
        : sccSizeChange(scc, (n) => findFormalsFor(exprs, n as Sym), () => body, exprs);
    const label = `recursive function "${name.name}"`;
    if (progress === "limit") {
      add("size-change-limit", name, form, `${label} exceeds the size-change analysis limit`);
    } else if (progress === "no-descent" || (progress === "unguarded" && hasBaseCase(body, name, formals ?? []))) {
      add("no-decreasing-arg", name, form, `${label} has no decreasing argument in recursive call(s)${equalityStopHint(body)}`);
    } else if (!hasBaseCase(body, name, formals ?? [])) {
      add("no-base-case", name, form, `${label} has no reachable base case`);
    }
  }
  return violations;
}
