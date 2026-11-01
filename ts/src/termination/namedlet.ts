// Phase 4 of termination.ss (HC-16): the named-let pass. A named let that recurses must make
// progress on its loop variables, judged as Phase 5 judges a directly recursive definition, and must
// have a branch that does not recurse.

import { car, caddr, cadr, cdr, cddr, cdddr, elements, isList, isPair, isSym, sym, type Datum, type Sym } from "../sexp.ts";
import { properPrefix } from "./callgraph.ts";
import { containsCall, equalityStopHint, exprReferencesAny, lowerPassTest } from "./guards.ts";
import { sccSizeChange } from "./sizechange.ts";
import type { TerminationKind, TerminationViolation } from "./violation.ts";

const S = {
  quote: sym("quote"),
  define: sym("define"),
  lambda: sym("lambda"),
  let: sym("let"),
  if: sym("if"),
  cond: sym("cond"),
  when: sym("when"),
  unless: sym("unless"),
  else: sym("else"),
  not: sym("not"),
  pair: sym("pair?"),
  null: sym("null?"),
  zero: sym("zero?"),
  eq: sym("="),
  lt: sym("<"),
  le: sym("<="),
  gt: sym(">"),
  ge: sym(">="),
};

/**
 * termination.ss:1280 base-case-test?: a test whose truth ends the recursion on one of vars.
 * (= v N) either way round, (zero? v), (null? v), (not (pair? v)), and (< v N), (<= v N),
 * (> v N), (>= v N) and the mirrors of the first two, where v is in vars and N is not. The
 * Scheme's type-env argument is accepted there but never read.
 */
export function baseCaseTest(expr: Datum, vars: readonly Datum[]): boolean {
  if (!isPair(expr)) return false;
  const head = car(expr);
  const rest = cdr(expr);
  if (head === S.zero || head === S.null) return isPair(rest) && vars.includes(car(rest));
  if (head === S.not) {
    const t = isPair(rest) ? car(rest) : null;
    return t !== null && isPair(t) && car(t) === S.pair && isPair(cdr(t)) && vars.includes(cadr(t));
  }
  if (!isPair(rest) || !isPair(cdr(rest))) return false;
  const a = car(rest);
  const b = cadr(rest);
  const left = vars.includes(a) && !vars.includes(b);
  const right = !vars.includes(a) && vars.includes(b);
  if (head === S.eq) return left || right;
  if (head === S.lt || head === S.le) return left;
  if (head === S.gt || head === S.ge) return left || right;
  return false;
}

/**
 * termination.ss:1351 negated-base-case-test?: a test whose falsity is a base case. (pair? v),
 * (not t) for a base-case t, or a lower-pass test such as (> v 0) whose bound is not in vars (HC-8).
 */
export function negatedBaseCaseTest(expr: Datum, vars: readonly Datum[]): boolean {
  if (!isPair(expr)) return false;
  const rest = cdr(expr);
  if (isPair(rest) && elements(rest).length === 1 && isList(rest)) {
    if (car(expr) === S.pair && vars.includes(car(rest))) return true;
    if (car(expr) === S.not && baseCaseTest(car(rest), vars)) return true;
  }
  return vars.some((v) => isSym(v) && lowerPassTest(expr, v, (c) => !vars.includes(c)));
}

/**
 * termination.ss:1369 cond-fall-through-test: the test of a cond's last clause when it is not
 * else, so a false test falls out of the cond without recursing; null otherwise (HC-8).
 */
export function condFallThroughTest(expr: Datum): Datum | null {
  const clauses = cdr(expr);
  if (!isList(clauses) || clauses.length === 0) return null;
  const c = clauses[clauses.length - 1]!;
  return isPair(c) && car(c) !== S.else ? car(c) : null;
}

/**
 * termination.ss:1474 has-base-case-by?: some if, cond, when or unless in bodyExprs has a branch
 * that cannot recurse, by calls. when and unless count only when their test mentions one of vars,
 * since otherwise the implicit void branch may be unreachable.
 */
export function hasBaseCaseBy(bodyExprs: readonly Datum[], vars: readonly Datum[], calls: (e: Datum) => boolean): boolean {
  let found = false;
  function walk(expr: Datum): void {
    if (found || !isPair(expr) || car(expr) === S.quote) return;
    const head = car(expr);
    if (head === S.if) {
      if (!isPair(cdr(expr)) || !isPair(cddr(expr))) return;
      const test = cadr(expr);
      const consequent = caddr(expr);
      const alternative = isPair(cdddr(expr)) ? car(cdddr(expr)) : null;
      if (baseCaseTest(test, vars) && !calls(consequent)) found = true;
      if (negatedBaseCaseTest(test, vars) && !calls(test) && !(alternative !== null && calls(alternative))) found = true;
      walk(consequent);
      if (alternative !== null) walk(alternative);
    } else if (head === S.cond) {
      for (const clause of properPrefix(cdr(expr))) {
        if (!isPair(clause) || !isPair(cdr(clause))) continue;
        const test = car(clause);
        const body = cdr(clause);
        if ((baseCaseTest(test, vars) || test === S.else) && !calls(body)) found = true;
        properPrefix(body).forEach(walk);
      }
      const test = condFallThroughTest(expr);
      if (test !== null && !calls(test) && negatedBaseCaseTest(test, vars)) found = true;
    } else if (head === S.when || head === S.unless) {
      if (!isPair(cdr(expr))) return;
      const test = cadr(expr);
      const body = cddr(expr);
      if (calls(body) && !calls(test) && exprReferencesAny(test, vars)) found = true;
      properPrefix(body).forEach(walk);
    } else {
      if (isPair(head)) walk(head);
      for (const sub of properPrefix(cdr(expr))) if (isPair(sub)) walk(sub);
    }
  }
  properPrefix(bodyExprs as Datum[]).forEach(walk);
  return found;
}

/** termination.ss:1463 has-base-case?: hasBaseCaseBy, recursing through calls to loopName. */
export function hasBaseCase(bodyExprs: readonly Datum[], loopName: Datum, vars: readonly Datum[]): boolean {
  return hasBaseCaseBy(bodyExprs, vars, (e) => containsCall(e, loopName));
}

// The named let's loop variables: each binding's name, skipping malformed bindings.
function loopVars(bindings: Datum): Sym[] {
  return elements(bindings).flatMap((b) => (isPair(b) && isSym(car(b)) ? [car(b) as Sym] : []));
}

/**
 * termination.ss:1573 analyze-named-let-forms: the violations of every recursive named let in
 * exprs, in walk order. The Scheme's type-env and param-types arguments scope record types for
 * HC-18 and are absent here, so the define cases reduce to walking their bodies.
 */
export function analyzeNamedLetForms(exprs: readonly Datum[]): TerminationViolation[] {
  const violations: TerminationViolation[] = [];
  const add = (kind: TerminationKind, loopName: Sym, expr: Datum, reason: string): void => {
    violations.push({ kind, function: loopName, expr, reason });
  };

  function checkNamedLet(expr: Datum): void {
    const loopName = cadr(expr) as Sym;
    const vars = loopVars(caddr(expr));
    const body = properPrefix(cdddr(expr));
    if (!containsCall(body, loopName)) return;
    // Judged as Phase 5 judges a one-member SCC whose formals are the loop variables, so a numeric
    // step counts only under a test that guards its call, and an ascent bound must be stable (HC-7).
    const progress =
      vars.length === 0
        ? "no-descent"
        : sccSizeChange(
            [loopName],
            () => vars,
            () => body,
            exprs,
          );
    const name = `named-let "${loopName.name}"`;
    if (progress === "limit") {
      add("size-change-limit", loopName, expr, `${name} exceeds the size-change analysis limit`);
    } else if (progress === "no-descent" || (progress === "unguarded" && hasBaseCase(body, loopName, vars))) {
      add("no-decreasing-arg", loopName, expr, `${name} has no decreasing argument in recursive call(s)${equalityStopHint(body)}`);
    } else if (!hasBaseCase(body, loopName, vars)) {
      add("no-base-case", loopName, expr, `${name} has no reachable base case`);
    }
  }

  function walk(expr: Datum): void {
    if (!isPair(expr) || car(expr) === S.quote) return;
    const head = car(expr);
    const rest = cdr(expr);
    if (head === S.define && isPair(rest) && isPair(car(rest)) && isSym(car(car(rest)))) {
      properPrefix(cddr(expr)).forEach(walk);
    } else if (
      head === S.define &&
      isPair(rest) &&
      isSym(car(rest)) &&
      isPair(cddr(expr)) &&
      isPair(caddr(expr)) &&
      car(caddr(expr)) === S.lambda &&
      isPair(cdr(caddr(expr)))
    ) {
      properPrefix(cddr(caddr(expr))).forEach(walk);
    } else {
      if (head === S.let && isPair(rest) && isSym(car(rest)) && isPair(cddr(expr)) && isPair(cdddr(expr))) {
        checkNamedLet(expr);
      }
      if (isPair(head)) walk(head);
      for (const sub of properPrefix(rest)) if (isPair(sub)) walk(sub);
    }
  }

  exprs.forEach(walk);
  return violations;
}
