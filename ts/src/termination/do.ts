// Phase 3 of termination.ss (HC-16): the do-loop pass. A do-form must have a reachable exit test,
// a step, an exit test on a loop variable, and some step that moves a tested variable toward the
// exit test (HC-5).

import { car, caddr, cadr, cdr, cddr, elements, isList, isPair, isSym, sym, type Datum, type Sym } from "../sexp.ts";
import { properPrefix } from "./callgraph.ts";
import {
  ascentGuarded,
  decreasingExpr,
  descentGuarded,
  doInnerGuards,
  doOuterGuards,
  equalityStopHint,
  exprReferencesAny,
  increasingExpr,
  numericStep,
  provenSafe,
  safeIntegerHint,
  unprovenNames,
  type Guard,
} from "./guards.ts";
import { makeBoundOk, setTargets } from "./sizechange.ts";
import type { TerminationViolation } from "./violation.ts";

const DO = sym("do");
const QUOTE = sym("quote");
const OR = sym("or");
const LT = sym("<");
const LE = sym("<=");
const GT = sym(">");
const GE = sym(">=");

/**
 * termination.ss:960 do-continue-guards: the guards that hold while a do-loop keeps running. Its
 * exit test is false, and so is each disjunct of an or. A mirrored ascent test (<= c x) or (< c x)
 * also gets its flipped form, which upperBoundBaseCaseTest recognises.
 */
export function doContinueGuards(test: Datum): Guard[] {
  if (isList(test) && test[0] === OR) return test.slice(1).flatMap(doContinueGuards);
  if (isList(test) && test.length === 3 && (test[0] === LT || test[0] === LE)) {
    return [
      [test, false],
      [[test[0] === LT ? GT : GE, test[2]!, test[1]!], false],
    ];
  }
  return [[test, false]];
}

/**
 * termination.ss:976 do-steps-progress?: some loop variable x moves toward the exit test on every
 * step, and no set! in the do-form assigns x. Its step is numeric descent under a lower stop test on
 * x, ascent under an upper-bound test on x, or structural descent with a test that mentions x. A
 * bound must be stable: pure bound ops over literals, unstepped loop variables and names that no
 * set! in the program assigns (assigned).
 */
export function doStepsProgress(doExpr: Datum, assigned: readonly Datum[], outer: readonly Guard[] = []): boolean {
  const bindings = elements(cadr(doExpr)).filter((b) => isPair(b) && isSym(car(b)));
  const vars = bindings.map((b) => car(b));
  const steps = bindings.map((b) => (isPair(cdr(b)) && isPair(cddr(b)) ? caddr(b) : car(b)));
  const inits = bindings.map((b) => (isPair(cdr(b)) ? cadr(b) : false));
  const test = car(caddr(doExpr));
  const guards = doContinueGuards(test);
  const stable = makeBoundOk(vars, [[DO, ...steps]], assigned, []);
  // Under JavaScript doubles a numeric start and bound must also be proven safe integers (HC-21).
  // The bound is read inside the loop, where the do-form's own variables shadow outer guards.
  const inner = doInnerGuards(doExpr, outer);
  const boundOk = (b: Datum): boolean => stable(b) && provenSafe(b, inner);
  const reset = setTargets(doExpr);
  return vars.some((x, i) => {
    const s = steps[i]!;
    if (reset.includes(x)) return false;
    const startOk = provenSafe(inits[i]!, outer);
    return (
      (numericStep(s) && decreasingExpr(s, x) && startOk && descentGuarded(x, guards, boundOk)) ||
      (increasingExpr(s, x) && startOk && ascentGuarded(x, guards, boundOk)) ||
      (!numericStep(s) && decreasingExpr(s, x) && exprReferencesAny(test, [x]))
    );
  });
}

/**
 * termination.ss:1007 analyze-do-forms: an infinite-loop violation for every do-form in exprs, nested
 * ones included, in source order, whose exit test is #f, which has variables but no step, whose
 * exit test mentions no loop variable, or none of whose steps progresses (doStepsProgress).
 */
export function analyzeDoForms(exprs: readonly Datum[]): TerminationViolation[] {
  const violations: TerminationViolation[] = [];
  const assigned = setTargets([...exprs]);
  const add = (expr: Datum, reason: string) => violations.push({ kind: "infinite-loop", function: null, expr, reason });

  const checkDoForm = (doExpr: Datum): void => {
    if (!(isPair(cdr(doExpr)) && isPair(cddr(doExpr)))) return;
    const bindings = cadr(doExpr);
    const termination = caddr(doExpr);
    const vars: Sym[] = isList(bindings) ? bindings.filter((b) => isPair(b) && isSym(car(b))).map((b) => car(b) as Sym) : [];
    const hasAnyStep = properPrefix(bindings).some((b) => isPair(b) && isPair(cdr(b)) && isPair(cddr(b)));
    if (isPair(termination) && car(termination) === false) {
      add(doExpr, "do-form has unreachable exit condition");
    } else if (vars.length > 0 && !hasAnyStep) {
      add(doExpr, "do-form has no step expressions; loop variables never change");
    } else if (isPair(termination) && vars.length > 0 && hasAnyStep && !exprReferencesAny(car(termination), vars)) {
      add(doExpr, "do-form exit test does not reference any loop variable");
    } else if (isPair(termination) && isList(bindings) && !doStepsProgress(doExpr, assigned, doOuterGuards(doExpr))) {
      const hint = equalityStopHint(doExpr) || safeIntegerHint(unsafeEnds(doExpr, doOuterGuards(doExpr)));
      add(doExpr, "do-form has no step that moves a tested variable toward the exit test" + hint);
    }
  };

  const walk = (expr: Datum): void => {
    if (!isPair(expr) || car(expr) === QUOTE) return;
    if (car(expr) === DO) checkDoForm(expr);
    for (const sub of properPrefix(expr)) if (isPair(sub)) walk(sub);
  };

  for (const e of exprs) walk(e);
  return violations;
}

// The names in a do-loop's starts and exit test that are not proven safe integers.
function unsafeEnds(doExpr: Datum, outer: readonly Guard[]): Sym[] {
  const bindings = elements(cadr(doExpr)).filter((b) => isPair(b) && isSym(car(b)));
  const vars = bindings.map((b) => car(b));
  const starts = bindings.map((b) => (isPair(cdr(b)) ? cadr(b) : false));
  return [
    ...starts.flatMap((e) => unprovenNames(e, outer)),
    ...unprovenNames(car(caddr(doExpr)), doInnerGuards(doExpr, outer)).filter((n) => !vars.includes(n)),
  ];
}
