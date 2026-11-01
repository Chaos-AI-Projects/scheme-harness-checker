// Binder and guard helpers, ported from src/harness-checker/termination.ss (HC-16): the names a form
// binds, the branch tests that hold where an expression is evaluated, and which of those tests bound
// a numeric descent or ascent. The expression predicates they rest on (decreasing-expr? and friends,
// the upper-bound base-case tests) come from Phases 3 and 5 of the same file.
//
// Guards are [test, known] pairs, the Scheme's (test . #t) and (test . #f). A bound pair is the
// Scheme's (var . bound). Forms are found by identity, as the Scheme finds them by eq?.

import { car, cadr, caddr, cdr, cddr, cdddr, isList, isPair, isSym, sym, write, type Datum, type Sym } from "../sexp.ts";
import { properPrefix } from "./callgraph.ts";

/** A branch test and whether it is known true (true) or false (false) where it holds. */
export type Guard = readonly [test: Datum, known: boolean];

/** The Scheme's (var . bound). */
export type BoundPair = readonly [variable: Datum, bound: Datum];

/** Judges whether a guard's bound is stable between calls. */
export type BoundOk = (bound: Datum) => boolean;

const S = {
  quote: sym("quote"),
  quasiquote: sym("quasiquote"),
  begin: sym("begin"),
  define: sym("define"),
  lambda: sym("lambda"),
  caseLambda: sym("case-lambda"),
  let: sym("let"),
  if: sym("if"),
  cond: sym("cond"),
  when: sym("when"),
  unless: sym("unless"),
  else: sym("else"),
  not: sym("not"),
  lt: sym("<"),
  le: sym("<="),
  gt: sym(">"),
  ge: sym(">="),
  eq: sym("="),
  minus: sym("-"),
  sub1: sym("sub1"),
  fxMinus: sym("fx-"),
  plus: sym("+"),
  add1: sym("add1"),
  fxPlus: sym("fx+"),
  cdr: sym("cdr"),
  cddr: sym("cddr"),
  listTail: sym("list-tail"),
  positive: sym("positive?"),
  zero: sym("zero?"),
  cfaElement: sym("%cfa-element"),
  cfaSpread: sym("%cfa-spread"),
};

const LIST_BINDERS = new Set(["let*", "letrec", "letrec*", "let-values", "let*-values", "do"].map(sym));

/** Numeric step operators. termination.ss:1765 numeric-step-names. */
export const NUMERIC_STEP_NAMES: ReadonlySet<Sym> = new Set(["-", "sub1", "fx-", "+", "add1", "fx+"].map(sym));

/** termination.ss:1767 numeric-step?. */
export function numericStep(expr: Datum): boolean {
  return isPair(expr) && isSym(car(expr)) && NUMERIC_STEP_NAMES.has(car(expr) as Sym);
}

// The i-th element of a form's proper prefix, or undefined.
function nth(expr: Datum, i: number): Datum | undefined {
  return properPrefix(expr)[i];
}

const isPositiveNumber = (d: Datum | undefined): boolean => typeof d === "number" && d > 0;

// A proper list of exactly n elements headed by head.
const isForm = (expr: Datum, head: Sym, n: number): expr is Datum[] =>
  Array.isArray(expr) && expr.length === n && expr[0] === head;

/** termination.ss:466 cfa-element-form?: an element of a list handed on by the cfa rewrite. */
export function cfaElementForm(expr: Datum): boolean {
  return isPair(expr) && (car(expr) === S.cfaElement || car(expr) === S.cfaSpread);
}

/**
 * termination.ss:1096 decreasing-expr?: (- x k), (sub1 x), (fx- x k), (cdr x), (cddr x),
 * (list-tail x k) and an element of x or of its descent. The Scheme's third argument, var-type,
 * enables the record-accessor branch; that needs the types port and belongs to HC-18, so it is left
 * out here. The reader has no exact/inexact distinction, so list-tail's k is only checked integral.
 */
export function decreasingExpr(expr: Datum, v: Datum): boolean {
  if (!isPair(expr)) return false;
  const head = car(expr);
  if ((head === S.minus || head === S.fxMinus) && isForm(expr, head, 3)) {
    return expr[1] === v && isPositiveNumber(expr[2]);
  }
  if (head === S.sub1 || head === S.cdr || head === S.cddr) return nth(expr, 1) === v;
  if (head === S.listTail && isForm(expr, head, 3)) {
    return expr[1] === v && Number.isInteger(expr[2]) && (expr[2] as number) > 0;
  }
  if (cfaElementForm(expr) && isPair(cdr(expr))) {
    const coll = cadr(expr);
    return coll === v || decreasingExpr(coll, v);
  }
  return false;
}

/** termination.ss:1199 increasing-expr?: (+ x k), (+ k x), (add1 x), (fx+ x k). */
export function increasingExpr(expr: Datum, v: Datum): boolean {
  if (!isPair(expr)) return false;
  const head = car(expr);
  if (head === S.plus && isForm(expr, head, 3)) {
    return (expr[1] === v && isPositiveNumber(expr[2])) || (isPositiveNumber(expr[1]) && expr[2] === v);
  }
  if (head === S.add1) return nth(expr, 1) === v;
  if (head === S.fxPlus && isForm(expr, head, 3)) return expr[1] === v && isPositiveNumber(expr[2]);
  return false;
}

/** termination.ss:1166 monotonic-expr?: decreasing or increasing. var-type is HC-18's, as above. */
export function monotonicExpr(expr: Datum, v: Datum): boolean {
  return decreasingExpr(expr, v) || increasingExpr(expr, v);
}

/** termination.ss:947 expr-references-any?: skips quoted forms, at any cdr position too. */
export function exprReferencesAny(expr: Datum, symbols: readonly Datum[]): boolean {
  if (symbols.length === 0) return false;
  if (isSym(expr)) return symbols.includes(expr);
  if (!isPair(expr)) return false;
  if (car(expr) === S.quote) return false;
  return exprReferencesAny(car(expr), symbols) || exprReferencesAny(cdr(expr), symbols);
}

/** termination.ss:1228 contains-call?: loop-name in operator position, at any cdr position too. */
export function containsCall(expr: Datum, loopName: Datum): boolean {
  if (!isPair(expr)) return false;
  const head = car(expr);
  if (head === S.quote) return false;
  if (head === loopName) return true;
  return containsCall(head, loopName) || containsCall(cdr(expr), loopName);
}

/**
 * termination.ss:1382 upper-bound-base-case-test?: (>= v N), (> v N), or (= v N) / (= N v) with N
 * not literal 0, where v is one of vars and N is not.
 */
export function upperBoundBaseCaseTest(expr: Datum, vars: readonly Datum[]): boolean {
  if (!isPair(expr)) return false;
  const head = car(expr);
  const a = nth(expr, 1);
  const b = nth(expr, 2);
  if (a === undefined || b === undefined) return false;
  if (head === S.ge || head === S.gt) return vars.includes(a) && !vars.includes(b);
  if (head === S.eq) {
    return (vars.includes(a) && !vars.includes(b) && b !== 0) || (!vars.includes(a) && a !== 0 && vars.includes(b));
  }
  return false;
}

/** termination.ss:1409 upper-bound-test-pair: the (var . bound) an upper-bound test constrains. */
export function upperBoundTestPair(test: Datum, vars: readonly Datum[]): BoundPair {
  if (car(test) === S.eq && !vars.includes(cadr(test))) return [caddr(test), cadr(test)];
  return [cadr(test), caddr(test)];
}

/**
 * termination.ss:1419 upper-bound-base-cases: the (var . bound) pairs of the body's upper-bound
 * base cases, newest first. when is not one; cond clauses are not searched further.
 */
export function upperBoundBaseCases(bodyExprs: readonly Datum[], loopName: Datum, vars: readonly Datum[]): BoundPair[] {
  const found: BoundPair[] = [];
  const note = (test: Datum): void => {
    found.unshift(upperBoundTestPair(test, vars));
  };
  function walk(expr: Datum): void {
    if (!isPair(expr) || car(expr) === S.quote) return;
    const head = car(expr);
    if (head === S.if) {
      if (isPair(cdr(expr)) && isPair(cddr(expr))) {
        const test = cadr(expr);
        const consequent = caddr(expr);
        if (upperBoundBaseCaseTest(test, vars) && !containsCall(consequent, loopName)) note(test);
        walk(consequent);
        if (isPair(cdddr(expr))) walk(car(cdddr(expr)));
      }
    } else if (head === S.cond) {
      for (const clause of properPrefix(cdr(expr))) {
        if (isPair(clause) && isPair(cdr(clause))) {
          const test = car(clause);
          if (upperBoundBaseCaseTest(test, vars) && !containsCall(cdr(clause), loopName)) note(test);
        }
      }
    } else if (head === S.unless) {
      if (isPair(cdr(expr)) && upperBoundBaseCaseTest(cadr(expr), vars)) note(cadr(expr));
    } else {
      if (isPair(head)) walk(head);
      for (const sub of properPrefix(cdr(expr))) if (isPair(sub)) walk(sub);
    }
  }
  bodyExprs.forEach(walk);
  return found;
}

// ---------------------------------------------------------------
// Binder helpers (Phase 6)
// ---------------------------------------------------------------

/** termination.ss:2170 formal-names: every symbol in a formals tree, dotted tails included. */
export function formalNames(f: Datum): Sym[] {
  if (isSym(f)) return [f];
  if (isPair(f)) return [...formalNames(car(f)), ...formalNames(cdr(f))];
  return [];
}

/** termination.ss:2175 binding-names. */
export function bindingNames(bs: Datum): Sym[] {
  if (!isList(bs)) return [];
  return bs.flatMap((b) => (isPair(b) ? formalNames(car(b)) : []));
}

/** termination.ss:2180 flatten-begins. */
export function flattenBegins(es: readonly Datum[]): Datum[] {
  return es.flatMap((e) => (Array.isArray(e) && e.length > 0 && e[0] === S.begin ? flattenBegins(e.slice(1)) : [e]));
}

/** termination.ss:2187 define-names: the names the defines in es bind, begins flattened. */
export function defineNames(es: readonly Datum[]): Sym[] {
  return flattenBegins(es).flatMap((e) =>
    isPair(e) && car(e) === S.define && isPair(cdr(e)) ? formalNames(cadr(e)) : [],
  );
}

/** termination.ss:2195 form-binds: names a form binds anywhere inside itself. expr is a pair. */
export function formBinds(expr: Datum): Sym[] {
  const rest = cdr(expr);
  const tail: Datum[] = isList(rest) ? rest : [];
  const head = car(expr);
  let own: Sym[] = [];
  if (head === S.lambda || head === S.define) {
    own = tail.length > 0 ? formalNames(tail[0]!) : [];
  } else if (head === S.caseLambda) {
    own = tail.flatMap((c) => (isPair(c) ? formalNames(car(c)) : []));
  } else if (head === S.let) {
    if (tail.length > 1 && isSym(tail[0]!)) own = [tail[0] as Sym, ...bindingNames(tail[1]!)];
    else if (tail.length > 0) own = bindingNames(tail[0]!);
  } else if (isSym(head) && LIST_BINDERS.has(head)) {
    own = tail.length > 0 ? bindingNames(tail[0]!) : [];
  }
  return [...own, ...defineNames(tail)];
}

// A proper, non-empty list that is not quoted data: the forms the walkers below descend into.
const isCodeList = (e: Datum): e is Datum[] => Array.isArray(e) && e.length > 0 && e[0] !== S.quote;

// The Scheme escapes these walks with call/cc; a thrown Found carries the value out.
class Found<T> {
  readonly value: T;
  constructor(value: T) {
    this.value = value;
  }
}

function escape<T>(body: () => void): T | null {
  try {
    body();
  } catch (e) {
    if (e instanceof Found) return e.value as T;
    throw e;
  }
  return null;
}

/**
 * termination.ss:2217 names-shadowed-at: names some form in bodyExprs binds around target, found
 * by identity, plus the body's own defines. null when target is not in bodyExprs.
 */
export function namesShadowedAt(bodyExprs: readonly Datum[], target: Datum): Sym[] | null {
  function walk(expr: Datum, shadowed: Sym[]): void {
    if (expr === target) throw new Found(shadowed);
    if (!isCodeList(expr)) return;
    const inner = isSym(expr[0]!) ? [...formBinds(expr), ...shadowed] : shadowed;
    for (const sub of expr) if (isPair(sub)) walk(sub, inner);
  }
  const top = defineNames(bodyExprs);
  return escape<Sym[]>(() => bodyExprs.forEach((e) => walk(e, top)));
}

// Every name the forms in es bind, consed onto acc in walk order.
function collectBinders(es: readonly Datum[], acc: Sym[]): Sym[] {
  return es.reduce<Sym[]>(
    (a, e) => (isCodeList(e) ? collectBinders(e, isSym(e[0]!) ? [...formBinds(e), ...a] : a) : a),
    acc,
  );
}

/**
 * termination.ss:2235 names-bound-around: names bound around a definition's body. When the body
 * cannot be found in exprs, every name the program binds anywhere.
 */
export function namesBoundAround(exprs: readonly Datum[], body: readonly Datum[]): Sym[] {
  const target = body.find(isPair);
  const found = target === undefined ? null : namesShadowedAt(exprs, target);
  return found ?? collectBinders(exprs, defineNames(exprs));
}

/** termination.ss:2415 body-binders: every name some form in bodyExprs binds, its defines included. */
export function bodyBinders(bodyExprs: readonly Datum[]): Sym[] {
  return collectBinders(bodyExprs, defineNames(bodyExprs));
}

// ---------------------------------------------------------------
// Guards
// ---------------------------------------------------------------

/**
 * termination.ss:2254 guards-at: the branch tests that hold where target, found by identity, is
 * evaluated, innermost first. Only if, cond, when and unless contribute, and a test is dropped
 * under any binder that rebinds a name it mentions. null when target is not in bodyExprs.
 */
export function guardsAt(bodyExprs: readonly Datum[], target: Datum): Guard[] | null {
  const dropRebound = (guards: Guard[], names: Sym[]): Guard[] =>
    guards.filter(([t]) => !exprReferencesAny(t, names));
  function walk(expr: Datum, outer: Guard[]): void {
    if (expr === target) throw new Found(outer);
    if (!isCodeList(expr)) return;
    const head = expr[0]!;
    const binds = isSym(head) ? formBinds(expr) : [];
    const guards = binds.length === 0 ? outer : dropRebound(outer, binds);
    const kw = isSym(head) && !binds.includes(head) ? head : null;
    if (kw === S.if && expr.length >= 3 && expr.length <= 4) {
      const test = expr[1]!;
      walk(test, guards);
      walk(expr[2]!, [[test, true], ...guards]);
      if (expr.length === 4) walk(expr[3]!, [[test, false], ...guards]);
    } else if ((kw === S.when || kw === S.unless) && expr.length >= 2) {
      const test = expr[1]!;
      walk(test, guards);
      for (const e of expr.slice(2)) walk(e, [[test, kw === S.when], ...guards]);
    } else if (kw === S.cond) {
      let gs = guards;
      for (const c of expr.slice(1)) {
        if (!(Array.isArray(c) && c.length > 0)) continue;
        const test = c[0]!;
        if (test === S.else) {
          for (const e of c.slice(1)) walk(e, gs);
        } else {
          walk(test, gs);
          for (const e of c.slice(1)) walk(e, [[test, true], ...gs]);
          gs = [[test, false], ...gs];
        }
      }
    } else {
      for (const sub of expr) if (isPair(sub)) walk(sub, guards);
    }
  }
  return escape<Guard[]>(() => bodyExprs.forEach((e) => walk(e, [])));
}

/**
 * termination.ss:2306 lower-stop-test?: a test whose truth stops numeric descent on x at a bound c:
 * (< x c), (<= x c), their mirrors, and (not t) for a lower-pass t. boundOk judges c.
 */
export function lowerStopTest(t: Datum, x: Datum, boundOk: BoundOk): boolean {
  if (!isCodeOrQuotedList(t)) return false;
  const head = t[0];
  if (head === S.lt || head === S.le) {
    return t.length === 3 && t[1] === x && !exprReferencesAny(t[2]!, [x]) && boundOk(t[2]!);
  }
  if (head === S.gt || head === S.ge) {
    return t.length === 3 && t[2] === x && !exprReferencesAny(t[1]!, [x]) && boundOk(t[1]!);
  }
  if (head === S.not) return t.length === 2 && lowerPassTest(t[1]!, x, boundOk);
  return false;
}

/**
 * termination.ss:2323 lower-pass-test?: a test whose truth keeps x above a bound: (> x c),
 * (>= x c), (positive? x), their mirrors, and (not t) for a lower-stop t.
 */
export function lowerPassTest(t: Datum, x: Datum, boundOk: BoundOk): boolean {
  if (!isCodeOrQuotedList(t)) return false;
  const head = t[0];
  if (head === S.positive) return t.length === 2 && t[1] === x;
  if (head === S.gt || head === S.ge) {
    return t.length === 3 && t[1] === x && !exprReferencesAny(t[2]!, [x]) && boundOk(t[2]!);
  }
  if (head === S.lt || head === S.le) {
    return t.length === 3 && t[2] === x && !exprReferencesAny(t[1]!, [x]) && boundOk(t[1]!);
  }
  if (head === S.not) return t.length === 2 && lowerStopTest(t[1]!, x, boundOk);
  return false;
}

// Scheme's (and (pair? t) (list? t)).
function isCodeOrQuotedList(t: Datum): t is Datum[] {
  return Array.isArray(t) && t.length > 0;
}

/**
 * termination.ss:2339 equality-stop-hint: the note for a rejected countdown whose stop is (= x c)
 * or (zero? x), naming the lower stop (<= x c). "" when expr has no such test on an x it also
 * steps down.
 */
export function equalityStopHint(expr: Datum): string {
  const isData = (e: Datum[]): boolean => e[0] === S.quote || e[0] === S.quasiquote;
  const descends = (x: Datum): boolean => {
    const walk = (e: Datum): boolean =>
      isCodeOrQuotedList(e) && !isData(e) && ((numericStep(e) && decreasingExpr(e, x)) || e.some(walk));
    return walk(expr);
  };
  const hint = (test: Datum, x: Sym, c: Datum): void => {
    if (descends(x)) {
      throw new Found(`; ${write(test)} does not bound ${x.name} from below, use ${write([S.le, x, c])}`);
    }
  };
  function walk(e: Datum): void {
    if (!isCodeOrQuotedList(e) || isData(e)) return;
    if (e[0] === S.zero && e.length === 2 && isSym(e[1]!)) hint(e, e[1], 0);
    else if (e[0] === S.eq && e.length === 3 && isSym(e[1]!) && typeof e[2] === "number") hint(e, e[1], e[2]);
    e.forEach(walk);
  }
  return escape<string>(() => walk(expr)) ?? "";
}

/**
 * termination.ss:2368 descent-guarded?: numeric descent on x is strict at a call only under a
 * guard that stops it there.
 */
export function descentGuarded(x: Datum, guards: readonly Guard[], boundOk: BoundOk): boolean {
  return guards.some(([t, known]) => (known ? lowerPassTest(t, x, boundOk) : lowerStopTest(t, x, boundOk)));
}

/**
 * termination.ss:2380 ascent-guards: each true test that keeps a variable below a bound rewritten
 * as the false upper-bound test it equals, so (< x c) known true becomes (>= x c) known false.
 */
export function ascentGuards(guards: readonly Guard[]): Guard[] {
  return guards.map((g): Guard => {
    const [t, known] = g;
    if (!(known && isCodeOrQuotedList(t))) return g;
    if (t[0] === S.not && t.length === 2) return [t[1]!, false];
    if (t.length !== 3) return g;
    const [head, a, b] = t as [Datum, Datum, Datum];
    if (head === S.lt) return [[S.ge, a, b], false];
    if (head === S.le) return [[S.gt, a, b], false];
    if (head === S.gt) return [[S.ge, b, a], false];
    if (head === S.ge) return [[S.gt, b, a], false];
    return g;
  });
}

/** termination.ss:2395 guard-upper-bound-pairs: the (x . bound) pairs of the false upper-bound tests. */
export function guardUpperBoundPairs(guards: readonly Guard[], formals: readonly Datum[]): BoundPair[] {
  return ascentGuards(guards).reduce<BoundPair[]>(
    (acc, [t, known]) => (!known && upperBoundBaseCaseTest(t, formals) ? [upperBoundTestPair(t, formals), ...acc] : acc),
    [],
  );
}

/**
 * termination.ss:2406 ascent-guarded?: ascent of x is strict at a call only under a false
 * upper-bound test on x whose bound is stable, or the true test it equals.
 */
export function ascentGuarded(x: Datum, guards: readonly Guard[], boundOk: BoundOk): boolean {
  return ascentGuards(guards).some(([t, known]) => {
    if (known || !upperBoundBaseCaseTest(t, [x])) return false;
    const [v, bound] = upperBoundTestPair(t, [x]);
    return v === x && boundOk(bound);
  });
}
