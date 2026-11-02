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

// Under JavaScript doubles a step must be a positive integer literal: 1e-30 stalls below one ulp.
const isPositiveNumber = (d: Datum | undefined): boolean =>
  typeof d === "number" && d > 0 && (doubles === null || Number.isSafeInteger(d));

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

// ---------------------------------------------------------------
// JavaScript doubles (HC-21)
// ---------------------------------------------------------------
//
// A numeric measure proves termination only on values that are safe integers. A double at 2^53 has
// i + 1 === i, and NaN and the infinities never reach a bound. checkTypeScript() turns this mode on
// with withDoubles(); Scheme's exact integers do not need it, so the port matches Chez with it off.
// See plans/hc-21-js-doubles-termination.md in the brain vault.

const SAFE_INTEGER_P = sym("js.Number.isSafeInteger");
const SMALL_LITERAL = 2 ** 32;
const LENGTH_OPS: ReadonlySet<Datum> = new Set(["length", "string-length", "vector-length"].map(sym));
const DO_FORM = sym("do");
const SET = sym("set!");
const GUARD = sym("guard");

// Where a name is bound. A name may have several sites: the lowering of a while loop binds its do
// variable under the name of the variable it writes back to.
type Site =
  | { readonly kind: "init"; readonly init: Datum; readonly anchor: Datum }
  | { readonly kind: "do"; readonly doExpr: Datum }
  | { readonly kind: "opaque" };

interface Doubles {
  readonly exprs: readonly Datum[];
  readonly sites: Map<Datum, Site[]>;
  // Each name a set! assigns, with the values it assigns.
  readonly assigned: Map<Datum, Datum[]>;
  // provenSafe's verdict on a name, kept only when it rests on no assumption about another name.
  readonly memo: Map<Datum, boolean>;
  // The same for an unguarded name, which also proves every binding site.
  readonly unguardedMemo: Map<Datum, boolean>;
  readonly guardsAtAnchor: Map<Datum, Guard[]>;
}

// The names whose seen or assumed status a provenSafe call relied on, so its verdict is not cached.
let leaned = new Set<Datum>();

let doubles: Doubles | null = null;

/** Whether the double mode of withDoubles is on. */
export function doublesMode(): boolean {
  return doubles !== null;
}

const VALUE_BINDERS = new Set(["let", "let*", "letrec", "letrec*"].map(sym));

/** Runs body with numeric measures judged as JavaScript doubles over the program exprs. */
export function withDoubles<T>(exprs: readonly Datum[], body: () => T): T {
  const sites = new Map<Datum, Site[]>();
  const assigned = new Map<Datum, Datum[]>();
  const site = (name: Datum, s: Site): void => {
    sites.set(name, [...(sites.get(name) ?? []), s]);
  };
  const opaque = (names: readonly Datum[]): void => names.forEach((n) => site(n, { kind: "opaque" }));
  const walk = (e: Datum): void => {
    if (!isCodeList(e)) return;
    const head = e[0]!;
    if (head === S.define && e.length >= 2) {
      if (isSym(e[1]!)) site(e[1]!, e.length === 3 ? { kind: "init", init: e[2]!, anchor: e } : { kind: "opaque" });
      else opaque(formalNames(e[1]!));
    } else if (head === S.lambda && e.length >= 2) {
      opaque(formalNames(e[1]!));
    } else if (head === S.caseLambda) {
      for (const c of e.slice(1)) if (isPair(c)) opaque(formalNames(car(c)));
    } else if (head === S.let && e.length >= 3 && isSym(e[1]!)) {
      // A named let rebinds its variables on every pass.
      opaque([e[1]!, ...bindingNames(e[2]!)]);
    } else if (isSym(head) && VALUE_BINDERS.has(head) && e.length >= 2 && isList(e[1]!)) {
      for (const b of e[1] as Datum[]) {
        if (isList(b) && b.length === 2 && isSym(b[0]!)) site(b[0]!, { kind: "init", init: b[1]!, anchor: b });
        else if (isPair(b)) opaque(formalNames(car(b)));
      }
    } else if (head === DO_FORM && e.length >= 2 && isList(e[1]!)) {
      for (const b of e[1] as Datum[]) if (isPair(b)) site(car(b), isSym(car(b)) ? { kind: "do", doExpr: e } : { kind: "opaque" });
    } else if (isSym(head) && LIST_BINDERS.has(head) && e.length >= 2) {
      opaque(bindingNames(e[1]!));
    } else if (head === GUARD && e.length >= 2 && isPair(e[1]!)) {
      opaque(formalNames(car(e[1]!)));
    }
    if (head === SET && e.length === 3) assigned.set(e[1]!, [...(assigned.get(e[1]!) ?? []), e[2]!]);
    e.forEach(walk);
  };
  exprs.forEach(walk);
  const saved = doubles;
  doubles = { exprs, sites, assigned, memo: new Map(), unguardedMemo: new Map(), guardsAtAnchor: new Map() };
  try {
    return body();
  } finally {
    doubles = saved;
  }
}

// An integer literal of at most 2^32 or a length, or a sum or difference of such terms. A program
// holds far fewer than 2^21 of them, so the result stays a safe integer.
function smallSafe(t: Datum): boolean {
  if (typeof t === "number") return Number.isInteger(t) && Math.abs(t) <= SMALL_LITERAL;
  if (!isCodeOrQuotedList(t)) return false;
  if (LENGTH_OPS.has(t[0]!)) return t.length === 2;
  return (t[0] === S.plus || t[0] === S.minus) && t.length === 3 && smallSafe(t[1]!) && smallSafe(t[2]!);
}

// A guard that holds Number.isSafeInteger(x): the call known true or its negation known false.
function safeGuarded(x: Datum, guards: readonly Guard[]): boolean {
  const isCheck = (t: Datum): boolean => isCodeOrQuotedList(t) && t.length === 2 && t[0] === SAFE_INTEGER_P && t[1] === x;
  return guards.some(([t, known]) =>
    known ? isCheck(t) : isCodeOrQuotedList(t) && t[0] === S.not && t.length === 2 && isCheck(t[1]!));
}

/**
 * termination term is proven a safe integer where guards hold: a safe integer literal, a smallSafe
 * term, a name under a Number.isSafeInteger guard, a name bound once to a proven term and never
 * assigned, or the variable of a do-loop that counts by an integer step between proven ends.
 * Outside withDoubles every term counts as proven.
 */
export function provenSafe(
  term: Datum,
  guards: readonly Guard[],
  seen: readonly Datum[] = [],
  assumed: readonly Datum[] = [],
): boolean {
  if (doubles === null) return true;
  if (typeof term === "number") return Number.isSafeInteger(term);
  if (smallSafe(term)) return true;
  if (!isSym(term)) return false;
  if (assumed.includes(term) || seen.includes(term)) {
    leaned.add(term);
    return assumed.includes(term);
  }
  // An assigned name is proven by induction over the run: its value at the guard or its binding
  // is, and each set! writes back a value a do-loop computed from a proven one.
  const next = [...seen, term];
  const writesSafe = (): boolean =>
    (doubles!.assigned.get(term) ?? []).every((v) => doExitSafe(v, next, [...assumed, term]));
  if (safeGuarded(term, guards)) return cached(doubles.memo, term, writesSafe);
  // The sites carry their own anchor guards, so the unguarded verdict ignores guards and is cached.
  return cached(doubles.unguardedMemo, term, () => sitesSafe(term, next, assumed, writesSafe));
}

// Every binding site of an unguarded term is proven, and so is every value set! writes to it.
function sitesSafe(
  term: Datum,
  next: readonly Datum[],
  assumed: readonly Datum[],
  writesSafe: () => boolean,
): boolean {
  const sites = doubles!.sites.get(term) ?? [];
  if (sites.length === 0) return false;
  // Whichever site a use denotes, its value is proven.
  const siteSafe = (st: Site): boolean => {
    if (st.kind === "init") return provenSafe(st.init, anchorGuards(st.anchor), next, assumed);
    // A do variable's start is read before its loop runs, so it may assume the name's earlier values.
    if (st.kind === "do") return doVarSafe(st.doExpr, term, next, [...assumed, term]);
    return false;
  };
  return sites.every(siteSafe) && cached(doubles!.memo, term, writesSafe);
}

// body's verdict on name, from memo when an earlier verdict rested on no other name's status.
function cached(memo: Map<Datum, boolean>, name: Datum, body: () => boolean): boolean {
  if (memo.has(name)) return memo.get(name)!;
  const outer = leaned;
  leaned = new Set();
  const verdict = body();
  const mine = leaned;
  leaned = outer;
  mine.delete(name);
  if (mine.size === 0) memo.set(name, verdict);
  else mine.forEach((n) => outer.add(n));
  return verdict;
}

// guardsAt over the whole program, once per anchor.
function anchorGuards(anchor: Datum): Guard[] {
  const cache = doubles!.guardsAtAnchor;
  if (!cache.has(anchor)) cache.set(anchor, guardsAt(doubles!.exprs, anchor) ?? []);
  return cache.get(anchor)!;
}

/**
 * The guards that hold inside a do-form's exit test and steps: those around it, less any that
 * mention a name the do-form rebinds.
 */
export function doInnerGuards(doExpr: Datum, outer: readonly Guard[]): Guard[] {
  const vars = isCodeOrQuotedList(doExpr) && isList(doExpr[1]!) ? bindingNames(doExpr[1]!) : [];
  return outer.filter(([t]) => !exprReferencesAny(t, vars));
}

/** The guards around a do-form, before its own variables are bound. */
export function doOuterGuards(doExpr: Datum): Guard[] {
  return doubles === null ? [] : anchorGuards(doExpr);
}

// A do-form whose value is a loop variable that leaves the loop a safe integer: it counts by a step
// of at most 2^32 from a proven start toward a smallSafe bound, so it stops within one step of it.
// This is the write-back the lowering of a while loop makes.
function doExitSafe(v: Datum, seen: readonly Datum[], assumed: readonly Datum[]): boolean {
  if (!isCodeOrQuotedList(v) || v[0] !== DO_FORM || !isList(v[1]!) || !isList(v[2]!)) return false;
  const exit = v[2] as Datum[];
  const y = exit.length === 2 ? exit[1]! : null;
  if (y === null || !isSym(y)) return false;
  const binding = (v[1] as Datum[]).find((b) => isList(b) && b[0] === y) as Datum[] | undefined;
  const step = binding?.[2];
  const k = step !== undefined && isCodeOrQuotedList(step) ? step[step[1] === y ? 2 : 1] : undefined;
  const smallStep = typeof k === "number" && k <= SMALL_LITERAL;
  return smallStep && doVarSafe(v, y, seen, assumed, smallSafe);
}

// A do variable x is a safe integer inside its loop when its start and its bound are, its step
// moves it by a positive integer toward the bound, and nothing in the loop assigns it.
function doVarSafe(
  doExpr: Datum,
  x: Datum,
  seen: readonly Datum[],
  assumed: readonly Datum[],
  boundRule: (b: Datum) => boolean = () => true,
): boolean {
  if (!isCodeOrQuotedList(doExpr) || !isList(doExpr[1]!) || !isList(doExpr[2]!)) return false;
  const binding = (doExpr[1] as Datum[]).find((b) => isList(b) && b[0] === x);
  if (!isList(binding!) || binding.length !== 3) return false;
  const [, init, step] = binding as [Datum, Datum, Datum];
  if (assignsName(doExpr.slice(2), x)) return false;
  const outer = anchorGuards(doExpr);
  const inner = doInnerGuards(doExpr, outer);
  const tests = doContinueTests((doExpr[2] as Datum[])[0]!);
  const ok = (b: Datum): boolean => provenSafe(b, outer, seen, assumed);
  const bound = (b: Datum): boolean => provenSafe(b, inner, seen, assumed) && boundRule(b);
  const down = numericStep(step) && decreasingExpr(step, x) && tests.some((t) => lowerStopTest(t, x, bound));
  const up = increasingExpr(step, x) && tests.some((t) => isCodeOrQuotedList(t) && upperBoundBaseCaseTest(t, [x]) &&
    bound(upperBoundTestPair(t, [x])[1]));
  return (down || up) && ok(init);
}

// Whether some set! in es assigns name.
function assignsName(es: readonly Datum[], name: Datum): boolean {
  return es.some((e) => isCodeList(e) && ((e[0] === SET && e[1] === name) || assignsName(e, name)));
}

// The disjuncts of a do-loop's exit test, any one of which ends the loop.
function doContinueTests(test: Datum): Datum[] {
  return isCodeOrQuotedList(test) && test[0] === sym("or") ? test.slice(1).flatMap(doContinueTests) : [test];
}

/** The names in term that provenSafe does not prove, for a hint that names the guard to add. */
export function unprovenNames(term: Datum, guards: readonly Guard[]): Sym[] {
  if (isSym(term)) return provenSafe(term, guards) ? [] : [term];
  if (!isCodeOrQuotedList(term) || term[0] === S.quote) return [];
  return term.slice(1).flatMap((t) => unprovenNames(t, guards));
}

/** The formals a numeric step moves anywhere in body, for safeIntegerHint. */
export function numericallyStepped(body: readonly Datum[], formals: readonly Datum[]): Sym[] {
  const found: Sym[] = [];
  const walk = (e: Datum): void => {
    if (!isCodeList(e)) return;
    if (numericStep(e)) for (const x of formals) if (isSym(x) && monotonicExpr(e, x)) found.push(x);
    e.forEach(walk);
  };
  body.forEach(walk);
  return found;
}

/** The note for a numeric measure rejected for want of a safe-integer proof. */
export function safeIntegerHint(names: readonly Sym[]): string {
  const unique = [...new Set(names.filter((s) => doubles?.sites.has(s)))];
  if (doubles === null || unique.length === 0) return "";
  const written = unique.map((s) => s.name.replace(/~\d+$/, ""));
  const n = written[0]!;
  return `; ${written.join(", ")} is not proven a safe integer, and NaN, Infinity or a value ` +
    `above 2^53 never reaches the bound: add if (!Number.isSafeInteger(${n})) return; before counting on it`;
}
