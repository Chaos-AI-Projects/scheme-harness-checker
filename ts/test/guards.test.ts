// Direct unit tests for the binder and guard helpers of termination.ss (HC-16), and the expression
// predicates under them. test-termination.ss reaches these only through the drivers, so the cases
// here are derived from the Scheme definitions.

import { test } from "node:test";
import assert from "node:assert/strict";
import { readAll, readOne, sym, write, type Datum } from "../src/sexp.ts";
import {
  ascentGuarded,
  ascentGuards,
  bindingNames,
  bodyBinders,
  decreasingExpr,
  defineNames,
  descentGuarded,
  equalityStopHint,
  exprReferencesAny,
  flattenBegins,
  formBinds,
  formalNames,
  guardUpperBoundPairs,
  guardsAt,
  increasingExpr,
  lowerPassTest,
  lowerStopTest,
  monotonicExpr,
  namesBoundAround,
  namesShadowedAt,
  upperBoundBaseCaseTest,
  upperBoundBaseCases,
  upperBoundTestPair,
  type Guard,
} from "../src/termination/guards.ts";

const r = readOne;
const x = sym("x");
const syms = (...names: string[]) => names.map(sym);
const anyBound = () => true;
const noBound = () => false;

// Guards as Scheme text: ((test . #t) ...).
const showGuards = (gs: readonly Guard[] | null): string =>
  gs === null ? "#f" : `(${gs.map(([t, k]) => `(${write(t)} . ${k ? "#t" : "#f"})`).join(" ")})`;
const showPairs = (ps: readonly (readonly [Datum, Datum])[]): string =>
  `(${ps.map(([v, b]) => `(${write(v)} . ${write(b)})`).join(" ")})`;
const guards = (text: string): Guard[] =>
  (r(text) as Datum[][]).map((g) => [g[0]!, g[1] === true] as const);

// The first subform of `form` whose car is `head`, depth first.
function find(form: Datum, head: string): Datum {
  const found = (function walk(e: Datum): Datum | null {
    if (!Array.isArray(e)) return null;
    if (e[0] === sym(head)) return e;
    for (const s of e) {
      const f = walk(s);
      if (f) return f;
    }
    return null;
  })(form);
  if (!found) throw new Error(`no (${head} ...) in ${write(form)}`);
  return found;
}

// ---- expression predicates (termination.ss ~947-1230) ----

test("decreasing-expr? numeric and structural patterns", () => {
  for (const e of ["(- x 1)", "(- x 3)", "(sub1 x)", "(fx- x 2)", "(cdr x)", "(cddr x)", "(list-tail x 2)"]) {
    assert.ok(decreasingExpr(r(e), x), e);
  }
  for (const e of ["(- x 0)", "(- 1 x)", "(- x y)", "(list-tail x 0)", "(cdr y)", "(+ x 1)", "x", "(- x 1 2)"]) {
    assert.ok(!decreasingExpr(r(e), x), e);
  }
});

test("decreasing-expr? accepts an element of var or of its descent", () => {
  assert.ok(decreasingExpr(r("(%cfa-element x)"), x));
  assert.ok(decreasingExpr(r("(%cfa-spread (cdr x))"), x));
  assert.ok(!decreasingExpr(r("(%cfa-element y)"), x));
});

test("increasing-expr? and monotonic-expr?", () => {
  for (const e of ["(+ x 1)", "(+ 2 x)", "(add1 x)", "(fx+ x 1)"]) {
    assert.ok(increasingExpr(r(e), x), e);
    assert.ok(monotonicExpr(r(e), x), e);
  }
  for (const e of ["(+ x 0)", "(+ x y)", "(+ x 1 1)", "(- x 1)"]) assert.ok(!increasingExpr(r(e), x), e);
  assert.ok(monotonicExpr(r("(cdr x)"), x));
  assert.ok(!monotonicExpr(r("(* x 2)"), x));
});

test("expr-references-any? skips quoted data", () => {
  assert.ok(exprReferencesAny(r("(+ (car x) 1)"), [x]));
  assert.ok(!exprReferencesAny(r("(+ 'x 1)"), [x]));
  assert.ok(!exprReferencesAny(r("(+ x 1)"), []));
});

test("upper-bound tests and their pairs", () => {
  const vs = syms("i");
  for (const e of ["(>= i n)", "(> i n)", "(= i n)", "(= n i)"]) assert.ok(upperBoundBaseCaseTest(r(e), vs), e);
  for (const e of ["(= i 0)", "(= 0 i)", "(< i n)", "(>= n i)", "(>= i i)"]) assert.ok(!upperBoundBaseCaseTest(r(e), vs), e);
  assert.equal(showPairs([upperBoundTestPair(r("(= n i)"), vs)]), "((i . n))");
  assert.equal(showPairs([upperBoundTestPair(r("(>= i (length l))"), vs)]), "((i . (length l)))");
});

test("upper-bound-base-cases finds if, cond and unless base cases, newest first", () => {
  const body = readAll("(if (>= i n) 0 (f (+ i 1))) (cond ((> i m) 1) (else (f i))) (unless (= i k) (f i))");
  assert.equal(showPairs(upperBoundBaseCases(body, sym("f"), syms("i"))), "((i . k) (i . m) (i . n))");
  // A branch that recurses is not a base case.
  assert.equal(showPairs(upperBoundBaseCases(readAll("(if (>= i n) (f i) 0)"), sym("f"), syms("i"))), "()");
});

// ---- binder helpers (termination.ss ~2170-2245) ----

test("formal-names flattens nested and dotted formals", () => {
  assert.equal(write(formalNames(r("(a (b . c) . d)"))), "(a b c d)");
  assert.equal(write(formalNames(r("r"))), "(r)");
  assert.equal(write(formalNames(r("5"))), "()");
});

test("binding-names takes each binding's formals", () => {
  assert.equal(write(bindingNames(r("((x 1) ((a b) 2) bad)"))), "(x a b)");
  assert.equal(write(bindingNames(r("(x . y)"))), "()");
});

test("flatten-begins and define-names", () => {
  assert.equal(write(flattenBegins(readAll("a (begin b (begin c)) d"))), "(a b c d)");
  assert.equal(write(defineNames(readAll("(define (f x) 1) (begin (define y 2)) (g 3)"))), "(f x y)");
});

test("form-binds per binding form", () => {
  const cases: [string, string][] = [
    ["(lambda (a . b) (define c 1) c)", "(a b c)"],
    ["(define (f x) x)", "(f x)"],
    ["(case-lambda ((a) a) ((a b) b))", "(a a b)"],
    ["(let lp ((i 0)) i)", "(lp i)"],
    ["(let ((i 0) (j 1)) i)", "(i j)"],
    ["(let* ((i 0)) i)", "(i)"],
    ["(do ((i 0 (+ i 1))) ((= i 3)) i)", "(i)"],
    ["(let-values (((a b) (values 1 2))) a)", "(a b)"],
    ["(if a (define z 1) b)", "(z)"],
    ["(f . x)", "()"],
  ];
  for (const [form, names] of cases) assert.equal(write(formBinds(r(form))), names, form);
});

test("names-shadowed-at collects binders around the target by identity", () => {
  const prog = readAll("(define (f x) (let ((y 1)) (g y)))");
  const target = find(prog[0]!, "g");
  assert.equal(write(namesShadowedAt(prog, target)!), "(y f x f x)");
  // An equal but distinct form is not the target.
  assert.equal(namesShadowedAt(prog, r("(g y)")), null);
});

test("names-bound-around falls back to every binder in the program", () => {
  const prog = readAll("(define (f x) (let ((y 1)) (g y))) (define (h z) z)");
  const body = [find(prog[0]!, "let")];
  assert.equal(write(namesBoundAround(prog, body)), "(f x f x h z)");
  assert.equal(write(namesBoundAround(prog, readAll("(not-there)"))), "(h z y f x f x h z)");
});

test("body-binders collects every binder including its own defines", () => {
  assert.equal(write(bodyBinders(readAll("(define a 1) (let ((b 2)) (lambda (c) '(let ((q 1)) q)))"))), "(c b a a)");
});

// ---- guards (termination.ss ~2247-2408) ----

test("guards-at: if branches carry the test", () => {
  const body = readAll("(if (< x 0) 0 (f (- x 1)))");
  assert.equal(showGuards(guardsAt(body, find(body[0]!, "f"))), "(((< x 0) . #f))");
  const body2 = readAll("(if (> x 0) (f (- x 1)) 0)");
  assert.equal(showGuards(guardsAt(body2, find(body2[0]!, "f"))), "(((> x 0) . #t))");
  assert.equal(guardsAt(body, r("(f (- x 1))")), null);
});

test("guards-at: cond clauses see earlier tests false", () => {
  const body = readAll("(cond ((null? x) 0) ((pair? x) (f (cdr x))) (else (g x)))");
  assert.equal(showGuards(guardsAt(body, find(body[0]!, "f"))), "(((pair? x) . #t) ((null? x) . #f))");
  assert.equal(showGuards(guardsAt(body, find(body[0]!, "g"))), "(((pair? x) . #f) ((null? x) . #f))");
});

test("guards-at: when and unless", () => {
  const body = readAll("(when (< i n) (f (+ i 1))) (unless (zero? x) (g x))");
  assert.equal(showGuards(guardsAt(body, find(body[0]!, "f"))), "(((< i n) . #t))");
  assert.equal(showGuards(guardsAt(body, find(body[1]!, "g"))), "(((zero? x) . #f))");
});

test("guards-at: a rebinding drops the tests it mentions", () => {
  const body = readAll("(if (< x 0) 0 (if (> y 1) (let ((x 5)) (f x)) 1))");
  assert.equal(showGuards(guardsAt(body, find(body[0]!, "f"))), "(((> y 1) . #t))");
});

test("lower-stop-test? and lower-pass-test?", () => {
  for (const t of ["(< x 0)", "(<= x 0)", "(> 0 x)", "(>= 0 x)", "(not (> x 0))", "(not (positive? x))"]) {
    assert.ok(lowerStopTest(r(t), x, anyBound), t);
  }
  for (const t of ["(= x 0)", "(zero? x)", "(< x x)", "(< y 0)", "(> x 0)"]) assert.ok(!lowerStopTest(r(t), x, anyBound), t);
  assert.ok(!lowerStopTest(r("(< x n)"), x, noBound));
  for (const t of ["(positive? x)", "(> x 0)", "(>= x 1)", "(< 0 x)", "(<= 1 x)", "(not (< x 0))"]) {
    assert.ok(lowerPassTest(r(t), x, anyBound), t);
  }
  for (const t of ["(positive? x 1)", "(> x (- x 1))", "(< x 0)"]) assert.ok(!lowerPassTest(r(t), x, anyBound), t);
});

test("equality-stop-hint names the lower stop", () => {
  assert.equal(
    equalityStopHint(r("(define (f x) (if (= x 0) 0 (f (- x 1))))")),
    "; (= x 0) does not bound x from below, use (<= x 0)",
  );
  assert.equal(
    equalityStopHint(r("(define (f n) (if (zero? n) 0 (f (sub1 n))))")),
    "; (zero? n) does not bound n from below, use (<= n 0)",
  );
  assert.equal(equalityStopHint(r("(define (f x) (if (= x 0) 0 (f (+ x 1))))")), "");
  assert.equal(equalityStopHint(r("(define (f x) '(if (= x 0) 0 (f (- x 1))))")), "");
});

test("descent-guarded? needs a guard that stops descent", () => {
  assert.ok(descentGuarded(x, guards("(((> x 0) #t))"), anyBound));
  assert.ok(descentGuarded(x, guards("(((<= x 0) #f))"), anyBound));
  assert.ok(!descentGuarded(x, guards("(((= x 0) #f))"), anyBound));
  assert.ok(!descentGuarded(x, guards("(((> x n) #t))"), noBound));
});

test("ascent-guards rewrites true lower tests as false upper tests", () => {
  assert.equal(
    showGuards(ascentGuards(guards("(((< i n) #t) ((<= i n) #t) ((> n i) #t) ((>= n i) #t) ((not (>= i n)) #t) ((< i n) #f) ((null? l) #t))"))),
    "(((>= i n) . #f) ((> i n) . #f) ((>= i n) . #f) ((> i n) . #f) ((>= i n) . #f) ((< i n) . #f) ((null? l) . #t))",
  );
});

test("guard-upper-bound-pairs and ascent-guarded?", () => {
  const i = sym("i");
  assert.equal(showPairs(guardUpperBoundPairs(guards("(((< i n) #t) ((>= j m) #f))"), syms("i", "j"))), "((j . m) (i . n))");
  assert.ok(ascentGuarded(i, guards("(((< i n) #t))"), anyBound));
  assert.ok(ascentGuarded(i, guards("(((= n i) #f))"), anyBound));
  assert.ok(!ascentGuarded(i, guards("(((< i n) #t))"), noBound));
  assert.ok(!ascentGuarded(i, guards("(((< i n) #f))"), anyBound));
});
