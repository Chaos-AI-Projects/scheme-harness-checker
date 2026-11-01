// The cases of tests/test-cfa.ss, transcribed.

import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { car, cdr, equal, isPair, readAll, readOne, sym, write, type Datum } from "../src/sexp.ts";
import { cfaAnalyze, cfaLambdaRef, cfaModeledBuiltin, cfaSiteCalleeLabels, cfaSiteOf, type CfaResult } from "../src/termination/cfa.ts";

function analyze(source: string): CfaResult {
  return cfaAnalyze(readAll(source));
}

// A lambda's display name: its bound symbol, else its label.
function lambdaName(result: CfaResult, label: number): string {
  const name = cfaLambdaRef(result, label)!.name;
  return name ? name.name : String(label);
}

// Every call site whose expression is equal to `datum`, as Scheme text
// ((caller-name callee-name ...) ...). The top level is named `top`.
function calleesAt(source: string, datum: string): string {
  const r = analyze(source);
  const want = readOne(datum);
  const rows = r.sites
    .filter((s) => equal(s.expr, want))
    .map((s) => [
      sym(s.caller === null ? "top" : lambdaName(r, s.caller)),
      ...cfaSiteCalleeLabels(s).map((l) => sym(lambdaName(r, l))),
    ]);
  return write(rows);
}

function siteUnresolved(source: string, datum: string): boolean {
  const want = readOne(datum);
  return analyze(source).sites.some((s) => equal(s.expr, want) && s.unresolved);
}

// direct calls

test("direct call to a define", () => {
  assert.equal(calleesAt("(define (f x) (g x)) (define (g y) y)", "(g x)"), "((f g))");
});

test("call to a built-in has no callees", () => {
  assert.equal(calleesAt("(define (f x) (car x))", "(car x)"), "((f))");
});

// the HC-2 loops

test("omega: outer site calls the first lambda", () => {
  assert.equal(
    calleesAt("((lambda (x) (x x)) (lambda (x) (x x)))", "((lambda (x) (x x)) (lambda (x) (x x)))"),
    "((top 0))",
  );
});

test("omega: both (x x) sites call the second lambda", () => {
  assert.equal(calleesAt("((lambda (x) (x x)) (lambda (x) (x x)))", "(x x)"), "((0 1) (1 1))");
});

test("self-application through a formal", () => {
  assert.equal(calleesAt("(define (f g) (g g)) (f f)", "(g g)"), "((f f))");
});

test("alias through let", () => {
  assert.equal(calleesAt("(define (loop n) (let ((h loop)) (h n))) (loop 3)", "(h n)"), "((loop loop))");
});

test("recursion through map", () => {
  assert.equal(calleesAt("(define (f x) (map f (list x))) (f 1)", "(map f (list x))"), "((f f))");
});

test("anonymous self-application inside a define", () => {
  assert.equal(calleesAt("(define (f) (let ((g (lambda (h) (h h)))) (g g))) (f)", "(h h)"), "((1 1))");
});

// data structures

test("lambda stored with cons and read with car", () => {
  assert.equal(calleesAt("(define (f x) ((car (cons f '())) x))", "((car (cons f '())) x)"), "((f f))");
});

test("cdr returns the rest of a list", () => {
  assert.equal(calleesAt("(define (g) 0) (define (f) ((cadr (list 1 g))))", "((cadr (list 1 g)))"), "((f g))");
});

test("vector-set! then vector-ref", () => {
  assert.equal(
    calleesAt(
      "(define (g) 1) (define (f v) (vector-set! v 0 g) ((vector-ref v 0))) (f (make-vector 1 0))",
      "((vector-ref v 0))",
    ),
    "((f g))",
  );
});

test("quasiquote holds an unquoted lambda", () => {
  assert.equal(calleesAt("(define (g) 1) (define (f) ((car `(,g))))", "((car `(,g)))"), "((f g))");
});

// apply and HOFs

test("apply with leading and list arguments", () => {
  assert.equal(calleesAt("(define (h a b) a) (define (f) (apply h 1 (list 2)))", "(apply h 1 (list 2))"), "((f h))");
});

test("apply spreads a list of lambdas into the formals", () => {
  assert.equal(calleesAt("(define (k) 0) (define (f g) (g)) (apply f (list k))", "(g)"), "((f k))");
});

test("HOF callback receives list elements", () => {
  assert.equal(calleesAt("(define (k) 0) (define (f) (for-each (lambda (g) (g)) (list k)))", "(g)"), "((2 k))");
});

test("fold-left accumulator flows back to the callback", () => {
  assert.equal(
    calleesAt("(define (k) 0) (define (f) (fold-left (lambda (acc x) (acc)) k (list 1)))", "(acc)"),
    "((2 k))",
  );
});

test("a built-in passed as a callback adds no callees", () => {
  assert.equal(calleesAt("(define (f l) (for-each display l))", "(for-each display l)"), "((f))");
});

// binding forms

test("named let loop calls itself", () => {
  assert.equal(
    calleesAt("(define (f n) (let loop ((i n)) (if (= i 0) 0 (loop (- i 1)))))", "(loop (- i 1))"),
    "((loop loop))",
  );
});

test("letrec binding", () => {
  assert.equal(calleesAt("(letrec ((ev (lambda (n) n))) (ev 1))", "(ev 1)"), "((top ev))");
});

test("set! adds to a variable", () => {
  assert.equal(calleesAt("(define (g) 1) (define (f) (let ((h 0)) (set! h g) (h)))", "(h)"), "((f g))");
});

test("inner binding shadows an outer name", () => {
  assert.equal(calleesAt("(define (g) 1) (define (f g) (g)) (f 2)", "(g)"), "((f))");
});

test("case-lambda dispatches on arity", () => {
  const r = analyze("(define f (case-lambda ((x) x) ((x y) (f x))))");
  const s = r.sites.find((s) => equal(s.expr, readOne("(f x)")))!;
  assert.equal(cfaSiteCalleeLabels(s).length, 1);
});

test("cond => invokes the procedure", () => {
  assert.equal(calleesAt("(define (g x) x) (define (f y) (cond (y => g) (else 0)))", "(y => g)"), "((f g))");
});

// lambda records

test("define gets kind define and its name; letrec gets kind letrec", () => {
  const r = analyze("(define (f g) (g g)) (letrec ((h (lambda () 0))) (h))");
  const f = cfaLambdaRef(r, 0)!;
  assert.deepEqual([f.kind, f.name, f.parent], ["define", sym("f"), null]);
  const h = cfaLambdaRef(r, 1)!;
  assert.deepEqual([h.kind, h.name], ["letrec", sym("h")]);
});

test("an inner lambda records its parent", () => {
  const r = analyze("(define (f n) (for-each (lambda (x) x) n))");
  const l = cfaLambdaRef(r, 1)!;
  assert.deepEqual([l.kind, l.name, l.parent], ["lambda", null, 0]);
});

// fail-closed

test("a value returned by an unmodeled operator is unresolved", () => {
  assert.equal(siteUnresolved("(define (f x) ((tool-get x f)))", "((tool-get x f))"), true);
});

test("a lambda handed to an unmodeled operator escapes", () => {
  assert.equal(calleesAt("(define (f x) (tool-run f))", "(tool-run f)"), "((f f))");
});

test("opaque data in operator position is not unresolved", () => {
  assert.equal(siteUnresolved("(define (f x) ((car (list (+ x 1)))))", "((car (list (+ x 1))))"), false);
});

test("an unmodeled operator given only data returns data", () => {
  assert.equal(siteUnresolved("(define (f x) ((tool-get 1)))", "((tool-get 1))"), false);
});

// The whitelist has no procedure-returning built-in, so opaque data can never
// reach operator position. If a signature gains a function return type, cfa.ts
// must model that built-in.
const signatures = readOne(readFileSync(new URL("../../data/type-signatures.scm", import.meta.url), "utf8")) as Datum[];

function functionType(t: Datum): boolean {
  return isPair(t) && (car(t) === sym("->") || car(t) === sym("->*"));
}

function returnType(sig: Datum): Datum {
  return functionType(sig) ? (sig as Datum[])[(sig as Datum[]).length - 1]! : sig;
}

test("no whitelisted built-in returns a procedure", () => {
  const bad = signatures.filter((e) => functionType(returnType(cdr(e))));
  assert.deepEqual(bad.map((e) => write(car(e))), []);
});

test("every whitelisted built-in is modeled by cfa.ts", () => {
  assert.ok(signatures.length > 50);
  const names = signatures.map(car);
  assert.deepEqual(names.filter((n) => !cfaModeledBuiltin(n)).map(write), []);
});

// Beyond the Scheme suite: the result's lookups by source form.

test("cfaSiteOf finds a site by its source object, not by structure", () => {
  const forms = readAll("(define (g) 0) (define (f) (g) (g))");
  const r = cfaAnalyze(forms);
  const body = forms[1] as Datum[];
  const first = body[2]!;
  const second = body[3]!;
  assert.ok(isPair(first));
  assert.equal(cfaSiteOf(r, first)!.expr, first);
  assert.equal(cfaSiteOf(r, second)!.expr, second);
  assert.notEqual(cfaSiteOf(r, first), cfaSiteOf(r, second));
  assert.equal(cfaSiteOf(r, readOne("(g)")), undefined);
});
