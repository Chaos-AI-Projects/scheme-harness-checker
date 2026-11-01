// Direct unit tests for the size-change helpers of termination.ss (HC-16). test-termination.ss
// reaches these only through the Phase 5 and 6 drivers, so the cases are derived from the Scheme
// definitions.

import { test } from "node:test";
import assert from "node:assert/strict";
import { cdr, readAll, readOne, sym, write, Sym, type Datum } from "../src/sexp.ts";
import { extractDefinitions } from "../src/termination/callgraph.ts";
import { makeScGraph, type Arc, type ScGraph } from "../src/termination/sct.ts";
import type { Guard } from "../src/termination/guards.ts";
import {
  PURE_BOUND_OPS,
  SIZE_CHANGE_CAP,
  boundMeasure,
  boundedFormals,
  callScGraph,
  collectIntraSccCalls,
  sccSizeChange,
  cfaFullFormals,
  makeBoundOk,
  numericStep,
  properFormals,
  scCheckMembers,
  scDecreasingExpr,
  setTargets,
  unassignedFormals,
} from "../src/termination/sizechange.ts";

const r = readOne;
const x = sym("x");
const syms = (...names: string[]) => names.map(sym);
const anyBound = () => true;

// A graph's arcs as Scheme text, sorted so tests do not depend on arc order.
const arcsOf = (g: ScGraph): string => `(${g.arcs.map((a) => write([...a])).sort().join(" ")})`;
const guards = (text: string): Guard[] => (r(text) as Datum[][]).map((g) => [g[0]!, g[1] === true] as const);
const graph = (src: string, dst: string, arcs: string): ScGraph =>
  makeScGraph(r(src), r(dst), (r(arcs) as Datum[]).map((a) => a as unknown as Arc));

test("size-change-cap is 1000", () => {
  assert.equal(SIZE_CHANGE_CAP, 1000);
});

test("sc-decreasing-expr? adds car of var or of its descent", () => {
  assert.ok(scDecreasingExpr(r("(car x)"), x));
  assert.ok(scDecreasingExpr(r("(car (cdr x))"), x));
  assert.ok(scDecreasingExpr(r("(car (car x))"), x));
  assert.ok(scDecreasingExpr(r("(- x 1)"), x));
  assert.ok(!scDecreasingExpr(r("(car y)"), x));
  assert.ok(!scDecreasingExpr(r("(car x 1)"), x));
});

test("bound-measure is (bound . x)", () => {
  assert.equal(write(boundMeasure(x)), "(bound . x)");
});

test("set!-targets finds every target outside quoted data", () => {
  assert.equal(write(setTargets(r("(begin (set! a 1) (let () (set! b (set! c 2))) '(set! d 1))"))), "(a b c)");
  assert.equal(write(setTargets(r("(set! (car x) 1)"))), "()");
});

test("unassigned-formals replaces each assigned formal with a fresh symbol", () => {
  const out = unassignedFormals(syms("x", "y", "z"), readAll("(set! y 1) (f x)"));
  assert.equal(out[0], sym("x"));
  assert.equal(out[2], sym("z"));
  assert.ok(out[1] instanceof Sym && out[1] !== sym("y") && out[1] !== sym(out[1].name));
});

test("cfa-full-formals restores the rest formal as the tail", () => {
  assert.equal(write(cfaFullFormals({ formals: syms("a", "b"), rest: sym("r") })), "(a b . r)");
  assert.equal(write(cfaFullFormals({ formals: [], rest: sym("r") })), "r");
  assert.equal(write(cfaFullFormals({ formals: syms("a"), rest: null })), "(a)");
});

test("proper-formals drops the rest formal", () => {
  assert.equal(write(properFormals(r("(a b . c)"))), "(a b)");
  assert.equal(write(properFormals(r("r"))), "()");
  assert.equal(write(properFormals(r("(a b)"))), "(a b)");
});

test("numeric-step? names the step operators", () => {
  for (const e of ["(- x 1)", "(sub1 x)", "(fx- x 1)", "(+ x 1)", "(add1 x)", "(fx+ x 1)"]) assert.ok(numericStep(r(e)), e);
  for (const e of ["(cdr x)", "x", "(* x 2)"]) assert.ok(!numericStep(r(e)), e);
});

// call-sc-graph (termination.ss:1786)

test("call-sc-graph: numeric descent is strict only when guarded", () => {
  const f = sym("f");
  const call = r("(f (- x 1))") as Datum[];
  const g = callScGraph(f, [x], [], call, [x], true, "any", anyBound);
  assert.equal(write([g.src, g.dst]), "(f f)");
  assert.equal(arcsOf(g), "((x x #t))");
  assert.equal(arcsOf(callScGraph(f, [x], [], call, [x], true, [], anyBound)), "((x x #f))");
  assert.equal(arcsOf(callScGraph(f, [x], [], call, [x], true, guards("(((> x 0) #t))"), anyBound)), "((x x #t))");
  // numeric-strict? #f demotes it even when guarded.
  assert.equal(arcsOf(callScGraph(f, [x], [], call, [x], false, "any", anyBound)), "((x x #f))");
});

test("call-sc-graph: structural descent is strict unguarded and may cross positions", () => {
  const f = sym("f");
  assert.equal(arcsOf(callScGraph(f, [x], [], r("(f (cdr x))") as Datum[], [x], false, [], anyBound)), "((x x #t))");
  assert.equal(
    arcsOf(callScGraph(f, syms("x", "y"), [], r("(f y (cdr x))") as Datum[], syms("x", "y"), true, [], anyBound)),
    "((x y #t) (y x #f))",
  );
});

test("call-sc-graph: numeric descent may not cross positions", () => {
  const f = sym("f");
  assert.equal(
    arcsOf(callScGraph(f, syms("x", "y"), [], r("(f y (- x 1))") as Datum[], syms("x", "y"), true, "any", anyBound)),
    "((y x #f))",
  );
});

test("call-sc-graph: bound-minus arcs for bounded formals", () => {
  const f = sym("f");
  const i = sym("i");
  const call = r("(f (+ i 1) n)") as Datum[];
  assert.equal(
    arcsOf(callScGraph(f, syms("i", "n"), [i], call, syms("i", "n"), true, "any", anyBound)),
    "(((bound . i) (bound . i) #t) (n n #f))",
  );
  assert.equal(
    arcsOf(callScGraph(f, syms("i", "n"), [i], call, syms("i", "n"), true, guards("(((< i n) #t))"), anyBound)),
    "(((bound . i) (bound . i) #t) (n n #f))",
  );
  assert.equal(
    arcsOf(callScGraph(f, syms("i", "n"), [i], call, syms("i", "n"), true, [], anyBound)),
    "(((bound . i) (bound . i) #f) (n n #f))",
  );
  assert.equal(
    arcsOf(callScGraph(f, [i], [i], r("(f i)") as Datum[], [i], true, [], anyBound)),
    "(((bound . i) (bound . i) #f) (i i #f))",
  );
  // Not bounded: no measure arcs.
  assert.equal(arcsOf(callScGraph(f, syms("i", "n"), [], call, syms("i", "n"), true, "any", anyBound)), "((n n #f))");
});

test("call-sc-graph: extra arguments or parameters are ignored, and opaque #f args give no arc", () => {
  const f = sym("f");
  assert.equal(arcsOf(callScGraph(f, [x], [], [f, r("(cdr x)"), x], [x], true, [], anyBound)), "((x x #t))");
  assert.equal(arcsOf(callScGraph(f, [x], [], [f, false], [x], true, [], anyBound)), "()");
});

test("pure-bound-ops", () => {
  assert.equal(
    write([...PURE_BOUND_OPS]),
    "(length vector-length string-length + - * quotient remainder modulo abs min max car cdr cadr cddr)",
  );
});

test("make-bound-ok? accepts only stable bounds", () => {
  const ok = makeBoundOk(r("(i n)"), [r("(f (+ i 1) n)") as Datum[], r("(f i n)") as Datum[]], [], syms("tmp"));
  assert.ok(ok(sym("n")));
  assert.ok(!ok(sym("i")));
  assert.ok(ok(r("(length n)")));
  assert.ok(ok(r("(- (length n) 1)")));
  assert.ok(!ok(r("(vector-ref n 0)")));
  assert.ok(ok(r("'(1 2)")));
  assert.ok(ok(5));
  assert.ok(ok(sym("outer")));
  assert.ok(!ok(sym("tmp")));
  assert.ok(!ok(r("(length . n)")));
});

test("make-bound-ok? rejects assigned names, moving formals, rest formals and mutual SCCs", () => {
  assert.ok(!makeBoundOk(r("(i n)"), [r("(f i n)") as Datum[]], syms("n"), [])(sym("n")));
  assert.ok(!makeBoundOk(r("(i n)"), [r("(f i (cdr n))") as Datum[]], [], [])(sym("n")));
  assert.ok(!makeBoundOk(r("(i n)"), [r("(f i)") as Datum[]], [], [])(sym("n")));
  assert.ok(!makeBoundOk(r("(i n)"), null, [], [])(sym("n")));
  assert.ok(!makeBoundOk(r("(i . r)"), [r("(f i r)") as Datum[]], [], [])(sym("r")));
  // No calls at all: every formal is trivially in place.
  assert.ok(makeBoundOk(r("(i n)"), [], [], [])(sym("n")));
});

test("bounded-formals keeps formals with a stable bound, newest first, once each", () => {
  const pairs = [[sym("i"), sym("n")], [sym("j"), sym("m")], [sym("i"), sym("k")], [sym("q"), sym("n")]] as const;
  const stable = (e: Datum) => e !== sym("m");
  assert.equal(write(boundedFormals(pairs, syms("i", "j"), stable)), "(i)");
  assert.equal(write(boundedFormals(pairs, syms("i", "j"), () => true)), "(j i)");
});

test("sc-check-members", () => {
  const strict = graph("f", "f", "((x x #t))");
  const loose = graph("f", "f", "((x x #f))");
  assert.equal(scCheckMembers(() => [strict], 1), "terminates");
  assert.equal(scCheckMembers(() => [loose], 1), "no-descent");
  // Mutual: every call strict passes without the demoted check.
  const fg = graph("f", "g", "((x y #t))");
  const gf = graph("g", "f", "((y x #t))");
  assert.equal(scCheckMembers((ns) => (ns ? [fg, gf] : []), 2), "terminates");
  // Mutual with one non-strict edge falls back to the demoted graphs.
  const gfLoose = graph("g", "f", "((y x #f))");
  const fgDemoted = graph("f", "g", "((x y #f))");
  assert.equal(scCheckMembers((ns) => (ns ? [fg, gfLoose] : [fgDemoted, gfLoose]), 2), "no-descent");
  assert.equal(scCheckMembers((ns) => (ns ? [fg, gfLoose] : [fg, gfLoose]), 2), "terminates");
});

// collect-intra-scc-calls (termination.ss:2440)

const callsIn = (src: string, members: string[], userNames: string[] = []): string =>
  write(collectIntraSccCalls(readAll(src), syms(...members), syms(...userNames)).map((c) => [...c]));

test("collect-intra-scc-calls: calls to members, newest first", () => {
  assert.equal(callsIn("(if (null? l) 0 (+ (f (cdr l)) (g (car l) 1)))", ["f", "g"]), "((g (car l) 1) (f (cdr l)))");
  assert.equal(callsIn("(h '(f x))", ["f"]), "()");
});

test("collect-intra-scc-calls: an argument naming a rebound name is opaque", () => {
  assert.equal(callsIn("(let ((l (list l))) (f (car l)))", ["f"]), "((f #f))");
});

test("collect-intra-scc-calls: a call inside a captured lambda has opaque arguments", () => {
  assert.equal(callsIn("(let ((g (lambda () (f (cdr l))))) g)", ["f"]), "((f #f))");
  assert.equal(callsIn("(list (lambda () (f (cdr l))))", ["f"]), "((f #f))");
});

test("collect-intra-scc-calls: a lambda run in this activation keeps its arguments", () => {
  assert.equal(callsIn("((lambda () (f (cdr l))))", ["f"]), "((f (cdr l)))");
  assert.equal(callsIn("(map (lambda (x) (f (cdr l))) l)", ["f"]), "((f (cdr l)))");
  assert.equal(callsIn("(dynamic-wind (lambda () 1) (lambda () (f (cdr l))) (lambda () 2))", ["f"]), "((f (cdr l)))");
  assert.equal(callsIn("(let ((g (lambda () (f (cdr l))))) (g))", ["f"]), "((f (cdr l)))");
  // A user binding named map is not the HOF.
  assert.equal(callsIn("(map (lambda (x) (f (cdr l))) l)", ["f"], ["map"]), "((f #f))");
});

test("collect-intra-scc-calls: cond, case and do clauses are expressions", () => {
  assert.equal(callsIn("(cond ((f (cdr l)) 1) (else (lambda () (f l))))", ["f"]), "((f #f) (f (cdr l)))");
  assert.equal(callsIn("(case (f (cdr l)) ((1) (f l)))", ["f"]), "((f l) (f (cdr l)))");
  assert.equal(callsIn("(do ((i 0 (f i))) ((f l)) (f (cdr l)))", ["f"]), "((f (cdr l)) (f l) (f #f))");
});

// scc-size-change (termination.ss:1874)

function sccOf(src: string, names: string[]): string {
  const exprs = readAll(src);
  const defs = extractDefinitions(exprs);
  const forms = new Map(exprs.map((e) => [((e as Datum[])[1] as Datum[])[0], e as Datum[]]));
  return sccSizeChange(
    syms(...names),
    (n) => {
      const form = forms.get(n);
      return form ? cdr(form[1]!) : null;
    },
    (n) => defs.find(([d]) => d === n)?.[1] ?? [],
    exprs,
  );
}

test("scc-size-change: structural descent terminates", () => {
  assert.equal(sccOf("(define (f l) (if (null? l) 0 (f (cdr l))))", ["f"]), "terminates");
});

test("scc-size-change: guarded countdown terminates, an equality stop is unguarded", () => {
  assert.equal(sccOf("(define (f n) (if (<= n 0) 0 (f (- n 1))))", ["f"]), "terminates");
  assert.equal(sccOf("(define (f n) (if (= n 0) 0 (f (- n 1))))", ["f"]), "unguarded");
});

test("scc-size-change: count-up to a stable bound terminates", () => {
  // Cases from test-termination.ss:2349-2355. A formal is a var, so the bound is a top-level name.
  assert.equal(sccOf("(define n 10) (define (f i) (if (>= i n) 0 (f (+ i 1))))", ["f"]), "terminates");
  assert.equal(sccOf("(define n 10) (define (f i) (when (< i n) (f (+ i 1))))", ["f"]), "terminates");
  // A body-local bound is recomputed on each call; an assigned one can grow.
  assert.equal(
    sccOf("(define (f i l) (let ((n (length l))) (if (>= i n) 0 (f (+ i 1) (cons 1 l)))))", ["f"]),
    "no-descent",
  );
  assert.equal(
    sccOf("(define n 10) (define (f i) (if (>= i n) 0 (begin (set! n (+ n 1)) (f (+ i 1)))))", ["f"]),
    "no-descent",
  );
});

test("scc-size-change: no descent, and a captured descent", () => {
  assert.equal(sccOf("(define (f x) (f x))", ["f"]), "no-descent");
  assert.equal(sccOf("(define (f l) (if (null? l) 0 (let ((g (lambda () (f (cdr l))))) g)))", ["f"]), "no-descent");
});

test("scc-size-change: mutual recursion", () => {
  assert.equal(
    sccOf("(define (ev n) (if (<= n 0) #t (od (- n 1)))) (define (od n) (if (<= n 0) #f (ev (- n 1))))", ["ev", "od"]),
    "terminates",
  );
  // One numeric edge cannot carry a cycle through an edge that decreases nothing.
  assert.equal(
    sccOf("(define (ev n) (if (<= n 0) #t (od (- n 1)))) (define (od n) (if (<= n 0) #f (ev (+ n 1))))", ["ev", "od"]),
    "no-descent",
  );
});
