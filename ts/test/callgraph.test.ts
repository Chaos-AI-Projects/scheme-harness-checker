// The Phase 2 cases of tests/test-termination.ss, transcribed: definition extraction, the call
// graph and Tarjan's SCCs.

import { test } from "node:test";
import assert from "node:assert/strict";
import { readAll, sym, write, type Datum, type Sym } from "../src/sexp.ts";
import { buildCallGraph, callGraphEdges, extractDefinitions, tarjanScc } from "../src/termination/callgraph.ts";

const graphOf = (source: string) => buildCallGraph(readAll(source));
const edges = (source: string, name: string): string => write(callGraphEdges(graphOf(source), sym(name)));
const defNames = (source: string): string[] => extractDefinitions(readAll(source)).map(([n]) => n.name);

// The SCC holding `name`, its members sorted, as Scheme text; "#f" when none holds it.
function sccOf(sccs: readonly (readonly Datum[])[], name: string): string {
  const scc = sccs.find((c) => c.includes(sym(name)));
  return scc ? write([...scc].sort((a, b) => ((a as Sym).name < (b as Sym).name ? -1 : 1))) : "#f";
}

test("extracts define-fn name and body", () => {
  const [def] = extractDefinitions(readAll("(define (f x) (+ x 1))"));
  assert.equal(def![0], sym("f"));
  assert.equal(write(def![1]), "((+ x 1))");
});

test("extracts define-lambda name and body", () => {
  const [def] = extractDefinitions(readAll("(define f (lambda (x) (+ x 1)))"));
  assert.equal(def![0], sym("f"));
  assert.equal(write(def![1]), "((+ x 1))");
});

test("extracts case-lambda name and every clause body", () => {
  const [def] = extractDefinitions(readAll("(define f (case-lambda ((x) (+ x 1)) ((x y) (+ x y))))"));
  assert.equal(def![0], sym("f"));
  assert.equal(write(def![1]), "((+ x 1) (+ x y))");
});

test("non-definition returns empty", () => {
  assert.deepEqual(defNames("(+ 1 2)"), []);
});

test("extracts multiple definitions", () => {
  assert.deepEqual(defNames("(define (f x) (+ x 1)) (define (g y) (* y 2))"), ["f", "g"]);
});

test("letrec extracts its lambda bindings", () => {
  assert.deepEqual(
    defNames("(letrec ((ping (lambda (n) (if (= n 0) 'done (pong (- n 1))))) (pong (lambda (n) (if (= n 0) 'done (ping (- n 1)))))) (ping 10))"),
    ["ping", "pong"],
  );
});

test("internal defines come after their parent", () => {
  assert.deepEqual(defNames("(define (outer x) (define (inner y) (+ y 1)) (inner x))"), ["outer", "inner"]);
});

test("a definition inside a letrec init or an operator is found", () => {
  assert.deepEqual(defNames("(letrec ((v (let () (define (g) 1) g))) v)"), ["g"]);
  assert.deepEqual(defNames("((letrec ((lp (lambda (n) n))) lp) 1)"), ["lp"]);
});

test("quoted data and dotted forms hold no definitions and do not raise", () => {
  assert.deepEqual(defNames("(quote (define (f x) x))"), []);
  assert.deepEqual(defNames("(define (f a . rest) (g a)) (define (g . xs) xs)"), ["f", "g"]);
});

test("direct recursion: fact has exactly one edge, itself", () => {
  assert.equal(edges("(define (fact n) (if (= n 0) 1 (* n (fact (- n 1)))))", "fact"), "(fact)");
});

test("mutual recursion: even? and odd? call each other", () => {
  const src = "(define (even? n) (if (= n 0) #t (odd? (- n 1)))) (define (odd? n) (if (= n 0) #f (even? (- n 1))))";
  assert.equal(edges(src, "even?"), "(odd?)");
  assert.equal(edges(src, "odd?"), "(even?)");
});

test("non-recursive functions have no edges", () => {
  assert.equal(edges("(define (add x y) (+ x y))", "add"), "()");
  const src = "(define (f x) (+ x 1)) (define (g y) (* y 2))";
  assert.equal(edges(src, "f"), "()");
  assert.equal(edges(src, "g"), "()");
});

test("caller/callee: quad calls double", () => {
  const src = "(define (double x) (* x 2)) (define (quad x) (double (double x)))";
  assert.equal(edges(src, "double"), "()");
  assert.equal(edges(src, "quad"), "(double)");
});

test("a quoted name is not a call edge", () => {
  assert.equal(edges("(define (f x) (list 'g x)) (define (g y) y)", "f"), "()");
  const src = "(define (f x) (g x)) (define (g y) y) (define (h z) (list 'f z))";
  assert.equal(edges(src, "f"), "(g)");
  assert.equal(edges(src, "g"), "()");
  assert.equal(edges(src, "h"), "()");
});

test("outer calls its internal define", () => {
  const src = "(define (outer x) (define (inner y) (+ y 1)) (inner x))";
  assert.equal(edges(src, "outer"), "(inner)");
  assert.equal(edges(src, "inner"), "()");
});

test("a nested call is an edge, in Scheme's order", () => {
  // collect-calls-in-body conses, so the last call found comes first.
  assert.equal(edges("(define (f x) (g (h x))) (define (g y) y) (define (h z) z)", "f"), "(h g)");
});

test("a callback in argument position is not an edge; a direct call is", () => {
  assert.equal(edges("(define (process lst) (map helper lst)) (define (helper x) (+ x 1))", "process"), "()");
  assert.equal(edges("(define (process lst) (helper (car lst))) (define (helper x) (+ x 1))", "process"), "(helper)");
});

test("a user definition named like a collection HOF is not an edge", () => {
  assert.equal(edges("(define (map f l) (map f l))", "map"), "()");
});

test("empty source and no definitions produce an empty graph", () => {
  assert.deepEqual(graphOf(""), []);
  assert.deepEqual(graphOf('(+ 1 2) (display "hello")'), []);
});

test("SCC: direct recursion", () => {
  assert.equal(sccOf(tarjanScc(graphOf("(define (fact n) (if (= n 0) 1 (* n (fact (- n 1)))))")), "fact"), "(fact)");
});

test("SCC: mutual recursion shares one component", () => {
  const sccs = tarjanScc(graphOf("(define (even? n) (if (= n 0) #t (odd? (- n 1)))) (define (odd? n) (if (= n 0) #f (even? (- n 1))))"));
  assert.equal(sccs.find((c) => c.includes(sym("even?"))), sccs.find((c) => c.includes(sym("odd?"))));
  assert.equal(sccOf(sccs, "even?"), "(even? odd?)");
});

test("SCC: a non-recursive function is a trivial component", () => {
  assert.equal(sccOf(tarjanScc(graphOf("(define (add x y) (+ x y))")), "add"), "(add)");
});

test("SCC: mixed graph", () => {
  const sccs = tarjanScc(
    graphOf(
      "(define (helper x) (+ x 1)) (define (fact n) (if (= n 0) 1 (* n (fact (- n (helper 0)))))) " +
        "(define (even? n) (if (= n 0) #t (odd? (- n 1)))) (define (odd? n) (if (= n 0) #f (even? (- n 1))))",
    ),
  );
  assert.equal(sccOf(sccs, "helper"), "(helper)");
  assert.equal(sccOf(sccs, "fact"), "(fact)");
  assert.equal(sccOf(sccs, "even?"), "(even? odd?)");
});

test("SCC: one self-recursive function gives one component", () => {
  assert.equal(tarjanScc(graphOf("(define (f x) (if x (f (not x)) x))")).length, 1);
});

test("SCC: components come in Scheme's order, root first within each", () => {
  // a -> b -> c -> b: Tarjan pops {b c} before {a}; the Scheme conses each, so {a} comes first.
  const g = graphOf("(define (a) (b)) (define (b) (c)) (define (c) (b))");
  assert.equal(write(tarjanScc(g)), "((a) (b c))");
});
