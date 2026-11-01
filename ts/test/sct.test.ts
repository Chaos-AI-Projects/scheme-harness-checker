// The cases of tests/test-sct.ss, transcribed.

import { test } from "node:test";
import assert from "node:assert/strict";
import { readOne, write, type Datum } from "../src/sexp.ts";
import { makeScGraph, scCheck, scCompose, type Arc, type ScGraph } from "../src/termination/sct.ts";

// A graph from Scheme text, e.g. g("f", "g", "((x y #f))").
function g(src: string, dst: string, arcs: string): ScGraph {
  return makeScGraph(readOne(src), readOne(dst), (readOne(arcs) as Datum[]).map((a) => a as unknown as Arc));
}

// A graph's arcs as Scheme text, sorted so tests do not depend on arc order.
function arcsOf(graph: ScGraph): string {
  return write(graph.arcs.map((a) => write([...a])).sort().map((s) => readOne(s)));
}

test("duplicate arcs merge, strict wins", () => {
  assert.equal(arcsOf(g("f", "g", "((x y #f) (x y #t) (x y #f))")), "((x y #t))");
});

test("graph keeps its endpoints", () => {
  const graph = g("f", "g", "()");
  assert.equal(write([graph.src, graph.dst]), "(f g)");
});

test("non-strict then strict is strict", () => {
  assert.equal(arcsOf(scCompose(g("tree-sum", "my-map", "((t l #f))"), g("my-map", "tree-sum", "((l t #t))"))), "((t t #t))");
});

test("non-strict then non-strict is non-strict", () => {
  assert.equal(arcsOf(scCompose(g("f", "g", "((x y #f))"), g("g", "h", "((y z #f))"))), "((x z #f))");
});

test("an arc needs both halves", () => {
  assert.equal(arcsOf(scCompose(g("f", "g", "((x y #t))"), g("g", "h", "((w z #t))"))), "()");
});

test("two paths to one arc keep the strict one", () => {
  assert.equal(arcsOf(scCompose(g("f", "g", "((x a #f) (x b #t))"), g("g", "h", "((a z #f) (b z #f))"))), "((x z #t))");
});

test("argument swap composes to strict self-arcs", () => {
  const graph = g("f", "f", "((x y #t) (y x #f))");
  assert.equal(arcsOf(scCompose(graph, graph)), "((x x #t) (y y #t))");
});

test("arcs are kept in Scheme's canonical order", () => {
  assert.equal(write(g("f", "f", "((y x #f) (x y #t))").arcs.map((a) => [...a])), "((x y #t) (y x #f))");
});

test("empty graph set terminates", () => {
  assert.equal(scCheck([], 1000), "terminates");
});

test("direct recursion with a strict self-arc terminates", () => {
  assert.equal(scCheck([g("f", "f", "((n n #t))")], 1000), "terminates");
});

test("direct recursion with only a non-strict arc does not", () => {
  assert.equal(scCheck([g("f", "f", "((n n #f))")], 1000), "no-descent");
});

test("direct recursion with no arcs does not", () => {
  assert.equal(scCheck([g("f", "f", "()")], 1000), "no-descent");
});

test("tree-sum through my-map terminates", () => {
  const graphs = [
    g("tree-sum", "my-map", "((t l #f))"),
    g("my-map", "my-map", "((g g #f) (l l #t))"),
    g("my-map", "tree-sum", "((l t #t))"),
  ];
  assert.equal(scCheck(graphs, 1000), "terminates");
});

// (define (f x y) (if (<= x 0) 0 (f y (- x 1))))
test("argument swap terminates", () => {
  assert.equal(scCheck([g("f", "f", "((x y #t) (y x #f))")], 1000), "terminates");
});

// (define (f x y) (if (<= x 0) 0 (f (+ y 1) (- x 1))))
test("swap with growth does not", () => {
  assert.equal(scCheck([g("f", "f", "((x y #t))")], 1000), "no-descent");
});

// Each edge alone decreases something, but the path f->g->f does not.
test("a cycle that decreases per edge but not round the loop", () => {
  assert.equal(scCheck([g("f", "g", "((x a #t))"), g("g", "f", "((b x #t))")], 1000), "no-descent");
});

test("mutual recursion that decreases round the loop terminates", () => {
  assert.equal(scCheck([g("even?", "odd?", "((n n #t))"), g("odd?", "even?", "((n n #t))")], 1000), "terminates");
});

test("the cap rejects with size-change-limit", () => {
  const graphs = [g("f", "f", "((a b #f) (b c #f) (c a #t))"), g("f", "f", "((a a #f) (b c #t) (c b #f))")];
  assert.equal(scCheck(graphs, 2), "limit");
});

test("derived measures compare by structure", () => {
  assert.equal(scCheck([g("f", "f", "(((- n i) (- n i) #t))")], 1000), "terminates");
});
