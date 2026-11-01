// The HOF-callback pass of termination.ss (HC-17, Phase 7). Unit cases are the hof-callback-position,
// collect-hof-callback-edges and user-defined HOF groups of test-termination.ss (from line 1340).
// Its end-to-end cases need check-termination's proven-terminating set, which the driver builds.

import { test } from "node:test";
import assert from "node:assert/strict";
import { readAll, sym, write } from "../src/sexp.ts";
import { extractDefinitions } from "../src/termination/callgraph.ts";
import {
  checkHofCallbacks,
  collectHofCallbackEdges,
  collectUserHofCallbackEdges,
  detectUserDefinedHofs,
  hofCallbackPosition,
  paramInCallPosition,
} from "../src/termination/hof.ts";

test("hofCallbackPosition follows termination.ss's table", () => {
  for (const n of ["map", "fold-left", "filter", "vector-map"]) assert.equal(hofCallbackPosition(sym(n)), 0);
  for (const n of ["memv", "memq", "remv", "assoc", "my-custom-fn", "partition"]) assert.equal(hofCallbackPosition(sym(n)), null);
});

const edges = (source: string, caller: string) => write(collectHofCallbackEdges(readAll(source), sym(caller)).map(([c, , cb]) => [c, cb]));

test("collectHofCallbackEdges", () => {
  assert.equal(edges("(map helper lst)", "process"), "((process helper))");
  assert.equal(edges("(map (lambda (x) (+ x 1)) lst)", "process"), "()");
  assert.equal(edges("(memq val lst)", "process"), "()");
  assert.equal(edges("(fold-left combine 0 lst)", "accum"), "((accum combine))");
  // The Scheme walks operands before the operator and conses, so the outer call's edge is last.
  assert.equal(edges("(map f (filter g lst))", "process"), "((process g) (process f))");
  assert.equal(edges("'(map f lst)", "process"), "()");
  assert.equal(edges("(map . f)", "process"), "()");
});

const MY_MAP = "(define (my-map f lst) (if (null? lst) '() (cons (f (car lst)) (my-map f (cdr lst)))))";

const hofsOf = (source: string) => {
  const exprs = readAll(source);
  return write(detectUserDefinedHofs(extractDefinitions(exprs), exprs).map(([n, p]) => [n, p]));
};

test("detectUserDefinedHofs", () => {
  assert.equal(hofsOf(MY_MAP), "((my-map 0))");
  assert.equal(hofsOf("(define (add1 x) (+ x 1))"), "()");
  assert.equal(hofsOf("(define (my-fold init f lst) (if (null? lst) init (my-fold (f init (car lst)) f (cdr lst))))"), "((my-fold 1))");
  // Only the first formal called counts, and collection HOF names are excluded.
  assert.equal(hofsOf("(define (two f g) (f (g 1)))"), "((two 0))");
  assert.equal(hofsOf("(define (map f xs) (f xs))"), "()");
});

test("paramInCallPosition skips quoted forms and finds operators only", () => {
  assert.equal(paramInCallPosition(sym("f"), readAll("(g (f 1))")), true);
  assert.equal(paramInCallPosition(sym("f"), readAll("(g f)")), false);
  assert.equal(paramInCallPosition(sym("f"), readAll("'(f 1)")), false);
  assert.equal(paramInCallPosition(sym("f"), readAll("((f 1) 2)")), true);
});

test("collectUserHofCallbackEdges finds a callback passed to a user HOF", () => {
  const exprs = readAll(`${MY_MAP} (define (helper x) (+ x 1)) (define (process data) (my-map helper data))`);
  const defs = extractDefinitions(exprs);
  const hofs = detectUserDefinedHofs(defs, exprs);
  const body = defs.find(([n]) => n === sym("process"))![1];
  assert.equal(write(collectUserHofCallbackEdges(body, sym("process"), hofs).map((e) => [...e])), "((process my-map helper))");
});

test("checkHofCallbacks flags an unproven callback to a collection HOF", () => {
  const exprs = readAll("(define (process lst) (map spin lst)) (define (spin x) (spin x))");
  const defs = extractDefinitions(exprs);
  const [v, ...rest] = checkHofCallbacks(defs, [sym("process"), sym("spin")], [sym("process")]);
  assert.equal(rest.length, 0);
  assert.equal(v!.kind, "hof-callback-not-terminating");
  assert.equal(v!.function, sym("process"));
  assert.equal(write(v!.expr), "(define process ...)");
  assert.equal(v!.reason, 'HOF callback "spin" passed in function "process" is not proven terminating');
});

test("checkHofCallbacks checks a user HOF's callbacks only when the HOF is proven", () => {
  const exprs = readAll(`${MY_MAP} (define (spin x) (spin x)) (define (process data) (my-map spin data))`);
  const defs = extractDefinitions(exprs);
  const names = [sym("my-map"), sym("spin"), sym("process")];
  const hofs = detectUserDefinedHofs(defs, exprs);
  const [v] = checkHofCallbacks(defs, names, [sym("my-map"), sym("process")], hofs);
  assert.equal(v!.reason, 'HOF callback "spin" passed to user-defined HOF "my-map" in function "process" is not proven terminating');
  assert.deepEqual(checkHofCallbacks(defs, names, [sym("process")], hofs), []);
});

test("checkHofCallbacks ignores callbacks that are not user-defined", () => {
  const exprs = readAll("(define (process lst) (map car lst))");
  assert.deepEqual(checkHofCallbacks(extractDefinitions(exprs), [sym("process")], []), []);
});
