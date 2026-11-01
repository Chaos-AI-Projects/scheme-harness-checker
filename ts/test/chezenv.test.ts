// The Chez scheme-environment names alpha-rename-definitions (termination.ss:2960 misread-name?) treats
// as builtins or keywords. The table is generated from Chez by test/differential/regen-chezenv.sh.

import { test } from "node:test";
import assert from "node:assert/strict";
import { CHEZ_VERSION, isChezSchemeName } from "../src/termination/chezenv.ts";

test("isChezSchemeName knows Chez's procedures and syntactic keywords", () => {
  for (const n of ["car", "-", "map", "fold-left", "cons*", "fx-", "vector-ref", "display", "list-tail", "sub1"])
    assert.equal(isChezSchemeName(n), true, n);
  for (const n of ["define", "lambda", "let", "letrec*", "case-lambda", "guard", "do", "quasiquote", "parameterize"])
    assert.equal(isChezSchemeName(n), true, n);
});

test("isChezSchemeName leaves user names alone", () => {
  for (const n of ["helper", "my-map", "loop", "f", "lambda@3", "car~1", "%cfa-element", "tool-get"])
    assert.equal(isChezSchemeName(n), false, n);
});

test("the table records the Chez it came from", () => {
  assert.match(CHEZ_VERSION, /^\d+\.\d+\.\d+$/);
});
