// The termination driver (HC-17): checkTermination against termination.ss's check-termination, with an
// empty type-env as test-termination.ss runs it, over every program test-termination.ss checks.
// check.oracle.txt is Chez's output, regenerated with test/differential/regen-phase2b.sh; a line is
// ((kind function reason expr) ...), or (skipped rc) when Chez could not finish that program.

import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { readAll, readOne, sym, write, type Datum } from "../src/sexp.ts";
import { checkTermination } from "../src/termination/check.ts";
import type { TerminationViolation } from "../src/termination/violation.ts";

const fixture = (name: string): string[] =>
  readFileSync(new URL(`./differential/${name}`, import.meta.url), "utf8").split("\n").filter((l) => l !== "");

const corpus = fixture("phase2b.corpus.txt");
const oracle = fixture("check.oracle.txt");

const asList = (v: TerminationViolation): Datum[] => [sym(v.kind), v.function ?? false, v.reason, v.expr];

// An anonymous-cycle violation names the first in-cycle edge, which follows Chez's unspecified `map`
// order (cfa.ts header), so its site is compared only as "some site". Violations compare as sets.
const normalise = (vs: readonly Datum[]): string[] =>
  vs
    .map((v) => {
      const [kind, fn, reason] = v as Datum[];
      const anon = typeof reason === "string" && reason.startsWith("anonymous lambda recursion");
      return write(anon ? [kind!, fn!, reason!, sym("<cycle-site>")] : v);
    })
    .sort();

const kinds = (source: string, maxDefinitions: number | null = null): string[] =>
  checkTermination(readAll(source), maxDefinitions).map((v) => v.kind);

test("the check fixtures line up one oracle row per program", () => {
  assert.equal(oracle.length, corpus.length);
});

test("a name defined twice at top level is reported once", () => {
  const vs = checkTermination(readAll("(define (f) 1) (define (f) 2) (begin (define (f) 3))"));
  assert.deepEqual(vs.map((v) => [v.kind, v.function]), [["duplicate-definition", sym("f")]]);
  assert.equal(vs[0]!.reason, '"f" is defined more than once at top level');
});

test("a cyclic datum rejects the whole program before analysis", () => {
  const cell: Datum[] = [1];
  cell.push(cell);
  const vs = checkTermination([[sym("quote"), cell]]);
  assert.deepEqual(vs.map((v) => [v.kind, v.function, v.expr]), [["cyclic-datum", null, false]]);
});

test("shared but acyclic structure is accepted", () => {
  const shared: Datum[] = [1];
  assert.deepEqual(checkTermination([[sym("quote"), [shared, shared]]]), []);
});

test("more definitions than max-definitions blocks the program", () => {
  assert.deepEqual(kinds("(define (f) 1) (define (g) 2)", 1), ["definition-limit-exceeded"]);
  assert.deepEqual(kinds("(define (f) 1) (define (g) 2)", 2), []);
});

test("a renamed top-level builtin is reported under its own name", () => {
  const [v, ...rest] = checkTermination(readAll("(define (car x) (car x)) (car 1)"));
  assert.equal(rest.length, 0);
  assert.equal(v!.function, sym("car"));
  assert.equal(write(v!.expr), "(define (car x) (car x))");
  assert.ok(!v!.reason.includes("car~"), v!.reason);
});

test("checkTermination agrees with check-termination over the corpus", () => {
  let compared = 0;
  const unreadable: number[] = [];
  const diffs: string[] = [];
  corpus.forEach((line, i) => {
    const source = readOne(line) as string;
    let exprs: Datum[];
    try {
      exprs = readAll(source);
    } catch {
      unreadable.push(i + 1);
      return;
    }
    if (oracle[i]!.startsWith("(skipped") || oracle[i] === "(error)") {
      diffs.push(`program ${i + 1}: Chez gave ${oracle[i]} on a program the TS reader accepts`);
      return;
    }
    const want = normalise(readOne(oracle[i]!) as Datum[]);
    let have: string[];
    try {
      have = normalise(checkTermination(exprs).map(asList));
    } catch (e) {
      have = [`threw ${(e as Error).message}`];
    }
    compared++;
    if (JSON.stringify(have) !== JSON.stringify(want)) {
      diffs.push(`program ${i + 1}: ${source}\n  want ${want.join(" ")}\n  have ${have.join(" ")}`);
    }
  });
  assert.deepEqual(diffs, []);
  assert.deepEqual(unreadable, [291, 292, 293, 294, 295]);
  assert.equal(compared, 410);
});
