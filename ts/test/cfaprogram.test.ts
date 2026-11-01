// Phase 2b of termination.ss (HC-17): cfaAnalyzeProgram against termination.ss's cfa-analyze-program
// over every program test-termination.ss checks. The fixtures are Chez's output, regenerated with
// test/differential/regen-phase2b.sh; a line of the oracle is (rewritten violations), or (skipped rc)
// when Chez could not finish that program under the memory cap. Programs written with datum labels
// (#0=) are left to the driver's differential: the TS reader refuses them, so they never reach 2b.

import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { readAll, readOne, sym, write, type Datum } from "../src/sexp.ts";
import { cfaAnalyzeProgram } from "../src/termination/cfaprogram.ts";

const fixture = (name: string): string[] =>
  readFileSync(new URL(`./differential/${name}`, import.meta.url), "utf8").split("\n").filter((l) => l !== "");

const corpus = fixture("phase2b.corpus.txt");
const oracle = fixture("phase2b.oracle.txt");

test("the phase2b fixtures line up one oracle row per program", () => {
  assert.equal(oracle.length, corpus.length);
});

test("cfaAnalyzeProgram agrees with cfa-analyze-program over the corpus", () => {
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
    const expected = readOne(oracle[i]!) as Datum[];
    const got = cfaAnalyzeProgram(exprs);
    // An anonymous-cycle violation names the first in-cycle edge, and the Scheme's edge order follows
    // its call-site order, which follows Chez's unspecified `map` order (cfa.ts header). The site is
    // compared only as "some site": kind, owner and reason must still agree.
    const violations = (vs: readonly Datum[]) =>
      vs
        .map((v) => {
          const [kind, fn, reason] = v as Datum[];
          const anon = typeof reason === "string" && reason.startsWith("anonymous lambda recursion");
          return write(anon ? [kind!, fn!, reason!, sym("<cycle-site>")] : v);
        })
        .sort();
    if (expected[0] === sym("skipped") || expected[0] === sym("error")) {
      diffs.push(`program ${i + 1}: Chez gave ${oracle[i]} on a program the TS reader accepts`);
      return;
    }
    const want = { rewritten: write(expected[0]!), violations: violations(expected[1] as Datum[]) };
    const have = {
      rewritten: write([...got.rewritten]),
      violations: violations(got.violations.map((v) => [sym(v.kind), v.function ?? false, v.reason, v.expr])),
    };
    compared++;
    try {
      assert.deepEqual(have, want);
    } catch {
      diffs.push(`program ${i + 1}: ${source}\n  want ${JSON.stringify(want)}\n  have ${JSON.stringify(have)}`);
    }
  });
  assert.deepEqual(diffs, []);
  // The five datum-label programs, one of them the cyclic (+ 1 #0#) Chez cannot analyse under the cap.
  assert.deepEqual(unreadable, [291, 292, 293, 294, 295]);
  assert.equal(compared, corpus.length - unreadable.length);
});

test("a dotted cond => clause synthesizes the call from its test, as cfa-analyze-program does", () => {
  // Chez: (((define (f x) (cond (begin (x => f . 0) (f x))))) ()). Indexing the Dotted clause gave
  // (f undefined), and write() threw.
  const got = cfaAnalyzeProgram(readAll("(define (f x) (cond (x => f . 0)))"));
  assert.equal(write([...got.rewritten]), "((define (f x) (cond (begin (x => f . 0) (f x)))))");
  assert.deepEqual(got.violations, []);
});
