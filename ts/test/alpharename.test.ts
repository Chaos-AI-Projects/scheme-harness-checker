// Binding identity of termination.ss (HC-17): alphaRenameDefinitions against alpha-rename-definitions
// over every program test-termination.ss checks. rename.oracle.txt is Chez's output, regenerated with
// test/differential/regen-phase2b.sh; a line is (renamed-program top-env), or (skipped rc).

import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { readAll, readOne, sym, write, Dotted, type Datum } from "../src/sexp.ts";
import { alphaRenameDefinitions } from "../src/termination/alpharename.ts";

const fixture = (name: string): string[] =>
  readFileSync(new URL(`./differential/${name}`, import.meta.url), "utf8").split("\n").filter((l) => l !== "");

const corpus = fixture("phase2b.corpus.txt");
const oracle = fixture("rename.oracle.txt");

const renamed = (source: string) => {
  const { exprs, topEnv } = alphaRenameDefinitions(readAll(source));
  return write([exprs as Datum[], topEnv.map(([k, v]) => new Dotted([k], v))]);
};

test("a local helper sharing a top-level name gets its own", () => {
  assert.equal(
    renamed("(define (f x) x) (define (g y) (define (f z) (f z)) (f y))"),
    "(((define (f x) x) (define (g y) (define (f~1 z) (f~1 z)) (f~1 y))) ())",
  );
});

test("a top-level define shadowing a Chez builtin is renamed, quoted data is not", () => {
  assert.equal(
    renamed("(define (car x) 'car) (car 1)"),
    "(((define (car~1 x) (quote car)) (car~1 1)) ((car . car~1)))",
  );
});

test("a fresh name skips one the program already uses", () => {
  assert.equal(
    renamed("(define (car x) 'car~1) (car 1)"),
    "(((define (car~2 x) (quote car~1)) (car~2 1)) ((car . car~2)))",
  );
});

test("alphaRenameDefinitions agrees with alpha-rename-definitions over the corpus", () => {
  const unreadable: number[] = [];
  const diffs: string[] = [];
  corpus.forEach((line, i) => {
    const source = readOne(line) as string;
    try {
      readAll(source);
    } catch {
      unreadable.push(i + 1);
      return;
    }
    if (oracle[i]!.startsWith("(skipped") || oracle[i] === "(error)") {
      diffs.push(`program ${i + 1}: Chez gave ${oracle[i]} on a program the TS reader accepts`);
      return;
    }
    const want = write(readOne(oracle[i]!));
    const have = renamed(source);
    if (have !== want) diffs.push(`program ${i + 1}: ${source}\n  want ${want}\n  have ${have}`);
  });
  assert.deepEqual(diffs, []);
  assert.deepEqual(unreadable, [291, 292, 293, 294, 295]);
});
