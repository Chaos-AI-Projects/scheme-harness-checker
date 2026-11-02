// The halting check (plans/hc-12-typescript-checker.md in the brain vault, Test plan): every program
// in corpus/accepted/ must pass the checker and then finish in runProgram() under its default time
// budget. It is the empirical check that the lowering hid no loop from the termination proof.
//
// The corpus holds the accepted programs of check.test.ts and safeinteger.test.ts, one per file, each
// headed by the test it came from. A program that only defined a function gained a call to it.

import { test } from "node:test";
import assert from "node:assert/strict";
import { readdirSync, readFileSync } from "node:fs";
import { checkTypeScript } from "../src/check.ts";
import { runProgram } from "../src/run.ts";

const TOOLS = `
declare function getWeather(args: { city: string }): Promise<{ tempC: number }>;
`;
const tools = { getWeather: async () => ({ tempC: 30 }) };

const dir = new URL("./corpus/accepted/", import.meta.url);
const files = readdirSync(dir).filter((f) => f.endsWith(".ts")).sort();

test("the accepted corpus is not empty", () => {
  assert.ok(files.length >= 30, `found ${files.length} programs`);
});

for (const file of files) {
  test(`halting check: ${file}`, async () => {
    const code = readFileSync(new URL(file, dir), "utf8");
    const checked = checkTypeScript(code, { toolDeclarations: TOOLS });
    assert.deepEqual(checked.violations, [], `${file} is no longer accepted`);
    const run = await runProgram(code, { tools });
    assert.equal(run.ok, true, run.ok ? "" : `${file}: ${run.error}`);
  });
}
