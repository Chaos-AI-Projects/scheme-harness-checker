import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

const CLI = fileURLToPath(new URL("../src/cli.ts", import.meta.url));
const dir = mkdtempSync(join(tmpdir(), "hc-cli-"));

function file(name: string, text: string): string {
  const path = join(dir, name);
  writeFileSync(path, text);
  return path;
}

function run(args: string[], input?: string) {
  const r = spawnSync(process.execPath, [CLI, ...args], { encoding: "utf8", input });
  return { status: r.status, stdout: r.stdout, stderr: r.stderr };
}

const CLEAN = `
async function main(): Promise<number> {
  const w = await getWeather({ city: "Sydney" });
  return w.tempC;
}
main();
`;

const SCHEMAS = JSON.stringify({
  getWeather: {
    description: "Current weather for a city",
    inputSchema: { type: "object", properties: { city: { type: "string" } }, required: ["city"] },
    outputSchema: { type: "object", properties: { tempC: { type: "number" } }, required: ["tempC"] },
  },
});

test("a clean program exits 0 and says OK", () => {
  const r = run(["--tool-schemas", file("tools.json", SCHEMAS), file("clean.ts", CLEAN)]);
  assert.equal(r.status, 0, r.stderr);
  assert.match(r.stdout, /^OK: No violations found\.$/m);
});

test("violations exit 1 with one VIOLATION line each and a count", () => {
  const r = run([file("bad.ts", "eval('1');\nfetch('x');\n")]);
  assert.equal(r.status, 1, r.stderr);
  const lines = r.stdout.split("\n").filter((l) => l.startsWith("VIOLATION: "));
  assert.ok(lines.length >= 2, r.stdout);
  assert.match(r.stdout, /^VIOLATION: line 1:1 not-whitelisted: /m);
  assert.match(r.stdout, new RegExp(`^${lines.length} violation\\(s\\) total\\.$`, "m"));
});

test("a tool called without --tool-schemas is not whitelisted", () => {
  const r = run([file("clean2.ts", CLEAN)]);
  assert.equal(r.status, 1);
  assert.match(r.stdout, /not-whitelisted/);
});

test("- reads the program from stdin", () => {
  const r = run(["--tool-schemas", file("tools2.json", SCHEMAS), "-"], CLEAN);
  assert.equal(r.status, 0, r.stderr);
});

test("usage errors exit 2 and print usage to stderr", () => {
  for (const args of [[], ["a.ts", "b.ts"], ["--tool-schemas"], ["--bogus", "a.ts"]]) {
    const r = run(args);
    assert.equal(r.status, 2, `args ${JSON.stringify(args)}: ${r.stdout}`);
    assert.match(r.stderr, /usage: harness-checker-ts/i);
  }
});

test("an unreadable file or bad schema JSON exits 2, not 1", () => {
  assert.equal(run([join(dir, "missing.ts")]).status, 2);
  const r = run(["--tool-schemas", file("bad.json", "{not json"), file("clean3.ts", CLEAN)]);
  assert.equal(r.status, 2);
  assert.match(r.stderr, /harness-checker-ts: /);
});

test("tool declarations that do not compile exit 2, not 1", () => {
  const schemas = file("clash.json", JSON.stringify({ Promise: { inputSchema: { type: "object" } } }));
  const r = run(["--tool-schemas", schemas, file("clean4.ts", CLEAN)]);
  assert.equal(r.status, 2, r.stdout + r.stderr);
  assert.match(r.stderr, /^harness-checker-ts: .*do not compile/m);
});

test("--help prints usage and exits 0", () => {
  const r = run(["--help"]);
  assert.equal(r.status, 0);
  assert.match(r.stdout, /usage: harness-checker-ts/i);
});
