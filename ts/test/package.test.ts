// The git-URL install contract: what an app gets from
// `npm install github:Chaos-AI-Projects/scheme-harness-checker#<tag>`.
import { test } from "node:test";
import assert from "node:assert/strict";
import { existsSync, readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("../../", import.meta.url));
const pkg = JSON.parse(readFileSync(root + "package.json", "utf8"));

// ts/dist/x.js is built from ts/src/x.ts; the build keeps the tree, so data/ resolves the same.
function source(distPath: string): string {
  const m = /^\.?\/?ts\/dist\/(.+)\.(js|d\.ts)$/.exec(distPath);
  assert.ok(m, `${distPath} is not under ts/dist`);
  return root + "ts/src/" + m[1] + ".ts";
}

test("the package is private, so npm publish fails", () => {
  assert.equal(pkg.private, true);
});

test("every export and the bin point into ts/dist at a real source file", () => {
  const targets: string[] = [];
  for (const entry of Object.values(pkg.exports) as Record<string, string>[]) {
    targets.push(entry.types, entry.default);
  }
  targets.push(...Object.values(pkg.bin) as string[]);
  for (const t of targets) assert.ok(existsSync(source(t)), `no source for ${t}`);
  assert.deepEqual(Object.keys(pkg.exports).sort(), [".", "./ai-sdk"]);
  assert.deepEqual(Object.keys(pkg.bin), ["harness-checker-ts"]);
});

test("prepare builds ts/dist, and the packed files include it and the TypeScript whitelist", () => {
  assert.match(pkg.scripts.prepare, /tsconfig\.build\.json/);
  assert.ok(pkg.files.includes("ts/dist"));
  assert.ok(pkg.files.includes("data/ts-safe.d.ts"));
});

test("the root entry does not import ai, which is an optional peer", () => {
  const index = readFileSync(root + "ts/src/index.ts", "utf8");
  assert.doesNotMatch(index, /from "(ai|\.\/ai-sdk\.ts)"/);
  assert.equal(pkg.peerDependenciesMeta.ai.optional, true);
});

test("the cli starts with a node shebang so npm can link it as a bin", () => {
  assert.match(readFileSync(root + "ts/src/cli.ts", "utf8"), /^#!\/usr\/bin\/env node\n/);
});
