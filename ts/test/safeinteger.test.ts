// HC-21: JavaScript numbers are doubles, so a numeric measure proves termination only when its
// values are proven safe integers (plans/hc-21-js-doubles-termination.md in the brain vault). Each
// attack below passed checkTypeScript() with ok: true and hangs in Node.
import { test } from "node:test";
import assert from "node:assert/strict";
import { checkTypeScript } from "../src/check.ts";

const TOOLS = `
declare function getWeather(args: { city: string }): Promise<{ tempC: number }>;
`;

function check(code: string) {
  return checkTypeScript(code, { toolDeclarations: TOOLS });
}

function assertTerminationRejected(code: string): void {
  const result = check(code);
  assert.equal(result.ok, false, `expected a rejection for: ${code}`);
  assert.ok(
    result.violations.some((v) => /loop|recurs|terminat|decreasing|base-case/i.test(v.kind)),
    `expected a termination violation, got ${JSON.stringify(result.violations)}`,
  );
}

function assertClean(code: string): void {
  const result = check(code);
  assert.deepEqual(result.violations, [], code);
  assert.equal(result.ok, true);
}

const ATTACKS: Record<string, string> = {
  "a counter that starts at 2^53, where i + 1 === i":
    `for (let i = 9007199254740992; i < 9007199254741002; i++) {}`,
  "a countdown by 1 from 1e16, below one ulp": `let i = 1e16; while (i > 0) { i--; }`,
  "a countdown by 1 from 1e300": `let i = 1e300; while (i > 0) { i -= 1; }`,
  "a step of 1e-30, which stalls below one ulp": `for (let i = 0; i < 1; i += 1e-30) {}`,
  "an Infinity bound through a number parameter":
    `function f(n: number): void { for (let i = 0; i < n; i++) {} } f(1 / 0);`,
  "a recursion on a number parameter called with NaN":
    `function count(n: number): number { if (n <= 0) return 0; return count(n - 1); } count(NaN);`,
  "a recursion whose step is below one ulp":
    `function f(n: number): number { if (n <= 0) return 0; return f(n - 1e-17); } f(10);`,
  "a bound returned by a tool": `
    async function main(): Promise<number> {
      const { tempC } = await getWeather({ city: "Hobart" });
      let k = 0;
      for (let i = 0; i < tempC; i++) { k = k + 1; }
      return k;
    }`,
  "a start returned by a tool": `
    async function main(): Promise<number> {
      const { tempC } = await getWeather({ city: "Hobart" });
      let k = 0;
      for (let i = tempC; i > 0; i--) { k = k + 1; }
      return k;
    }`,
};

for (const [name, code] of Object.entries(ATTACKS)) {
  test(`HC-21 attack is rejected: ${name}`, () => assertTerminationRejected(code));
}

test("HC-21 rejection names the Number.isSafeInteger guard to add", () => {
  const result = check(`function f(n: number): void { for (let i = 0; i < n; i++) {} }`);
  assert.equal(result.ok, false);
  assert.ok(
    result.violations.some((v) => v.message.includes("Number.isSafeInteger(n)")),
    JSON.stringify(result.violations),
  );
});

test("HC-21 keeps a counter up to an array length", () => {
  assertClean(`const xs = [1, 2, 3]; let t = 0; for (let i = 0; i < xs.length; i++) { t += xs[i]; }`);
});

test("HC-21 keeps a countdown from a literal", () => {
  assertClean(`let k = 0; for (let i = 10; i > 0; i--) { k = k + 1; }`);
});

test("HC-21 keeps a loop over a number parameter behind a Number.isSafeInteger return", () => {
  assertClean(`
    function f(n: number): number {
      if (!Number.isSafeInteger(n)) return 0;
      let k = 0;
      for (let i = 0; i < n; i++) { k = k + 1; }
      return k;
    }`);
});

test("HC-21 keeps a loop over a number parameter inside a Number.isSafeInteger if", () => {
  assertClean(`
    function f(n: number): number {
      let k = 0;
      if (Number.isSafeInteger(n)) { for (let i = n; i > 0; i--) { k = k + 1; } }
      return k;
    }`);
});

test("HC-21 keeps a guarded recursion on a number parameter", () => {
  assertClean(`
    function count(n: number): number {
      if (!Number.isSafeInteger(n)) return 0;
      if (n <= 0) return 0;
      return count(n - 1);
    }`);
});

test("HC-21 recursion rejection names the Number.isSafeInteger guard to add", () => {
  const result = check(`function count(n: number): number { if (n <= 0) return 0; return count(n - 1); }`);
  assert.equal(result.ok, false);
  assert.ok(
    result.violations.some((v) => v.message.includes("Number.isSafeInteger(n)")),
    JSON.stringify(result.violations),
  );
});

test("HC-21 keeps a nested loop bounded by an outer loop variable", () => {
  assertClean(`
    const xs = [1, 2, 3];
    let k = 0;
    for (let i = 0; i < xs.length; i++) { for (let j = 0; j < i; j++) { k = k + 1; } }`);
});

test("HC-21 keeps a countdown from a const literal", () => {
  assertClean(`const n = 10; let k = 0; for (let i = n; i > 0; i--) { k = k + 1; }`);
});

test("HC-21 keeps a while countdown from a let literal", () => {
  assertClean(`let k = 3; while (k > 0) { k = k - 1; }`);
});

test("HC-21 rejects a second while loop that counts on from a huge bound", () => {
  assertTerminationRejected(`
    let i = 0;
    while (i < 9007199254740991) { i += 4294967296; }
    while (i > 0) { i--; }`);
});

test("HC-21 rejects a while countdown over a number parameter", () => {
  assertTerminationRejected(`function f(k: number): void { while (k > 0) { k = k - 1; } } f(Infinity);`);
});

test("HC-21 rejects a while countdown over a name reassigned to a huge value", () => {
  assertTerminationRejected(`let i = 3; i = 1e300; while (i > 0) { i = i - 1; }`);
});

// Review 1 of PR #765: a guard must not outlive a write to its name, and a do-form's own variable
// shadows an outer guard inside its bound.
const REVIEW_ATTACKS: Record<string, string> = {
  "a guarded parameter reassigned to 1e300":
    `function f(n: number): number { if (!Number.isSafeInteger(n)) return 0; n = 1e300; let k = 0; for (let i = n; i > 0; i--) { k = k + 1; } return k; }`,
  "a guarded parameter reassigned by a closure":
    `function f(n: number): number { if (!Number.isSafeInteger(n)) return 0; const g = (): void => { n = 1e300; }; g(); let k = 0; for (let i = n; i > 0; i--) { k = k + 1; } return k; }`,
  "a guarded parameter reassigned inside the guard":
    `function f(n: number): number { let k = 0; if (Number.isSafeInteger(n)) { n = 1e300; for (let i = n; i > 0; i--) { k = k + 1; } } return k; }`,
  "a guarded parameter reassigned before a while":
    `function f(n: number): number { if (!Number.isSafeInteger(n)) return 0; n = 1e300; while (n > 0) { n = n - 1; } return n; }`,
  "a loop variable that shadows a guarded name in the bound":
    `function f(n: number): number { if (!Number.isSafeInteger(n)) return 0; let k = 0; for (let i = 9007199254740991, n = Infinity; i < n; i++) { k = k + 1; } return k; }`,
};

for (const [name, code] of Object.entries(REVIEW_ATTACKS)) {
  test(`HC-21 review attack is rejected: ${name}`, () => assertTerminationRejected(code));
}

test("HC-21 proof time stays flat on deeply nested loops", () => {
  let body = "k = k + 1;";
  for (let d = 15; d >= 1; d--) {
    const bound = d === 1 ? "xs.length" : `i${d - 1}`;
    body = `for (let i${d} = 0; i${d} < ${bound}; i${d}++) { ${body} } for (let j${d} = 0; j${d} < ${bound}; j${d}++) { k = k + 1; }`;
  }
  const started = Date.now();
  assertClean(`const xs = [1, 2]; let k = 0; ${body}`);
  assert.ok(Date.now() - started < 3000, `took ${Date.now() - started}ms`);
});

test("HC-21 proof time stays flat when sibling loops reuse a name", () => {
  // Review 2: each binding of a reused name re-proved its bound, doubling the work per level.
  let body = "k = k + 1;";
  for (let d = 20; d >= 1; d--) {
    const bound = d === 1 ? "xs.length" : `v${d - 1}`;
    body = `for (let v${d} = 0; v${d} < ${bound}; v${d}++) { ${body} } for (let v${d} = 0; v${d} < ${bound}; v${d}++) { k = k + 1; }`;
  }
  const started = Date.now();
  assertClean(`const xs = [1, 2]; let k = 0; ${body}`);
  assert.ok(Date.now() - started < 3000, `took ${Date.now() - started}ms`);
});
