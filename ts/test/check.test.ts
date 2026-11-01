import { test } from "node:test";
import assert from "node:assert/strict";
import { checkTypeScript } from "../src/check.ts";

const TOOLS = `
declare function getWeather(args: { city: string }): Promise<{ tempC: number }>;
`;

function kinds(code: string, toolDeclarations = TOOLS): string[] {
  return checkTypeScript(code, { toolDeclarations }).violations.map((v) => v.kind);
}

function assertClean(code: string): void {
  const result = checkTypeScript(code, { toolDeclarations: TOOLS });
  assert.deepEqual(result.violations, []);
  assert.equal(result.ok, true);
}

function assertRejected(code: string, kind: string): void {
  const result = checkTypeScript(code, { toolDeclarations: TOOLS });
  assert.equal(result.ok, false, `expected ${kind} for: ${code}`);
  assert.ok(
    result.violations.some((v) => v.kind === kind),
    `expected ${kind}, got ${JSON.stringify(result.violations)}`,
  );
}

test("a program in the subset that calls a tool is accepted", () => {
  assertClean(`
    async function main(): Promise<string> {
      const cities = ["Sydney", "Hobart"];
      const temps: number[] = [];
      for (const city of cities) {
        const { tempC } = await getWeather({ city });
        temps.push(tempC);
      }
      const hot = temps.filter((t) => t > 25).map((t) => t * 2);
      let total = 0;
      for (let i = 0; i < hot.length; i++) {
        total += hot[i];
      }
      const label = total > 0 ? \`hot: \${total}\` : "none";
      console.log(JSON.stringify({ label, max: Math.max(...temps) }));
      return label;
    }
  `);
});

test("the whitelist covers the declared library surface", () => {
  assertClean(`
    const xs = [3, 1, 2];
    const s = "a,b,c";
    const parts = s.split(",").map((p) => p.toUpperCase().trim());
    const sorted = xs.slice().sort((a, b) => a - b);
    const sum = xs.reduce((acc, x) => acc + x, 0);
    const keys = Object.keys({ a: 1 });
    const entries = Object.entries({ a: 1 });
    const parsed: unknown = JSON.parse("{}");
    const n = Number.isInteger(sum) ? Math.floor(sum / 2) : 0;
    const isArr = Array.isArray(parsed);
    const both = Promise.all([getWeather({ city: "x" })]);
    console.log(parts, sorted, keys, entries, n, isArr, both, String(n), s.length);
  `);
});

test("try/catch, switch, while, destructuring and spread are in the subset", () => {
  assertClean(`
    function classify(n: number): string {
      switch (n) {
        case 0: return "zero";
        default: return n < 0 ? "neg" : "pos";
      }
    }
    let k = 3;
    while (k > 0) {
      k = k - 1;
    }
    const [head, ...rest] = [1, 2, 3];
    const obj = { ...{ a: 1 }, b: head ?? 0 };
    try {
      throw "boom";
    } catch (e) {
      console.log(classify(rest.length), obj, e);
    }
  `);
});

test("an undeclared global is a whitelist violation", () => {
  for (const name of ["process.env", "require('fs')", "fetch('x')", "globalThis", "eval('1')",
                      "Function('return 1')", "setTimeout", "Symbol.toPrimitive", "Reflect"]) {
    assertRejected(`const bad = ${name};`, "not-whitelisted");
  }
});

test("an undeclared member is a whitelist violation", () => {
  assertRejected(`const xs = [1]; const c = xs.notAMethod(0, 1);`, "not-whitelisted");
  assertRejected(`const o = { a: 1 }; const c = o.b;`, "not-whitelisted");
  // Builtin members the whitelist leaves out are stopped earlier, by name.
  assertRejected(`const xs = [1]; const c = xs.copyWithin(0, 1);`, "forbidden-member");
  assertRejected(`const f = (x: number) => x; const g = f.call(null, 1);`, "forbidden-member");
});

test("prototype-chain escapes are rejected", () => {
  assertRejected(`const f = () => 1; const F = f.constructor;`, "forbidden-member");
  assertRejected(`const c = [].constructor.constructor("return process")();`, "forbidden-member");
  assertRejected(`const o = {}; const p = o.__proto__;`, "forbidden-member");
  assertRejected(`const o = { __proto__: null };`, "forbidden-member");
  assertRejected(`const o = { a: 1 }; const p = o["constructor"];`, "forbidden-member");
  assertRejected(`const s = "x"; const p = s.prototype;`, "forbidden-member");
});

test("the any type is rejected, written or implicit", () => {
  assertRejected(`const x: any = 1;`, "any-type");
  assertRejected(`function f(x) { return x; }`, "any-type");
  assertRejected(`const xs: Array<any> = [];`, "any-type");
});

test("any laundered through a tool declaration is rejected", () => {
  const tools = `declare function leak(): any;`;
  assert.ok(kinds(`const x = leak(); const y = x.constructor;`, tools).length > 0);
  assert.ok(kinds(`const x = leak(); console.log(x.foo);`, tools).includes("any-type"));
});

test("casts and non-null assertions are rejected, as const is allowed", () => {
  assertRejected(`const x = (1 as unknown) as string;`, "cast");
  assertRejected(`const x = <string>(<unknown>1);`, "cast");
  assertRejected(`const xs = [1]; const y = xs.pop()!;`, "cast");
  assertClean(`const xs = [1, 2] as const; console.log(xs);`);
});

test("ts directive comments are rejected", () => {
  assertRejected(`// @ts-ignore\nconst x: number = "s";`, "ts-directive");
  assertRejected(`/* @ts-expect-error */ const x: number = "s";`, "ts-directive");
  assertRejected(`// @ts-nocheck\nconst x = 1;`, "ts-directive");
  assertRejected(`/// <reference lib="dom" />\nconst x = 1;`, "ts-directive");
  assertRejected(`const x = f(/* @ts-ignore */);\nfunction f() { return 1; }`, "ts-directive");
  assertClean(`const s = "// @ts-ignore is text here"; console.log(s);`);
});

test("computed member access needs a literal or a number key", () => {
  assertClean(`const xs = [1, 2]; const i = 1; console.log(xs[i], xs[0], ({ a: 1 })["a"]);`);
  assertRejected(`const o = { a: 1 }; const k: string = "a"; const v = o[k as "a"];`, "cast");
  assertRejected(`const o: { [k: string]: number } = {}; const k = "a" + "b"; console.log(o[k]);`,
                 "computed-access");
});

test("constructs outside the v1 subset are unsupported syntax", () => {
  const programs = [
    `class A {}`,
    `function f(this: unknown) { return this; }`,
    `function* g() { yield 1; }`,
    `const o = { get x() { return 1; } };`,
    `var x = 1;`,
    `label: for (const x of [1]) { break label; }`,
    `const r = /a+/;`,
    `const t = tag\`x\`; function tag(s: unknown) { return s; }`,
    `const o = { a: 1 }; delete o.a;`,
    `function f() { return arguments; }`,
    `const m = import("fs");`,
    `import fs from "fs";`,
    `export const x = 1;`,
    `declare const process: { env: unknown };`,
    `interface Function { constructor: unknown }`,
    `namespace N {}`,
    `enum E { A }`,
    `const f = function () { return 1; };`,
    `const d = new Date();`,
    `for (const k in { a: 1 }) { console.log(k); }`,
    `async function f() { for await (const x of [1]) { console.log(x); } }`,
    `do { console.log(1); } while (false);`,
    `const x = 1; with (x) {}`,
  ];
  for (const code of programs) {
    assert.ok(kinds(code).includes("unsupported-syntax"),
              `expected unsupported-syntax for: ${code}, got ${JSON.stringify(kinds(code))}`);
  }
});

test("a type error is reported with its position", () => {
  const result = checkTypeScript(`const n: number = "s";`, { toolDeclarations: TOOLS });
  assert.equal(result.ok, false);
  assert.equal(result.violations[0].kind, "type-error");
  assert.equal(result.violations[0].line, 1);
  assert.equal(typeof result.violations[0].message, "string");
});

test("a tool called with the wrong argument type is a type error", () => {
  assertRejected(`const w = getWeather({ town: "x" });`, "type-error");
  assertRejected(`const w = getWeather();`, "type-error");
});

test("a broken tool declaration throws rather than blaming the program", () => {
  assert.throws(() => checkTypeScript(`const x = 1;`, { toolDeclarations: `declare function t(): Nope;` }),
                /tool declarations/);
});

test("checks are independent across calls", () => {
  assertClean(`const a = 1; console.log(a);`);
  assertClean(`const a = 2; console.log(a);`);
});

test("escape probes found while building the gate are rejected", () => {
  assertRejected(`const o: { [k: string]: number } = {}; const k = "constructor"; console.log(o[k]);`,
                 "computed-access");
  assertRejected(`const o = { a: 1 }; console.log(o[\`constructor\`]);`, "forbidden-member");
  assertRejected(`const { constructor: c } = () => 1;`, "forbidden-member");
  assertRejected(`const { constructor } = () => 1;`, "forbidden-member");
  assertRejected(`type G = typeof globalThis;`, "not-whitelisted");
  assertRejected(`const s = Symbol.iterator;`, "not-whitelisted");
  assertRejected(`const p: unknown = JSON.parse("1"); if (typeof p === "function") { p("x"); }`, "any-type");
  assertRejected(`const p: unknown = JSON.parse("1"); if (typeof p === "object" && p) { console.log(p.constructor); }`,
                 "forbidden-member");
  assertRejected(`const x = [1, 2], y = (0, x);`, "unsupported-syntax");
  assertRejected(`const x = "a" in { a: 1 };`, "unsupported-syntax");
});

// Review round 1 on PR #756. Each probe gets Object under a type that lies about it, then reaches
// Function through getOwnPropertyDescriptor. None of them uses as, any or a directive.
const ESC = `
type Esc = {
  getPrototypeOf(o: unknown): unknown;
  getOwnPropertyDescriptor(o: unknown, k: string): { value: (s: string) => () => void };
};
const reach = (e: Esc) => e.getOwnPropertyDescriptor(e.getPrototypeOf(() => 1), "constructor").value("return globalThis")();
`;

test("type lies that reach Function without a cast are rejected", () => {
  const probes = [
    `function isEsc(x: unknown): x is Esc { return true; } const o: unknown = Object; if (isEsc(o)) { reach(o); }`,
    `function a(x: unknown): asserts x is Esc {} const o: unknown = Object; a(o); reach(o);`,
    `const escs: Esc[] = []; const wide: unknown[] = escs; wide.push(Object); reach(escs[0]);`,
    `const h: { v: Esc | null } = { v: null }; const w: { v: unknown } = h; w.v = Object; if (h.v) { reach(h.v); }`,
    `const got: Esc[] = []; const s: { put(x: unknown): void } = { put: (x: Esc) => { got.push(x); } }; s.put(Object); reach(got[0]);`,
    `let O!: Esc; reach(O);`,
  ];
  for (const probe of probes) {
    const result = checkTypeScript(ESC + probe, { toolDeclarations: TOOLS });
    assert.equal(result.ok, false, `expected rejection for: ${probe}`);
  }
});

test("type predicates, asserts and definite assignment are casts", () => {
  assertRejected(`function p(x: unknown): x is number { return true; }`, "cast");
  assertRejected(`function a(x: unknown): asserts x is number {}`, "cast");
  assertRejected(`function a(x: unknown): asserts x {}`, "cast");
  assertRejected(`let n!: number; console.log(n);`, "cast");
});

test("a lib global is usable only as a receiver or a callee", () => {
  assertRejected(`const o = Object;`, "not-whitelisted");
  assertRejected(`const xs = [1]; xs.map(String);`, "not-whitelisted");
  assertRejected(`const f = (x: unknown) => x; f(Math);`, "not-whitelisted");
  assertClean(`const n = Number("1"); const k = Object.keys({ a: n }); console.log(Math.max(n, 2), k);`);
});

test("builtin members outside the whitelist are rejected by name, whatever the type says", () => {
  assertRejected(`type G = { __lookupGetter__(k: string): unknown }; const g: G = { __lookupGetter__: (k: string) => k }; g.__lookupGetter__("x");`,
                 "forbidden-member");
  assertRejected(`const o = { getPrototypeOf: 1 }; console.log(o.getPrototypeOf);`, "forbidden-member");
  assertRejected(`const o = { apply: 1 }; console.log(o["apply"]);`, "forbidden-member");
  assertRejected(`const { getOwnPropertyDescriptor } = { getOwnPropertyDescriptor: 1 };`, "forbidden-member");
  assertRejected(`const { bind: b } = { bind: 1 };`, "forbidden-member");
  for (const name of ["caller", "callee", "arguments"]) {
    assertRejected(`const o = { a: 1 }; console.log(o["${name}"]);`, "forbidden-member");
  }
});

test("a member name declared by a tool is allowed even if a builtin has it", () => {
  const tools = `declare function mail(): Promise<{ from: string; values: number[] }>;`;
  const result = checkTypeScript(
    `async function main() { const m = await mail(); console.log(m.from, m.values); }`,
    { toolDeclarations: tools },
  );
  assert.deepEqual(result.violations, []);
});

test("directives are matched case-insensitively", () => {
  assertRejected(`// @TS-NOCHECK\nconst x: number = "s";`, "ts-directive");
  assertRejected(`//@ts-NoCheck\nconst x: number = "s";`, "ts-directive");
  assertRejected(`// @Ts-Ignore\nconst x: number = "s";`, "ts-directive");
});

test("a program that collides with a lib or tool name is a violation, not a throw", () => {
  for (const code of [`const Math = 1;`, `type Awaited<T> = T;`, `function getWeather() { return 1; }`,
                      `let JSON = 1;`, `function f(Object: number) { return Object; }`]) {
    const result = checkTypeScript(code, { toolDeclarations: TOOLS });
    assert.equal(result.ok, false, `expected rejection for: ${code}`);
  }
});

test("assigning through a lib global is rejected", () => {
  assertRejected(`Math.max = (...v: number[]) => 0;`, "forbidden-member");
  assertRejected(`console.log = (...d: unknown[]) => {};`, "forbidden-member");
  assertRejected(`[Math.max] = [(...v: number[]) => 0];`, "forbidden-member");
});

test("for...of iterates arrays only", () => {
  assertRejected(`for (const c of "abc") { console.log(c); }`, "unsupported-syntax");
  assertClean(`for (const c of ["a", "b"]) { console.log(c); }`);
});

test("a dynamic member key must be a number at run time, not just in its type", () => {
  // A string smuggled into a number[] through covariance reads Array.constructor and then Function.
  assertRejected(`
    const ks: number[] = [];
    const w: (number | string)[] = ks;
    w.push("constructor");
    const arrs: number[][] = [[]];
    console.log(arrs[ks[0]]);
  `, "computed-access");
  assertRejected(`const xs = [1]; function f(i: number) { return xs[i]; }`, "computed-access");
  assertRejected(`const xs = [1]; let i = 0; i = xs.findIndex((x) => x > 0); console.log(xs[i]);`,
                 "computed-access");
  assertRejected(`const xs = [1]; const ks: number[] = []; let i = 0; for (i of ks) {} console.log(xs[i]);`,
                 "computed-access");
  assertRejected(`const xs = [1]; const ks: number[] = []; let i = 0; [i] = ks; console.log(xs[i]);`,
                 "computed-access");
  assertClean(`
    const xs = [1, 2, 3];
    let total = 0;
    for (let i = 0; i < xs.length; i++) { total += xs[i]; }
    for (let j = xs.length - 1; j >= 0; j -= 1) { total += xs[j]; }
    const k = 2;
    console.log(total, xs[xs.length - 1], xs[k], xs[+k], xs[k * 2 - 1]);
  `);
});

// Review round 2 on PR #756: writes the key tracking missed, and builtin reads in assignment patterns.
const LIE = `const ks: number[] = []; const w: (number | string)[] = ks; w.push("constructor");
const fs: ((s: string) => () => string)[][] = [[]];
let i = 0;
`;

test("every way of writing a key variable is tracked", () => {
  for (const write of [`(i) = ks[0];`, `((i)) = ks[0];`, `(i) ||= ks[0];`, `({ i } = { i: ks[0] });`,
                       `for ({ i } of [{ i: ks[0] }]) {}`, `({ a: i } = { a: ks[0] });`,
                       `[[i]] = [[ks[0]]];`, `i ??= ks[0];`]) {
    for (const use of [`fs[i][i]("return 1")();`, `fs?.[i]?.[i]?.("return 1")();`]) {
      const result = checkTypeScript(LIE + write + use, { toolDeclarations: TOOLS });
      assert.ok(result.violations.some((v) => v.kind === "computed-access"),
                `expected computed-access for: ${write} ${use}, got ${JSON.stringify(result.violations)}`);
    }
  }
});

test("builtin member names are reads in an assignment pattern too", () => {
  const pre = `const hs: unknown[] = []; let b: unknown = 0; `;
  assertRejected(pre + `({ bind: b } = { bind: 1 });`, "forbidden-member");
  assertRejected(pre + `[{ call: b }] = [{ call: 1 }];`, "forbidden-member");
  assertRejected(pre + `for ({ hasOwnProperty: b } of [{ hasOwnProperty: 1 }]) {}`, "forbidden-member");
  assertRejected(`let apply: unknown = 0; ({ apply } = { apply: 1 });`, "forbidden-member");
});

test("renamed and nested destructuring is accepted, the property name is not a value", () => {
  assertClean(`async function main(): Promise<number> { const { tempC: t } = await getWeather({ city: "x" }); return t; }`);
  assertClean(`const p = { name: "a" }; const { name: n } = p; console.log(n);`);
  assertClean(`const ps = [{ name: "a" }]; console.log(ps.map(({ name: n }) => n));`);
  assertClean(`const { a: { b } } = { a: { b: 1 } }; console.log(b);`);
});

test("HTML-like comment tokens are rejected, a script parser reads them as comments", () => {
  assertRejected("let y = 5;\nconst b = false <!--y; const t = `\nconsole.log(1);\n//`; console.log(b, t);", "unsupported-syntax");
  assertRejected("let x = 3;\nlet y = 1;\nx\n-->y;\nconsole.log(x);", "unsupported-syntax");
  assertClean("const s = '<!-- -->'; const t = `<!--`; console.log(s, t); // <!-- -->");
});

test("a Math call is a numeric key", () => {
  assertClean(`function median(xs: number[]): number { const s = xs.slice().sort((a, b) => a - b); return s[Math.floor(s.length / 2)]; }`);
});
