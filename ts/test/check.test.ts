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

test("termination runs on the lowered program: a recursion that never shrinks is rejected", () => {
  const result = checkTypeScript(`
    function count(n: number): number {
      if (n === 0) return 0;
      return count(n + 1);
    }
  `, { toolDeclarations: TOOLS });
  assert.equal(result.ok, false);
  const v = result.violations.find((x) => x.kind === "no-decreasing-arg");
  assert.ok(v, `expected no-decreasing-arg, got ${JSON.stringify(result.violations)}`);
  assert.match(v.message, /\bcount\b/);
  assert.doesNotMatch(v.message, /js\./);
  assert.equal(v.line, 2);
});

test("termination runs on the lowered program: a shrinking recursion is accepted", () => {
  assertClean(`
    function count(n: number): number {
      if (!Number.isSafeInteger(n)) return 0;
      if (n <= 0) return 0;
      return 1 + count(n - 1);
    }
    console.log(count(3));
  `);
});

// HC-22: naming the smaller value before recursing is the common TypeScript shape.
test("a const naming the decreasing argument is seen through", () => {
  assertClean(`
    function count(n: number): number {
      if (!Number.isSafeInteger(n)) return 0;
      if (n <= 0) return 0;
      const m = n - 1;
      return 1 + count(m);
    }
    function down(n: number): number {
      if (!Number.isSafeInteger(n)) return 0;
      if (n <= 0) return 0;
      const k = n - 1;
      const m = k;
      return down(m);
    }
    console.log(count(3), down(2));
  `);
});

test("only a pure const initializer is seen through", () => {
  // A let can be reassigned before the call.
  assertRejected(`
    function g(n: number): number {
      if (!Number.isSafeInteger(n)) return 0;
      if (n <= 0) return 0;
      let m = n - 1;
      m = n;
      return g(m);
    }
  `, "no-decreasing-arg");
});

test("a chain of impure consts is lowered once per const, not once per path (HC-22 review)", () => {
  const chain = Array.from({ length: 12 }, (_, k) => `const c${k + 1} = h(c${k}, c${k});`).join("\n");
  const started = Date.now();
  checkTypeScript(`
    const h = (a: number, b: number): number => a;
    function f(n: number): number {
      const c0 = n;
      ${chain}
      return h(c12, 0);
    }
  `, { toolDeclarations: TOOLS });
  assert.ok(Date.now() - started < 5000, `took ${Date.now() - started}ms`);
});

test("a chain of pure consts used twice each is lowered once per const (HC-22 re-review)", () => {
  // c22 is no shape size-change reads, so f(c22) keeps its name. Lowered afresh at every use instead,
  // the chain doubles 22 times and the lowering grows past MAX_NODES.
  const chain = Array.from({ length: 22 }, (_, k) => `const c${k + 1} = c${k} * c${k};`).join("\n");
  assertRejected(`
    function f(n: number): number {
      if (!Number.isSafeInteger(n)) return 0;
      if (n <= 0) return 0;
      const c0 = n;
      ${chain}
      return f(c22);
    }
  `, "no-decreasing-arg");
});

test("a const is seen through only into a call that can recurse back (HC-22 review 3)", () => {
  // Each fall-through if copies what follows it, so inlining m into every g(m) multiplies the
  // lowering. g never calls f, so size-change reads nothing from these arguments.
  const ifs = Array.from({ length: 8 }, (_, k) => `if (n === ${k}) { if (n > 100) return ${k}; }`).join("\n");
  const uses = Array.from({ length: 15 }, () => "g(m)").join(" + ");
  assertClean(`
    function g(a: number): number { return a; }
    function f(n: number): number {
      const m = n - 1;
      ${ifs}
      return ${uses};
    }
    console.log(f(3));
  `);
});

test("a chain of const aliases is followed only MAX_LINKS deep (HC-22)", () => {
  // Followed all the way, f(c600) would read as f(n - 1) and pass. Capped, it keeps its name.
  const chain = Array.from({ length: 600 }, (_, k) => `const c${k + 1} = c${k};`).join("\n");
  assertRejected(`
    function f(n: number): number {
      if (!Number.isSafeInteger(n)) return 0;
      if (n <= 0) return 0;
      const c0 = n - 1;
      ${chain}
      return f(c600);
    }
  `, "no-decreasing-arg");
});

test("a const is seen through into a mutually recursive call (HC-22)", () => {
  assertClean(`
    function even(n: number): boolean {
      if (!Number.isSafeInteger(n)) return false;
      if (n <= 0) return true;
      const m = n - 1;
      return odd(m);
    }
    function odd(n: number): boolean {
      if (!Number.isSafeInteger(n)) return false;
      if (n <= 0) return false;
      const m = n - 1;
      return even(m);
    }
    console.log(even(4));
  `);
});

test("a parameter assigned after the const still gives no arc", () => {
  assertRejected(`
    function f(n: number): number {
      if (!Number.isSafeInteger(n)) return 0;
      if (n <= 0) return 0;
      const m = n - 1;
      n = n + 5;
      return f(m);
    }
  `, "no-decreasing-arg");
});

test("a const is not seen through where its names are shadowed", () => {
  // Inside g, n is g's own parameter, so g(m) read as g(n - 1) would shrink it; m is h's n - 1, so
  // h(2) runs g(1) forever (HC-22 review 5).
  assertRejected(`
    function h(n: number): number {
      if (!Number.isSafeInteger(n)) return 0;
      if (n <= 0) return 0;
      const m = n - 1;
      const g = (n: number): number => {
        if (!Number.isSafeInteger(n)) return 0;
        if (n <= 0) return 0;
        return g(m);
      };
      return g(n + 5);
    }
  `, "no-decreasing-arg");
});

test("a construct the lowering does not know is unsupported syntax", () => {
  assertRejected(`const xs = [3, 1]; xs.unshift(0);`, "unsupported-syntax");
});

// Review of PR #760: each program below passed with ok: true and does not terminate in node.
test("string + and string comparisons are not read as numeric progress", () => {
  assert.equal(checkTypeScript(`for (let s = "a"; s < "b"; s += 1) {}`, { toolDeclarations: TOOLS }).ok, false);
  assert.equal(checkTypeScript(`let s = "a"; while (s < "b") { s += 1; }`, { toolDeclarations: TOOLS }).ok, false);
  assert.equal(checkTypeScript(`
    async function f(s: string): Promise<number> { if (s >= "b") return 0; await 0; return f(s + 1); }
    f("a");
  `, { toolDeclarations: TOOLS }).ok, false);
});

test("a while whose variable a closure assigns is rejected", () => {
  assert.equal(checkTypeScript(`
    function g(): number {
      let i = 0;
      const reset = (): void => { i = 0; };
      while (i < 10) { reset(); i++; }
      return i;
    }
  `, { toolDeclarations: TOOLS }).ok, false);
  assert.equal(checkTypeScript(`
    let i = 0;
    const back = (): void => { i = i - 1; };
    while (i < 10) { back(); i++; }
  `, { toolDeclarations: TOOLS }).ok, false);
});

test("a pushed array returned from a nested function is an alias", () => {
  assert.equal(checkTypeScript(`
    function g(): number {
      const a = [1];
      const get = (): number[] => { return a; };
      for (const x of get()) { a.push(x); }
      return 0;
    }
  `, { toolDeclarations: TOOLS }).ok, false);
});

test("a for whose counter a closure assigns is rejected", () => {
  assert.equal(checkTypeScript(`
    for (let i = 0; i < 10; i++) { const reset = (): void => { i = 0; }; reset(); }
  `, { toolDeclarations: TOOLS }).ok, false);
});

// Review round 2 of PR #760: a type can say number while the value is a string, and then + concatenates.
test("+ is numeric progress only when both operands are numbers by construction", () => {
  const poisoned = (loop: string) => `
    function main(): number {
      let x: number | string = 0;
      const poison = () => { x = "-1"; };
      poison();
      let k = 0;
      ${loop}
      return k;
    }`;
  assert.equal(checkTypeScript(poisoned(`for (let i = x; i < 10; i += 1) { k = k + 1; }`), { toolDeclarations: TOOLS }).ok, false);
  assert.equal(checkTypeScript(poisoned(`let i = x; while (i < 10) { i += 1; }`), { toolDeclarations: TOOLS }).ok, false);
  assert.equal(checkTypeScript(`
    function count(x: number): number { let k = 0; for (let i = x; i < 10; i += 1) { k = k + 1; } return k; }
    function main(): number { const b: { f(x: string | number): number } = { f: count }; const f = b.f; return f("-1"); }
  `, { toolDeclarations: TOOLS }).ok, false);
  assert.equal(checkTypeScript(`
    function up(i: number): number { if (i >= 10) return 0; return up(i + 1); }
  `, { toolDeclarations: TOOLS }).ok, false);
  // ++ always converts to a number, but since HC-21 a start of x, assigned by a closure, is not a
  // proven safe integer either, so the ++ loop is rejected too.
  assert.equal(checkTypeScript(poisoned(`for (let i = x; i < 10; i++) { k = k + 1; }`), { toolDeclarations: TOOLS }).ok, false);
  assert.equal(checkTypeScript(`let k = 0; for (let i = 0; i < 10; i += 2) { k = k + 1; }`, { toolDeclarations: TOOLS }).ok, true);
});

// Review round 3 of PR #760: a narrowing kept across a call lets a record pass as an array, and
// then .map is the record's own function, not the Scheme HOF the lowering wrote.
test("an object literal may not define a member the lowering reads as an array's", () => {
  assert.equal(checkTypeScript(`
    function go(cb: (v: number) => number): number[] { return lie().map(cb); }
    function lie(): number[] {
      let z: number[] | { tag: number } = [1];
      const p = () => { z = rec; };
      p();
      return z;
    }
    const rec = { tag: 1, map: (cb: (v: number) => number): number[] => go(cb) };
  `, { toolDeclarations: TOOLS }).ok, false);
  for (const key of ["map", "slice", "length", "join", "sort", "push", '"0"']) {
    const r = checkTypeScript(`const o = { ${key}: 1 };`, { toolDeclarations: TOOLS });
    assert.equal(r.ok, false, key);
    assert.equal(r.violations[0].kind, "unsupported-syntax", key);
  }
});

// Review round 4 of PR #760: a callback's type can claim one parameter while the function takes the
// array as its third, so the arity a HOF lowering needs comes from the function's own text.
test("a HOF callback's arity is read from its definition, not its type", () => {
  assert.equal(checkTypeScript(`
    async function main(): Promise<number> {
      const a: number[] = [1];
      let holder: number[] = [];
      let f: ((v: number) => void) | ((v: number, i: number, arr: number[]) => number) = (v: number): void => {};
      const set = (): void => { f = (v: number, i: number, arr: number[]): number => { holder = arr; return 0; }; };
      set();
      a.forEach(f);
      let n = 0;
      for (const x of holder) { a.push(x); }
      return n;
    }
  `, { toolDeclarations: TOOLS }).ok, false);
  // An arrow at the call, a const bound to one, and a function declaration all keep their arity.
  assert.equal(checkTypeScript(`
    function inc(x: number): number { return x - 1; }
    const pos = (x: number): boolean => x > 0;
    const xs = [1, 2];
    const ys = xs.map(inc).filter(pos).map((x: number) => x * 2);
  `, { toolDeclarations: TOOLS }).ok, true);
});

// Review round 5 of PR #760: on a shorthand property the checker names the property, not the
// variable, so { a } must still count as a use of a pushed array.
test("a shorthand property is an alias of a pushed array", () => {
  assert.equal(checkTypeScript(`
    function main(): number {
      const a: number[] = [1];
      const o = { a };
      for (const x of o.a) { a.push(x); }
      return a.length;
    }
  `, { toolDeclarations: TOOLS }).ok, false);
});

// Review round 6 of PR #760. JS [].slice(1) is [], a fixed point, so slice(1) and an array rest are
// no decrease. And a method signature is bivariant, which lets a string reach an array parameter,
// so [0] on it is no decrease either.
test("slice(1) and an array rest are not a decrease, [] is their fixed point", () => {
  assert.equal(checkTypeScript(`
    function f(xs: number[], n: number): number {
      if (n < 0) return 0;
      return f(xs.slice(1), n + 1);
    }
    f([], 0);
  `, { toolDeclarations: TOOLS }).ok, false);
  assert.equal(checkTypeScript(`
    function g(xs: number[], n: number): number {
      if (n < 0) return 0;
      const [, ...t] = xs;
      return g(t, n + 1);
    }
    g([], 0);
  `, { toolDeclarations: TOOLS }).ok, false);
});

test("a method signature is unsupported, its parameters are bivariant", () => {
  assertRejected(`
    function f(x: unknown[], n: number): number {
      if (n < 0) return 0;
      const o: { m(x: unknown, n: number): number } = { m: f };
      const m = o.m;
      return m(x[0], n + 1);
    }
    f(["a"], 0);
  `, "unsupported-syntax");
});

// Review round 7 of PR #760. A type can still say array while the value is a string, through an
// optional property, an index signature, {} or a narrowing kept across a call, and "a"[0] is "a".
// So an element read is no decrease, whatever the type says.
test("an element read is not a decrease, a string can pass as an array", () => {
  for (const lie of [
    `const o1 = { a: "str" }; const o2: {} = o1; const o3: { [k: string]: never[] } = o2; f(o3.a, 0);`,
    `let v: string | never[] = []; function g(): number { v = "a"; return 0; } if (Array.isArray(v)) { g(); f(v, 0); }`,
  ]) {
    assert.equal(checkTypeScript(`
      function f(x: never[], n: number): number {
        if (n < 0) return 0;
        return f(x[0], n + 1);
      }
      ${lie}
    `, { toolDeclarations: TOOLS }).ok, false, lie);
  }
  assert.equal(checkTypeScript(`
    function g(x: never[], n: number): number {
      if (n < 0) return 0;
      const [h] = x;
      return g(h, n + 1);
    }
    const o1 = { a: "str" }; const o2: {} = o1; const o3: { [k: string]: never[] } = o2; g(o3.a, 0);
  `, { toolDeclarations: TOOLS }).ok, false);
});

// HC-26: every const lowers to one more nested let*, and the checker's walkers recurse over that
// nesting. 1,900 links overflowed in the termination pass and 5,000 in lowering; either is a
// violation, never a thrown RangeError.
test("a program nested deeper than the checker's stack is rejected, not thrown", () => {
  for (const n of [1900, 5000]) {
    const chain = Array.from({ length: n }, (_, k) => `const c${k + 1} = c${k};`).join("\n");
    const code = `function f(n: number): number {\n  if (n <= 0) return 0;\n  const c0 = n - 1;\n${chain}\n  return f(c${n});\n}`;
    assertRejected(code, "unsupported-syntax");
  }
});

// HC-28: typeof alone leaves a JSON value at `object`, which has no fields. Object.entries and
// Object.values over `object` give its values as `unknown`, which typeof then narrows.
const JSON_TOOL_RESULT = `
  async function main(): Promise<number> {
    const raw: unknown = JSON.parse('{"a": 1, "b": "x", "c": 2}');
    let total = 0;
    if (typeof raw === "object" && raw !== null) {
      for (const entry of Object.entries(raw)) {
        const [key, value] = entry;
        if (typeof value === "number" && key !== "skip") {
          total += value;
        }
      }
      for (const value of Object.values(raw)) {
        if (typeof value === "string") {
          console.log(value.toUpperCase());
        }
      }
    }
    return total;
  }
  main();
`;

test("a JSON tool result is read by narrowing with typeof and iterating entries and values", () => {
  assertClean(JSON_TOOL_RESULT);
});

test("Object.values over a record keeps its value type", () => {
  assertClean(`const o: { [k: string]: number } = { a: 1 }; let s = 0; for (const v of Object.values(o)) { s += v; } console.log(s);`);
});

test("typeof narrowing opens no escape and hides no loop", () => {
  assertRejected(`const p: unknown = JSON.parse("{}");
    if (typeof p === "object" && p !== null) { for (const v of Object.values(p)) { if (typeof v === "function") { v(); } } }`,
    "any-type");
  const loop = checkTypeScript(`function f(x: unknown): number { if (typeof x === "number") { return f(x); } return 0; } f(1);`,
    { toolDeclarations: TOOLS });
  assert.equal(loop.ok, false);
  assert.ok(loop.violations.every((v) => v.kind !== "unsupported-syntax"), JSON.stringify(loop.violations));
});

test("a call inside a typeof operand is still analysed", () => {
  assertRejected(`function f(): number { return typeof f() === "number" ? 1 : 0; } f();`, "no-decreasing-arg");
});

// HC-29: const and let inside if, try, catch, a nested block and a case clause. Each gets a fresh IR
// name, so a later statement that names an outer binding is not captured by the block's.
test("const and let inside if, try, catch, a block and a case are accepted", () => {
  assertClean(`
    async function main(): Promise<number> {
      let total = 0;
      const raw: unknown = JSON.parse("[1, 2]");
      if (Array.isArray(raw)) { const n = raw.length; total += n; } else { let m = 1; m = m + 1; total += m; }
      try { const w = await getWeather({ city: "Sydney" }); total += w.tempC; } catch (e) { const msg = String(e); console.log(msg); }
      { const inner = total * 2; console.log(inner); }
      switch (total) { case 0: const z = 1; return z; default: const d = total; console.log(d); break; }
      return total;
    }
    main();
  `);
});

test("a branch binding does not capture the outer name that a recursive call decreases", () => {
  assertClean(`
    function f(n: number): number {
      if (!Number.isSafeInteger(n)) return 0;
      if (n <= 0) return 0;
      if (n > 2) { const n = 5; console.log(n); }
      return f(n - 1);
    }
    f(3);`);
});

test("a shadowing block binding hides no loop and no recursion", () => {
  assertRejected(`function f(n: number): number {
      if (!Number.isSafeInteger(n)) return 0;
      if (n <= 0) return 0;
      const k = n;
      if (n > 1) { const k = n - 1; console.log(k); }
      return f(k);
    }
    f(3);`, "no-decreasing-arg");
  assertRejected(`function g(n: number): number {
      let k = 0;
      { const n = 3; console.log(n); }
      for (let i = 0; i < n; i++) { k = k + 1; }
      return k;
    }
    g(1 / 0);`, "infinite-loop");
  assertRejected(`function h(n: number): number {
      if (n <= 0) return 0;
      try { console.log(n); } catch (n) { console.log(n); }
      return h(n);
    }
    h(1);`, "no-decreasing-arg");
});

// Loop bodies get fresh names too: a while loop lifts its body's last statement into the do step,
// outside the body's letrec*, so a plain inner name there would read the outer counter.
test("a loop-body binding does not capture the counter the loop condition reads", () => {
  assertRejected(`let k = 3; while (k > 0) { let k = 5; k = k - 1; }`, "infinite-loop");
});

// Each guards n before the loop, so with the block's binding captured the loop would look bounded.
test("a block binding that guards a shadowed name does not bound a loop over the outer one", () => {
  assertRejected(`function g(n: number): number {
      let k = 0;
      { const n = 3; if (!Number.isSafeInteger(n)) return 0; }
      for (let i = 0; i < n; i++) { k = k + 1; }
      return k;
    }
    g(1 / 0);`, "infinite-loop");
});

test("a catch variable that guards a shadowed name does not bound a loop over the outer one", () => {
  assertRejected(`function g(n: number): number {
      let k = 0;
      try { throw 1; } catch (n) { if (!Number.isSafeInteger(n)) return 0; }
      for (let i = 0; i < n; i++) { k = k + 1; }
      return k;
    }
    g(1 / 0);`, "infinite-loop");
});

// A function body's letrec* sits at the declaration, so a closure defined above it must not read an
// outer binding of the same name through it.
test("a closure's forward reference to a function-body binding is not captured by an outer one", () => {
  assertRejected(`const n = 3;
    function g(): number {
      const h = (): number => { let k = 0; for (let i = 0; i < n; i++) { k = k + 1; } return k; };
      const n = 1 / 0;
      return h();
    }
    g();`, "infinite-loop");
});

test("a violation in a block-scoped function names it without its fresh suffix", () => {
  const result = checkTypeScript(`function f(n: number): number {
      if (n > 0) { const go = (k: number): number => go(k); return go(n); }
      return 0;
    }
    f(1);`, { toolDeclarations: TOOLS });
  assert.equal(result.ok, false);
  assert.ok(result.violations.some((v) => v.message.startsWith("go: ")), JSON.stringify(result.violations));
  assert.ok(result.violations.every((v) => !v.message.includes("%")), JSON.stringify(result.violations));
});

// HC-30. Types are erased, so a type alias or an interface lowers to nothing wherever it sits.
test("a type alias and an interface are skipped by the lowering, at top level and in a block", () => {
  assertClean(`
    type Point = { x: number; y: number };
    interface Named { readonly name: string; tag?: string; pos: Point; f: (p: Point) => number }
    function norm(p: Point): number {
      type Sq = number;
      interface Box { v: Sq }
      const b: Box = { v: p.x * p.x + p.y * p.y };
      return b.v;
    }
    const n: Named = { name: "a", pos: { x: 1, y: 2 }, f: norm };
    console.log(norm(n.pos) + n.name.length);
  `);
});

test("Record<K, T> is declared by the lib and lowers as a record", () => {
  assertClean(`
    const counts: Record<string, number> = { a: 1, b: 2 };
    let total = 0;
    for (const v of Object.values(counts)) { total += v; }
    for (const k of Object.keys(counts)) { console.log(k); }
    const fixed: Record<"x" | "y", number> = { x: 1, y: 2 };
    console.log(total + fixed.x);
  `);
});

test("an interface admits property signatures only", () => {
  for (const [code, kind] of [
    [`interface I { m(x: unknown): number }`, "unsupported-syntax"],
    [`interface I { [k: string]: number }`, "unsupported-syntax"],
    [`interface I { (x: number): number }`, "unsupported-syntax"],
    [`interface I { new (x: number): I }`, "unsupported-syntax"],
    [`interface A { a: number } interface B extends A { b: number }`, "unsupported-syntax"],
    [`export interface I { a: number }`, "unsupported-syntax"],
    [`declare interface I { a: number }`, "unsupported-syntax"],
    [`interface I { a: any }`, "any-type"],
    [`interface I<T = any> { a: T }`, "any-type"],
    [`const r: Record<number, string> = {};`, "type-error"],
  ]) {
    assertRejected(code, kind);
  }
});

test("an interface or type alias may not reopen a lib or tool type", () => {
  for (const code of [
    `interface Array<T> { evil: (x: T) => void }`,
    `interface String { constructor: unknown }`,
    `interface Record { a: number }`,
    `type Record<K extends string, T> = { [P in K]: T };`,
  ]) {
    assert.ok(kinds(code).includes("unsupported-syntax"), `${code}: ${JSON.stringify(kinds(code))}`);
  }
});

// The method-signature hole of PR #760, reached through an interface instead of a type literal.
test("an interface method signature is rejected, its parameters are bivariant", () => {
  assertRejected(`
    interface M { m(x: unknown, n: number): number }
    function f(x: unknown[], n: number): number {
      if (n < 0) return 0;
      const o: M = { m: f };
      const m = o.m;
      return m(x[0], n + 1);
    }
    f(["a"], 0);
  `, "unsupported-syntax");
});

// HC-31: optional chaining on property and element reads, through a nullish-guarded temporary.
const OPTIONAL_CHAIN = `
  type Hit = { title: string; meta?: { score: number; tags: string[] } };
  async function main(): Promise<number> {
    const hits: Hit[] = [{ title: "a", meta: { score: 2, tags: ["x"] } }, { title: "b" }];
    let total = 0;
    for (const h of hits) {
      total += h.meta?.score ?? 0;
      const first = h.meta?.tags[0] ?? "none";
      console.log(first, h.meta?.tags.length ?? 0, h.meta?.["score"]);
    }
    const w: { tempC: number } | undefined = await getWeather({ city: "Sydney" });
    return total + (w?.tempC ?? 0);
  }
  main();
`;

test("optional property and element reads are accepted", () => {
  assertClean(OPTIONAL_CHAIN);
});

test("a recursive call inside an optional element key is still analysed", () => {
  const loop = checkTypeScript(`function g(xs: number[] | undefined): number { return xs?.[g(xs) - 1] ?? 0; } g([1]);`,
    { toolDeclarations: TOOLS });
  assert.deepEqual(loop.violations.map((v) => v.kind), ["no-decreasing-arg"]);
});

// The positive control matters: without it the rejection below could come from the safe-integer
// rule rather than from the optional read.
test("an optional read does not count as a decrease", () => {
  const shape = (m: string) => `type L = { n: number; next?: L };
    function f(l: L | undefined, n: number): number {
      if (!Number.isSafeInteger(n)) return 0;
      if (n <= 0) return 0;
      const m = ${m};
      return f(l, m);
    }
    f(undefined, 3);`;
  assertClean(shape("n - 1"));
  assertRejected(shape("l?.n ?? n - 1"), "no-decreasing-arg");
});

test("an optional chain opens no escape: computed keys and banned members stay banned", () => {
  assertRejected(`const o: { [k: string]: number } | undefined = { a: 1 }; const k = "a"; console.log(o?.[k]);`, "computed-access");
  assertRejected(`const o: { a: number } | undefined = { a: 1 }; console.log(o?.constructor);`, "forbidden-member");
});

// HC-32: optional and literal-default parameters, filled in at each direct call.
const DEFAULT_PARAMS = `
  function sum(n: number, acc = 0, label?: string): number {
    if (!Number.isSafeInteger(n)) return acc;
    if (n <= 0) return acc;
    return sum(n - 1, acc + n, label);
  }
  const fmt = (n: number, unit = "C", round = true): string => \`\${round ? Math.round(n) : n}\${unit}\`;
  async function main(): Promise<string> {
    const w = await getWeather({ city: "Sydney" });
    console.log(sum(4), sum(3, 10, "x"));
    return fmt(w.tempC) + fmt(w.tempC, "F", false);
  }
  main();
`;

test("optional and literal-default parameters are accepted", () => {
  assertClean(DEFAULT_PARAMS);
});

test("a filled-in default keeps the descent size-change reads", () => {
  const loop = checkTypeScript(`function f(n: number, acc = 0): number { if (n <= 0) return acc; return f(n, acc + 1); } f(3);`,
    { toolDeclarations: TOOLS });
  assert.deepEqual(loop.violations.map((v) => v.kind), ["no-decreasing-arg"]);
});

// The analysis drops a call whose arity cannot match its lambda, so an alias or a callback that
// passes too few arguments would hide the recursion. Each program here never terminates.
test("a defaulted function cannot recurse through a call that omits its argument", () => {
  assertRejected(`function spin(n: number, d = 0): number { const h = spin; return h(n); } spin(1);`, "unsupported-syntax");
  assertRejected(`
    function ap(g: (n: number) => number): number { return g(1); }
    function spin(n: number, d = 0): number { return ap(spin); }
    spin(1);
  `, "unsupported-syntax");
  assertRejected(`function spin(n: number, d?: number): number { return [n].map(spin)[0] ?? 0; } spin(1);`, "unsupported-syntax");
});

// HC-32 review: a const's annotation can declare more parameters than its arrow, so a direct call
// can pass too many, and the analysis drops that call as it drops one that passes too few.
test("a direct call may not pass a defaulted function more arguments than it declares", () => {
  const mk = (call: string) => `
    const mk: (d?: number, e?: number) => (n: number) => number = (d = 0): ((n: number) => number) => spin;
    function spin(n: number): number { const g = ${call}; return g(n); }
    console.log(spin(1));`;
  assertRejected(mk("mk()"), "no-decreasing-arg");
  assertRejected(mk("mk(0, 1)"), "unsupported-syntax");
  assertRejected(`
    const mk: (...xs: number[]) => (n: number) => number = (d = 0): ((n: number) => number) => spin;
    function spin(n: number): number { const g = mk(0, 1, 2); return g(n); }
    console.log(spin(1));`, "unsupported-syntax");
});

// HC-33: assigning to a field of a local const object literal.
const FIELD_ASSIGN = `
  function tally(words: string[]): { a: number; other: number } {
    const counts = { a: 0, other: 0 };
    for (const w of words) {
      if (w === "a") counts.a = counts.a + 1;
      else counts["other"] = counts.other + 1;
    }
    return counts;
  }
  async function main(): Promise<string> {
    const w = await getWeather({ city: "Sydney" });
    const o = { hot: false, n: 0 };
    o.hot = w.tempC > 25;
    o.n = w.tempC;
    for (const kv of Object.entries(tally(["a", "b", "a"]))) console.log(kv);
    return \`\${o.hot} \${o.n}\`;
  }
  main();
`;

test("field assignment on a local const object literal is accepted", () => {
  assertClean(FIELD_ASSIGN);
});

// A string key could reach constructor, so the computed-access gate still refuses it.
test("a field assignment under a computed string key stays refused", () => {
  assertRejected(`function f(k: string): Record<string, number> { const c: Record<string, number> = {}; c[k] = 1; return c; } f("a");`, "computed-access");
});

// A loop or recursion bounded by a field the body changes never ends, so neither may be accepted.
test("a field the body assigns cannot bound a loop or a recursion", () => {
  const loop = checkTypeScript(`
    function f(): number { const o = { n: 1 }; for (let i = 0; i < o.n; i++) o.n = o.n + 1; return o.n; }
    f();`, { toolDeclarations: TOOLS });
  assert.notDeepEqual(loop.violations, []);
  const rec = checkTypeScript(`
    function f(): number {
      const o = { n: 1 };
      const go = (i: number): number => (i >= o.n ? i : go(i + 1));
      o.n = 5;
      return go(0);
    }
    function spin(i: number): number {
      const o = { n: i + 1 };
      if (i >= o.n) return i;
      o.n = o.n + 1;
      return spin(i + 1);
    }
    f(); spin(0);`, { toolDeclarations: TOOLS });
  assert.notDeepEqual(rec.violations, []);
});
