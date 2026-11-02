// Lowering goldens (HC-18): each construct's TypeScript next to the exact IR it must lower to. User
// names are prefixed `js.`, which no TypeScript identifier can contain, so a program's `list` or `do`
// can never be read as the Scheme form of that name.

import { test } from "node:test";
import assert from "node:assert/strict";
import { lowerTypeScript } from "../src/check.ts";
import { write } from "../src/sexp.ts";
import { analyzeDoForms } from "../src/termination/do.ts";
import { checkTermination } from "../src/termination/check.ts";

const TOOLS = `
declare function getWeather(args: { city: string }): Promise<{ tempC: number }>;
declare function fetchCount(n: number): Promise<number>;
`;

function lowered(code: string): string {
  const { ir, violations } = lowerTypeScript(code, { toolDeclarations: TOOLS });
  assert.deepEqual(violations, []);
  return ir.map(write).join(" ");
}

function unsupported(code: string): void {
  const { violations } = lowerTypeScript(code, { toolDeclarations: TOOLS });
  assert.ok(violations.some((v) => v.kind === "unsupported-syntax"), `expected unsupported-syntax, got ${JSON.stringify(violations)}`);
}

test("a function declaration lowers to define, arithmetic to the Scheme operator", () => {
  assert.equal(
    lowered("function f(n: number): number { if (n <= 0) { return 0; } return f(n - 1); }"),
    "(define (js.f js.n) (if (<= js.n 0) 0 (js.f (- js.n 1))))",
  );
});

test("an if with no else takes the rest of the block as its else branch", () => {
  assert.equal(
    lowered("function g(n: number): number { if (n > 3) { return 1; } const m = n * 2; return m + 1; }"),
    "(define (js.g js.n) (if (> js.n 3) 1 (letrec* ((js.m (* js.n 2))) (+ js.m 1))))",
  );
});

test("the rest of a block is copied into each branch that falls through", () => {
  const ir = lowered("function h(n: number): number { let a = 0; if (n > 1) { a = 1; } else { a = 2; } return a; }");
  assert.equal(
    ir,
    "(define (js.h js.n) (letrec* ((js.a 0)) (if (> js.n 1) (begin (set! js.a 1) js.a) (begin (set! js.a 2) js.a))))",
  );
});

test("a const arrow becomes a lambda, and await is a plain call", () => {
  assert.equal(
    lowered("const k = async (n: number): Promise<number> => (await fetchCount(n)) % 2;"),
    "(define js.k (lambda (js.n) (remainder (js.fetchCount js.n) 2)))",
  );
});

test("comparison, logic, negation and ?: lower to their Scheme forms", () => {
  assert.equal(
    lowered("const p = (a: number, b: number): boolean => !(a === b) && (a !== 0 || b < 0) ? true : false;"),
    "(define js.p (lambda (js.a js.b) (if (and (not (eqv? js.a js.b)) (or (not (eqv? js.a 0)) (< js.b 0))) #t #f)))",
  );
});

test("falling off the end of a function returns (void)", () => {
  assert.equal(lowered("function v(n: number): void { fetchCount(n); }"), "(define (js.v js.n) (begin (js.fetchCount js.n) (void)))");
});

test("top-level statements lower in order", () => {
  assert.equal(
    lowered("function f(n: number): number { return n; } const x = f(2); f(x);"),
    "(define (js.f js.n) js.n) (define js.x (js.f 2)) (js.f js.x)",
  );
});

test("an array literal is a list and an object literal a vector of its keys and values", () => {
  assert.equal(
    lowered("const f = (n: number): number => n; const o = { a: 1, f }; const xs = [1, 2, o.a];"),
    '(define js.f (lambda (js.n) js.n)) (define js.o (vector "a" 1 "f" js.f)) (define js.xs (list 1 2 (vector-ref js.o "a")))',
  );
});

test("array members lower by type: length to length, an element read and slice(1) to free calls", () => {
  assert.equal(
    lowered("function s(xs: number[]): number { if (xs.length < 2) { return 0; } return xs[0] + xs[1] + s(xs.slice(1)); }"),
    "(define (js.s js.xs) (if (< (length js.xs) 2) 0 (js.%+ (js.%+ (js.%index js.xs 0) (js.%index js.xs 1)) (js.s (js.method.slice js.xs 1)))))",
  );
});

test("array HOFs lower to the Scheme HOF with the callback first, reduce to fold-left", () => {
  assert.equal(
    lowered("const f = (xs: number[]): number[] => xs.map((x) => x + 1).filter((x) => x > 2);"),
    "(define js.f (lambda (js.xs) (filter (lambda (js.x) (> js.x 2)) (map (lambda (js.x) (js.%+ js.x 1)) js.xs))))",
  );
  assert.equal(
    lowered("const g = (xs: number[]): boolean => xs.some((x) => x > 1) && xs.every((x) => x < 9);"),
    "(define js.g (lambda (js.xs) (and (exists (lambda (js.x) (> js.x 1)) js.xs) (for-all (lambda (js.x) (< js.x 9)) js.xs))))",
  );
  assert.equal(
    lowered("const h = (xs: number[]): number => xs.reduce((a, x) => a + x, 0);"),
    "(define js.h (lambda (js.xs) (fold-left (lambda (js.a js.x) (js.%+ js.a js.x)) 0 js.xs)))",
  );
  assert.equal(
    lowered("function inc(x: number): number { return x + 1; } function pos(x: number): boolean { return x > 0; } function k(xs: number[]): void { xs.forEach(inc); xs.find(pos); }"),
    "(define (js.inc js.x) (js.%+ js.x 1)) (define (js.pos js.x) (> js.x 0)) (define (js.k js.xs) (begin (for-each js.inc js.xs) (begin (find js.pos js.xs) (void))))",
  );
});

test("an array HOF whose callback arity or arguments the Scheme HOF cannot match is unsupported-syntax", () => {
  unsupported("const f = (xs: number[]): number[] => xs.map((x, i) => x + i);");
  unsupported("const f = (xs: number[]): number[] => xs.map(() => 1);");
  unsupported("const f = (xs: number[]): number => xs.reduce((a, x, i) => a + x + i, 0);");
  unsupported("function two(a: number, b: number): number { return a + b; } const f = (xs: number[]): number[] => xs.map(two);");
});

test("a member the lowering cannot place by type is unsupported-syntax", () => {
  unsupported("function f(s: string): string { return s[0]; }");
});

test("a construct the lowering does not know yet is unsupported-syntax, never dropped", () => {
  unsupported("const xs = [1]; const y = xs.pop();");
});

test("a block that declares a binding is unsupported until scoping is lowered, not spliced", () => {
  unsupported("function f(n: number): number { const a = 1; if (n > 0) { const a = 2; } return a; }");
  unsupported("function f(n: number): number { const a = 1; { const a = 2; } return a; }");
});

test("a classic for becomes a do loop whose exit test is the condition's opposite comparison", () => {
  assert.equal(
    lowered("function f(n: number): number { let s = 0; for (let i = 0; i < n; i++) { s = s + i; } return s; }"),
    "(define (js.f js.n) (letrec* ((js.s 0)) (begin (do ((js.i 0 (+ js.i 1))) ((>= js.i js.n)) (begin (set! js.s (+ js.s js.i)) (void))) js.s)))",
  );
  assert.equal(
    lowered("function g(xs: number[]): void { for (let i = xs.length; i > 0; i -= 2) { fetchCount(i); } }"),
    "(define (js.g js.xs) (begin (do ((js.i (length js.xs) (- js.i 2))) ((<= js.i 0)) (begin (js.fetchCount js.i) (void))) (void)))",
  );
  assert.equal(
    lowered("function h(n: number): void { for (let i = 0, j = 1; i < n; i = i + 1) { fetchCount(j); } }"),
    "(define (js.h js.n) (begin (do ((js.i 0 (+ js.i 1)) (js.j 1)) ((>= js.i js.n)) (begin (js.fetchCount js.j) (void))) (void)))",
  );
  assert.equal(
    lowered("function k(n: number, b: boolean): void { for (let i = 0; b && i < n; i++) { fetchCount(i); } }"),
    "(define (js.k js.n js.b) (begin (do ((js.i 0 (+ js.i 1))) ((not (and js.b (< js.i js.n)))) (begin (js.fetchCount js.i) (void))) (void)))",
  );
});

test("the do loop a for lowers to meets the do-loop rules: progress accepted, regress rejected", () => {
  const { ir: up } = lowerTypeScript("function f(n: number): void { for (let i = 0; i < n; ++i) { fetchCount(i); } }", { toolDeclarations: TOOLS });
  assert.deepEqual(analyzeDoForms(up), []);
  const { ir: down } = lowerTypeScript("function f(n: number): void { for (let i = 0; i < n; i--) { fetchCount(i); } }", { toolDeclarations: TOOLS });
  assert.notDeepEqual(analyzeDoForms(down), []);
});

test("for...of becomes for-each over a lambda binding the element", () => {
  assert.equal(
    lowered("function f(xs: number[]): number { let s = 0; for (const x of xs) { s = s + x; } return s; }"),
    "(define (js.f js.xs) (letrec* ((js.s 0)) (begin (for-each (lambda (js.x) (begin (set! js.s (js.%+ js.s js.x)) (void))) js.xs) js.s)))",
  );
});

test("a loop the lowering cannot model is unsupported-syntax", () => {
  // A return, break or continue inside a loop body leaves the loop early; lowering it as a value
  // would lose the function's result, and with it any lambda the result carries.
  unsupported("function f(n: number): number { for (let i = 0; i < n; i++) { return i; } return 0; }");
  unsupported("function f(n: number): number { for (let i = 0; i < n; i++) { if (i > 2) { break; } } return 0; }");
  unsupported("function f(xs: number[]): number { for (const x of xs) { if (x > 2) { continue; } } return 0; }");
  unsupported("function f(xs: number[]): number { for (const x of xs) { if (x > 2) { return x; } } return 0; }");
  // Parts the do loop has no place for.
  unsupported("function f(n: number): void { let i = 0; for (; i < n; i++) { fetchCount(i); } }");
  unsupported("function f(n: number): void { for (let i = 0; ; i++) { fetchCount(i); } }");
  unsupported("function f(n: number): void { for (let i = 0; i < n;) { i++; } }");
  unsupported("function f(n: number, k: number): void { for (let i = 0; i < n; k++) { fetchCount(i); } }");
  unsupported("function f(n: number): void { for (let i = 0; i < n; i *= 2) { fetchCount(i); } }");
  unsupported("function f(n: number): void { for (var i = 0; i < n; i++) { fetchCount(i); } }");
  unsupported("function f(s: string): void { for (const c of s) { fetchCount(1); } }");
  unsupported("function f(xs: number[][]): void { for (const [a] of xs) { fetchCount(a); } }");
});

test("a while whose body ends in one update of a variable becomes a do loop stepping it, assigned back", () => {
  assert.equal(
    lowered("function f(n: number): number { while (n > 0) { fetchCount(n); n = n - 1; } return n; }"),
    "(define (js.f js.n) (begin (set! js.n (do ((js.n js.n (- js.n 1))) ((<= js.n 0) js.n) (begin (js.fetchCount js.n) (void)))) js.n))",
  );
  assert.equal(
    lowered("function g(n: number): void { let i = 0; while (i < n) i++; }"),
    "(define (js.g js.n) (letrec* ((js.i 0)) (begin (set! js.i (do ((js.i js.i (+ js.i 1))) ((>= js.i js.n) js.i) (void))) (void))))",
  );
  const { ir } = lowerTypeScript("function f(n: number): void { while (n > 0) { fetchCount(n); n--; } }", { toolDeclarations: TOOLS });
  assert.deepEqual(analyzeDoForms(ir), []);
});

test("any other while is unsupported-syntax", () => {
  unsupported("function f(n: number): void { while (n > 0) { n = n - 1; fetchCount(n); } }");
  unsupported("function f(n: number): void { while (n > 0) { } }");
  unsupported("function f(n: number): void { while (n > 0) { if (n > 3) { continue; } n--; } }");
  unsupported("function f(n: number): number { while (n > 0) { if (n > 3) { return n; } n--; } return 0; }");
});

test("?? lowers to or, a template to string-append, and throw to raise, which ends its block", () => {
  assert.equal(
    lowered("const f = (a: number | undefined, b: number): number => a ?? b;"),
    "(define js.f (lambda (js.a js.b) (or js.a js.b)))",
  );
  assert.equal(
    lowered("const g = (n: number, s: string): string => `n=${n}, s=${s}!`;"),
    '(define js.g (lambda (js.n js.s) (string-append "n=" js.n ", s=" js.s "!")))',
  );
  assert.equal(
    lowered("function h(n: number): number { if (n < 0) { throw n; } return n; }"),
    "(define (js.h js.n) (if (< js.n 0) (raise js.n) js.n))",
  );
});

test("a switch lowers to nested ifs on eqv?, with the rest of the block after each break", () => {
  assert.equal(
    lowered("function f(n: number): number { switch (n) { case 1: case 2: return 10; case 3: n = 4; break; default: return 0; } return n; }"),
    "(define (js.f js.n) (if (or (eqv? js.n 1) (eqv? js.n 2)) 10 (if (eqv? js.n 3) (begin (set! js.n 4) js.n) 0)))",
  );
  assert.equal(
    lowered("function g(s: string): number { switch (s) { case \"a\": return 1; } return 2; }"),
    '(define (js.g js.s) (if (eqv? js.s "a") 1 2))',
  );
});

test("a switch that falls through, breaks early, binds, or puts default first is unsupported-syntax", () => {
  unsupported("function f(n: number): number { switch (n) { case 1: n = 2; case 2: return n; } return 0; }");
  unsupported("function f(n: number): number { switch (n) { case 1: if (n > 0) { break; } return 1; } return 0; }");
  unsupported("function f(n: number): number { switch (n) { case 1: const m = 2; return m; } return 0; }");
  unsupported("function f(n: number): number { switch (n) { default: return 0; case 1: return 1; } }");
  unsupported("function f(n: number): number { switch (n + 1) { case 1: return 1; } return 0; }");
});

test("try/catch lowers to guard, with the rest of the block copied into both", () => {
  assert.equal(
    lowered("function f(n: number): number { try { fetchCount(n); } catch (e) { return 0; } return n; }"),
    "(define (js.f js.n) (guard (js.e (#t 0)) (begin (js.fetchCount js.n) js.n)))",
  );
  assert.equal(
    lowered("function g(n: number): number { try { return n; } catch { n = 1; } return n; }"),
    "(define (js.g js.n) (guard (%e (#t (begin (set! js.n 1) js.n))) js.n))",
  );
});

test("finally, and a try or catch block that binds, are unsupported-syntax", () => {
  unsupported("function f(n: number): number { try { return n; } finally { fetchCount(n); } }");
  unsupported("function f(n: number): number { try { const m = n; return m; } catch (e) { return 0; } }");
});

test("an object literal may not define a member JavaScript calls implicitly", () => {
  // `${o}`, `"" + o`, JSON.stringify(o) and `await o` call these with no call in the program text,
  // so the IR would hold no edge to the method and could not see it recurse.
  unsupported("const o = { toString: (): string => `${o}` }; const s = `${o}`;");
  unsupported("const o = { valueOf: (): number => 1 }; const s = '' + o;");
  unsupported("const o = { \"toJSON\": (): string => \"x\" }; const s = 1;");
  unsupported("const then = (r: (v: number) => void): void => r(1); const o = { then };");
});

test("a lib global's method lowers to a call of a free name the analysis does not model", () => {
  assert.equal(
    lowered("const a = Math.max(1, 2); console.log(JSON.stringify({ a }), Object.keys({ a }));"),
    '(define js.a (js.Math.max 1 2)) (js.console.log (js.JSON.stringify (vector "a" js.a)) (js.Object.keys (vector "a" js.a)))',
  );
});

test("a string or number method, or a non-mutating array method, lowers to a free name with the receiver first", () => {
  assert.equal(
    lowered("const f = (s: string, xs: number[]): string => s.split(\",\").join(xs.indexOf(1).toFixed(2));"),
    '(define js.f (lambda (js.s js.xs) (js.method.join (js.method.split js.s ",") (js.method.toFixed (js.method.indexOf js.xs 1) 2))))',
  );
  assert.equal(
    lowered("const g = (xs: number[]): number => xs.findIndex((x, i) => x > i);"),
    "(define js.g (lambda (js.xs) (js.method.findIndex js.xs (lambda (js.x js.i) (> js.x js.i)))))",
  );
  assert.equal(
    lowered("const h = (xs: number[]): number[] => xs.slice(2).map((x) => x);"),
    "(define js.h (lambda (js.xs) (map (lambda (js.x) js.x) (js.method.slice js.xs 2))))",
  );
});

test("every array mutator but push, sort and reverse is unsupported", () => {
  for (const m of ["pop()", "shift()", "unshift(1)"]) {
    unsupported(`const xs: number[] = [3]; xs.${m};`);
  }
});

test("a method call on a record is unsupported, the lowering does not place it", () => {
  unsupported("const o = { f: (n: number): number => n }; const r = o.f(1);");
});

test("object destructuring reads each field with vector-ref, from a temporary bound first unless the source is a variable", () => {
  assert.equal(
    lowered("async function f(): Promise<number> { const { tempC, tempC: t } = await getWeather({ city: \"x\" }); return tempC + t; }"),
    '(define (js.f) (letrec* ((%js.tmp1 (js.getWeather (vector "city" "x"))) (js.tempC (vector-ref %js.tmp1 "tempC")) (js.t (vector-ref %js.tmp1 "tempC"))) (js.%+ js.tempC js.t)))',
  );
  assert.equal(
    lowered("const o = { a: 1 }; const { a } = o;"),
    '(define js.o (vector "a" 1)) (define js.a (vector-ref js.o "a"))',
  );
});

test("array destructuring takes a free index by position and a free slice for the rest", () => {
  assert.equal(
    lowered("function f(xs: number[]): number { const [h, , k, ...rest] = xs; return h + k + rest.length; }"),
    "(define (js.f js.xs) (letrec* ((js.h (js.%index js.xs 0)) (js.k (js.%index js.xs 2)) (js.rest (js.method.slice js.xs 3))) (js.%+ (js.%+ js.h js.k) (length js.rest))))",
  );
});

test("destructuring with a default or an object rest is unsupported-syntax", () => {
  unsupported("const o = { a: 1 }; const { a = 2 } = o;");
  unsupported("const o = { a: 1, b: 2 }; const { a, ...r } = o;");
  unsupported("const o = { a: { b: 1 } }; const { a: { b = 2 } } = o;");
});

test("a block binding is letrec*, so an arrow that calls itself by its const name is seen to recurse", () => {
  const { ir } = lowerTypeScript("function f(): number { const g = (n: number): number => g(n); return g(1); }", { toolDeclarations: TOOLS });
  assert.equal(ir.map(write).join(" "), "(define (js.f) (letrec* ((js.g (lambda (js.n) (js.g js.n)))) (js.g 1)))");
  assert.ok(checkTermination(ir).length > 0, "the self-call must be a termination violation");
});

test("a for initializer that names a variable of the same loop is unsupported-syntax", () => {
  // do evaluates its inits outside the loop's scope, so the name would be free and a leaf.
  unsupported("function f(): void { for (let g = (n: number): number => g(n), i = 0; i < 1; i++) { g(1); } }");
  unsupported("function f(): void { for (let i = 0, j = i; i < 1; i++) { fetchCount(j); } }");
});

test("array spread lowers to append, with each run of plain elements as one list", () => {
  assert.equal(
    lowered("const f = (xs: number[], ys: number[]): number[] => [0, ...xs, 1, 2, ...ys];"),
    "(define js.f (lambda (js.xs js.ys) (append (list 0) js.xs (list 1 2) js.ys)))",
  );
  assert.equal(lowered("const g = (xs: number[]): number[] => [...xs];"), "(define js.g (lambda (js.xs) (append js.xs)))");
});

test("call spread lowers to apply, with the plain arguments before the first spread passed directly", () => {
  assert.equal(
    lowered("const m = (xs: number[]): number => Math.max(0, ...xs);"),
    "(define js.m (lambda (js.xs) (apply js.Math.max 0 js.xs)))",
  );
  assert.equal(
    lowered("const j = (s: string, xs: string[]): string => s.concat(...xs, \"!\");"),
    '(define js.j (lambda (js.s js.xs) (apply js.method.concat js.s (append js.xs (list "!")))))',
  );
});

test("a function that calls itself through a spread is still seen to recurse", () => {
  const { ir, violations } = lowerTypeScript(
    "function h(n: number, m: number): number { const p: [number, number] = [m, n]; return h(...p); }",
    { toolDeclarations: TOOLS },
  );
  assert.deepEqual(violations, []);
  assert.equal(ir.map(write).join(" "), "(define (js.h js.n js.m) (letrec* ((js.p (list js.m js.n))) (apply js.h js.p)))");
  assert.ok(checkTermination(ir).length > 0, "a self-call through apply must be a termination violation");
});

test("a spread into an array HOF is unsupported-syntax", () => {
  unsupported("const f = (xs: number[], fs: [(x: number) => number]): number[] => xs.map(...fs);");
});

// push is the one growing mutator lowered, and only on a const bound to an array literal in the
// same function, used for nothing that could alias it. A growing array would otherwise break the
// stable length bound of a loop (checkpoint 9).
test("push on a fresh local array lowers to an escaping free call", () => {
  assert.equal(
    lowered("function f(xs: number[]): number[] { const out: number[] = []; for (const x of xs) { out.push(x * 2); } return out; }"),
    "(define (js.f js.xs) (letrec* ((js.out (list))) (begin (for-each (lambda (js.x) (begin (js.method.push js.out (* js.x 2)) (void))) js.xs) js.out)))",
  );
});

test("push on an array that may alias another is unsupported-syntax", () => {
  unsupported("function f(xs: number[]): number { xs.push(1); return 0; }");
  unsupported("function f(xs: number[]): number { const r = xs.slice(1); r.push(0); if (r.length === 0) { return 0; } return f(r); }");
  unsupported("function f(): number { const out: number[] = []; const y = out; for (const e of y) { out.push(e); } return 0; }");
  unsupported("function f(): number { const out: number[] = []; g(out); out.push(1); return 0; } function g(a: number[]): number { return 0; }");
  unsupported("function f(): number[] { const out: number[] = []; const add = (x: number): number => out.push(x); add(1); return out; }");
  unsupported("function f(): number { let out: number[] = []; out.push(1); return 0; }");
});

test("a loop whose bound or iterable is an array its body pushes to is unsupported-syntax", () => {
  unsupported("function f(): number { const out: number[] = [1]; for (const e of out) { out.push(e); } return 0; }");
  unsupported("function f(): number { const out: number[] = [1]; for (let i = 0; i < out.length; i++) { out.push(i); } return 0; }");
  unsupported("function f(): number { const out: number[] = [1]; let i = 0; while (i < out.length) { out.push(i); i = i + 1; } return 0; }");
});

test("a loop, if, switch or try at top level lowers as it does in a function body", () => {
  assert.equal(
    lowered("for (const c of [1, 2]) { console.log(c); }"),
    "(begin (for-each (lambda (js.c) (begin (js.console.log js.c) (void))) (list 1 2)) (void))",
  );
  assert.equal(
    lowered("let k = 3; while (k > 0) { k = k - 1; }"),
    "(define js.k 3) (begin (set! js.k (do ((js.k js.k (- js.k 1))) ((<= js.k 0) js.k) (void))) (void))",
  );
  assert.equal(
    lowered("for (let i = 0; i < 2; i++) { console.log(i); }"),
    "(begin (do ((js.i 0 (+ js.i 1))) ((>= js.i 2)) (begin (js.console.log js.i) (void))) (void))",
  );
  assert.equal(lowered("const n = 1; if (n > 0) { console.log(n); }"), "(define js.n 1) (if (> js.n 0) (begin (js.console.log js.n) (void)) (void))");
});

test("a top-level loop is judged by the loop rules", () => {
  const { ir } = lowerTypeScript("let k = 3; while (k > 0) { k = k + 1; }", { toolDeclarations: TOOLS });
  assert.ok(checkTermination(ir).length > 0);
});

test("as const lowers to its operand", () => {
  assert.equal(lowered("const xs = [1, 2] as const;"), "(define js.xs (list 1 2))");
});

test("a record read with a string literal key lowers to vector-ref", () => {
  assert.equal(lowered('const v = ({ a: 1 })["a"];'), '(define js.v (vector-ref (vector "a" 1) "a"))');
});

test("a nested pattern destructures a temporary bound to the outer field", () => {
  assert.equal(
    lowered("const { a: { b } } = { a: { b: 1 } };"),
    '(define %js.tmp1 (vector "a" (vector "b" 1))) (define %js.tmp2 (vector-ref %js.tmp1 "a")) (define js.b (vector-ref %js.tmp2 "b"))',
  );
});

test("a destructuring parameter becomes a temporary, destructured at the top of the body", () => {
  assert.equal(
    lowered("const ps = [{ name: \"a\" }]; const ns = ps.map(({ name: n }) => n);"),
    '(define js.ps (list (vector "name" "a"))) (define js.ns (map (lambda (%js.tmp1) (letrec* ((js.n (vector-ref %js.tmp1 "name"))) js.n)) js.ps))',
  );
});

test("sort and reverse keep the length, so they lower to escaping free calls", () => {
  assert.equal(
    lowered("const xs = [3, 1]; const ys = xs.slice().sort((a, b) => a - b); xs.reverse();"),
    "(define js.xs (list 3 1)) (define js.ys (js.method.sort (js.method.slice js.xs) (lambda (js.a js.b) (- js.a js.b)))) (js.method.reverse js.xs)",
  );
});

test("a pushed array may be the receiver of an array HOF or reader, or spread, since none of them aliases it", () => {
  assert.equal(
    lowered("function f(): number { const out: number[] = []; out.push(1); const ys = out.map((x) => x + 1); const j = out.join(\",\"); return Math.max(...out, ys.length, j.length); }"),
    '(define (js.f) (letrec* ((js.out (list))) (begin (js.method.push js.out 1) (letrec* ((js.ys (map (lambda (js.x) (js.%+ js.x 1)) js.out))) (letrec* ((js.j (js.method.join js.out ","))) (apply js.Math.max (append js.out (list (length js.ys) (string-length js.j)))))))))',
  );
  unsupported("function f(): number[] { const out: number[] = []; out.push(1); return out.slice(1); }");
  unsupported("function f(): number[] { const out: number[] = []; out.push(1); return out.sort(); }");
});

test("an object spread lowers to a free call, so the analysis knows nothing of its result", () => {
  assert.equal(
    lowered("const o = { a: 1 }; const p = { ...o, b: 2 };"),
    '(define js.o (vector "a" 1)) (define js.p (js.%spread js.o (vector "b" 2)))',
  );
  unsupported("const o = { a: 1 }; const p = { ...o, toString: () => \"x\" };");
  unsupported("const xs = [1]; const p = { ...xs };");
});

test("a compound assignment or increment statement lowers to set!", () => {
  assert.equal(
    lowered("let t = 0; t += 2; t -= 1; t++; --t;"),
    "(define js.t 0) (set! js.t (+ js.t 2)) (set! js.t (- js.t 1)) (set! js.t (+ js.t 1)) (set! js.t (- js.t 1))",
  );
});

test("unary plus lowers to a one-argument +", () => {
  assert.equal(lowered("const k = 2; const m = +k;"), "(define js.k 2) (define js.m (+ js.k))");
});

test("a call argument naming a pure const lowers as its expression only in a call that recurses back (HC-22)", () => {
  assert.equal(
    lowered("function f(n: number): number { const m = n - 1; return m > 0 ? f(m) : m; }"),
    "(define (js.f js.n) (letrec* ((js.m (- js.n 1))) (if (> js.m 0) (js.f (- js.n 1)) js.m)))",
  );
  assert.equal(
    lowered("function g(a: number): number { return a; } function h(n: number): number { const m = n - 1; return g(m); }"),
    "(define (js.g js.a) js.a) (define (js.h js.n) (letrec* ((js.m (- js.n 1))) (js.g js.m)))",
  );
});
