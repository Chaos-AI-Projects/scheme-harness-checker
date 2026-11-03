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
    "(define (js.g js.n) (if (> js.n 3) 1 (letrec* ((js.m%1 (* js.n 2))) (+ js.m%1 1))))",
  );
});

test("the rest of a block is copied into each branch that falls through", () => {
  const ir = lowered("function h(n: number): number { let a = 0; if (n > 1) { a = 1; } else { a = 2; } return a; }");
  assert.equal(
    ir,
    "(define (js.h js.n) (letrec* ((js.a%1 0)) (if (> js.n 1) (begin (set! js.a%1 1) js.a%1) (begin (set! js.a%1 2) js.a%1))))",
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

// HC-29: a block is spliced in front of the statements after it, so each binding it declares gets a
// fresh name. A later statement naming the outer binding keeps the outer name.
test("a binding in a spliced block gets a fresh name that the rest of the block cannot capture", () => {
  assert.equal(
    lowered("function f(n: number): number { const a = 1; if (n > 0) { const a = 2; fetchCount(a); } return a; }"),
    "(define (js.f js.n) (letrec* ((js.a%1 1)) (if (> js.n 0) (letrec* ((js.a%2 2)) (begin (js.fetchCount js.a%2) js.a%1)) js.a%1)))",
  );
  assert.equal(
    lowered("function f(n: number): number { const a = 1; { const a = 2; fetchCount(a); } return a; }"),
    "(define (js.f js.n) (letrec* ((js.a%1 1)) (letrec* ((js.a%2 2)) (begin (js.fetchCount js.a%2) js.a%1))))",
  );
});

test("try, catch and case bindings and the catch variable get fresh names", () => {
  assert.equal(
    lowered("function f(e: number): number { try { const a = e; fetchCount(a); } catch (e) { const b = 1; fetchCount(b); } return e; }"),
    "(define (js.f js.e) (guard (js.e%1 (#t (letrec* ((js.b%2 1)) (begin (js.fetchCount js.b%2) js.e)))) " +
      "(letrec* ((js.a%3 js.e)) (begin (js.fetchCount js.a%3) js.e))))",
  );
  assert.equal(
    lowered("function f(k: number): number { switch (k) { case 1: const a = 2; return a; default: const b = k; fetchCount(b); break; } return k; }"),
    "(define (js.f js.k) (if (eqv? js.k 1) (letrec* ((js.a%1 2)) js.a%1) (letrec* ((js.b%2 js.k)) (begin (js.fetchCount js.b%2) js.k))))",
  );
});

// A case's binding scopes over the whole switch in JavaScript, so a later case could name it and
// throw for touching it before its declaration ran. The IR has no binding there to model that.
test("a case binding named outside its own case is unsupported-syntax", () => {
  // TypeScript rejects a direct use (TS2454) but not one inside a closure.
  unsupported("function f(k: number): number { switch (k) { case 1: const a = 2; return a; default: const g = (): number => a; return g(); } }");
});

test("a destructuring and a shorthand property name the fresh binding", () => {
  assert.equal(
    lowered("function f(p: { x: number }): number { if (p.x > 0) { const { x } = p; fetchCount(x); const o = { x }; return o.x; } return 0; }"),
    "(define (js.f js.p) (if (> (vector-ref js.p \"x\") 0) (letrec* ((js.x%1 (vector-ref js.p \"x\"))) " +
      "(begin (js.fetchCount js.x%1) (letrec* ((js.o%2 (vector \"x\" js.x%1))) (vector-ref js.o%2 \"x\")))) 0))",
  );
});

test("a binding in a function or loop body gets a fresh name too", () => {
  assert.equal(
    lowered("function f(xs: number[]): void { const n = 1; for (const x of xs) { const y = x; fetchCount(y); } }"),
    "(define (js.f js.xs) (letrec* ((js.n%1 1)) (begin (for-each (lambda (js.x) (letrec* ((js.y%2 js.x)) (begin (js.fetchCount js.y%2) (void)))) js.xs) (void))))",
  );
});

test("a classic for becomes a do loop whose exit test is the condition's opposite comparison", () => {
  assert.equal(
    lowered("function f(n: number): number { let s = 0; for (let i = 0; i < n; i++) { s = s + i; } return s; }"),
    "(define (js.f js.n) (letrec* ((js.s%1 0)) (begin (do ((js.i 0 (+ js.i 1))) ((>= js.i js.n)) (begin (set! js.s%1 (+ js.s%1 js.i)) (void))) js.s%1)))",
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
    "(define (js.f js.xs) (letrec* ((js.s%1 0)) (begin (for-each (lambda (js.x) (begin (set! js.s%1 (js.%+ js.s%1 js.x)) (void))) js.xs) js.s%1)))",
  );
});

// HC-38: a pattern in the head binds a temporary, destructured at the top of the body, as a
// destructuring parameter is.
test("a for...of head pattern binds a temporary the body destructures", () => {
  assert.equal(
    lowered("function f(xs: number[][]): void { for (const [a] of xs) { fetchCount(a); } }"),
    "(define (js.f js.xs) (begin (for-each (lambda (%js.tmp1) (letrec* ((js.a (js.%index %js.tmp1 0))) (begin (js.fetchCount js.a) (void)))) js.xs) (void)))",
  );
  assert.equal(
    lowered("const o: { [k: string]: number } = { a: 1 }; for (const [k, v] of Object.entries(o)) { console.log(k, v); }"),
    '(define js.o (vector "a" 1)) (begin (for-each (lambda (%js.tmp1) (letrec* ((js.k (js.%index %js.tmp1 0)) (js.v (js.%index %js.tmp1 1))) (begin (js.console.log js.k js.v) (void)))) (js.Object.entries js.o)) (void))',
  );
  assert.equal(
    lowered("const ps = [{ name: \"a\" }]; for (const { name: n } of ps) { console.log(n); }"),
    '(define js.ps (list (vector "name" "a"))) (begin (for-each (lambda (%js.tmp1) (letrec* ((js.n (vector-ref %js.tmp1 "name"))) (begin (js.console.log js.n) (void)))) js.ps) (void))',
  );
});

test("a for...of head pattern the destructuring path cannot lower stays unsupported-syntax", () => {
  unsupported("function f(xs: number[][]): void { for (const [a = 1] of xs) { fetchCount(a); } }");
  unsupported("function f(xs: { a: number; b: number }[]): void { for (const { a, ...r } of xs) { fetchCount(a); } }");
  // An object pattern over an array element would read a field the array has no vector for.
  unsupported("function f(xs: number[][]): void { for (const { length } of xs) { fetchCount(length); } }");
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
});

test("a while whose body ends in one update of a variable becomes a do loop stepping it, assigned back", () => {
  assert.equal(
    lowered("function f(n: number): number { while (n > 0) { fetchCount(n); n = n - 1; } return n; }"),
    "(define (js.f js.n) (begin (set! js.n (do ((js.n js.n (- js.n 1))) ((<= js.n 0) js.n) (begin (js.fetchCount js.n) (void)))) js.n))",
  );
  assert.equal(
    lowered("function g(n: number): void { let i = 0; while (i < n) i++; }"),
    "(define (js.g js.n) (letrec* ((js.i%1 0)) (begin (set! js.i%1 (do ((js.i%1 js.i%1 (+ js.i%1 1))) ((>= js.i%1 js.n) js.i%1) (void))) (void))))",
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

test("a switch that falls through, breaks early, or puts default first is unsupported-syntax", () => {
  unsupported("function f(n: number): number { switch (n) { case 1: n = 2; case 2: return n; } return 0; }");
  unsupported("function f(n: number): number { switch (n) { case 1: if (n > 0) { break; } return 1; } return 0; }");
  unsupported("function f(n: number): number { switch (n) { default: return 0; case 1: return 1; } }");
  unsupported("function f(n: number): number { switch (n + 1) { case 1: return 1; } return 0; }");
});

test("try/catch lowers to guard, with the rest of the block copied into both", () => {
  assert.equal(
    lowered("function f(n: number): number { try { fetchCount(n); } catch (e) { return 0; } return n; }"),
    "(define (js.f js.n) (guard (js.e%1 (#t 0)) (begin (js.fetchCount js.n) js.n)))",
  );
  assert.equal(
    lowered("function g(n: number): number { try { return n; } catch { n = 1; } return n; }"),
    "(define (js.g js.n) (guard (%e (#t (begin (set! js.n 1) js.n))) js.n))",
  );
});

test("finally is unsupported-syntax", () => {
  unsupported("function f(n: number): number { try { return n; } finally { fetchCount(n); } }");
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
    '(define (js.f) (letrec* ((%js.tmp1 (js.getWeather (vector "city" "x"))) (js.tempC%1 (vector-ref %js.tmp1 "tempC")) (js.t%2 (vector-ref %js.tmp1 "tempC"))) (js.%+ js.tempC%1 js.t%2)))',
  );
  assert.equal(
    lowered("const o = { a: 1 }; const { a } = o;"),
    '(define js.o (vector "a" 1)) (define js.a (vector-ref js.o "a"))',
  );
});

test("array destructuring takes a free index by position and a free slice for the rest", () => {
  assert.equal(
    lowered("function f(xs: number[]): number { const [h, , k, ...rest] = xs; return h + k + rest.length; }"),
    "(define (js.f js.xs) (letrec* ((js.h%1 (js.%index js.xs 0)) (js.k%2 (js.%index js.xs 2)) (js.rest%3 (js.method.slice js.xs 3))) (js.%+ (js.%+ js.h%1 js.k%2) (length js.rest%3))))",
  );
});

test("destructuring with a default or an object rest is unsupported-syntax", () => {
  unsupported("const o = { a: 1 }; const { a = 2 } = o;");
  unsupported("const o = { a: 1, b: 2 }; const { a, ...r } = o;");
  unsupported("const o = { a: { b: 1 } }; const { a: { b = 2 } } = o;");
});

test("a block binding is letrec*, so an arrow that calls itself by its const name is seen to recurse", () => {
  const { ir } = lowerTypeScript("function f(): number { const g = (n: number): number => g(n); return g(1); }", { toolDeclarations: TOOLS });
  assert.equal(ir.map(write).join(" "), "(define (js.f) (letrec* ((js.g%1 (lambda (js.n) (js.g%1 js.n)))) (js.g%1 1)))");
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
  assert.equal(ir.map(write).join(" "), "(define (js.h js.n js.m) (letrec* ((js.p%1 (list js.m js.n))) (apply js.h js.p%1)))");
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
    "(define (js.f js.xs) (letrec* ((js.out%1 (list))) (begin (for-each (lambda (js.x) (begin (js.method.push js.out%1 (* js.x 2)) (void))) js.xs) js.out%1)))",
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
    '(define (js.f) (letrec* ((js.out%1 (list))) (begin (js.method.push js.out%1 1) (letrec* ((js.ys%2 (map (lambda (js.x) (js.%+ js.x 1)) js.out%1))) (letrec* ((js.j%3 (js.method.join js.out%1 ","))) (apply js.Math.max (append js.out%1 (list (length js.ys%2) (string-length js.j%3)))))))))',
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
    "(define (js.f js.n) (letrec* ((js.m%1 (- js.n 1))) (if (> js.m%1 0) (js.f (- js.n 1)) js.m%1)))",
  );
  assert.equal(
    lowered("function g(a: number): number { return a; } function h(n: number): number { const m = n - 1; return g(m); }"),
    "(define (js.g js.a) js.a) (define (js.h js.n) (letrec* ((js.m%1 (- js.n 1))) (js.g js.m%1)))",
  );
});

// HC-26: 5,000 chained consts in a function body overflow the stack inside lowering itself.
test("a program nested deeper than the lowering's stack is a violation, not a throw", () => {
  const chain = Array.from({ length: 5000 }, (_, k) => `  const c${k + 1} = c${k};`).join("\n");
  const code = `function f(n: number): number {\n  const c0 = n;\n${chain}\n  return c5000;\n}`;
  const { ir, violations } = lowerTypeScript(code, { toolDeclarations: TOOLS });
  assert.deepEqual(ir, []);
  assert.deepEqual(violations.map((v) => v.kind), ["unsupported-syntax"]);
});

// HC-28: typeof has no effect, always returns and calls no user code, so a free call is exact enough.
test("typeof lowers to a free call, and its comparison through the === path", () => {
  assert.equal(
    lowered("const f = (d: unknown): boolean => typeof d === \"object\" && d !== null;"),
    '(define js.f (lambda (js.d) (and (eqv? (js.%typeof js.d) "object") (not (eqv? js.d js.null)))))',
  );
});

// HC-31: an optional chain binds its receiver to a temporary, and the read runs only when that is not
// nullish. The rest of the chain sits inside the guard, because `a?.b.c` skips `.c` too.
test("an optional property read lowers to a nullish-guarded temporary", () => {
  assert.equal(
    lowered("const f = (o: { b: number } | undefined): number => o?.b ?? 0;"),
    '(define js.f (lambda (js.o) (or (letrec* ((%js.tmp1 js.o)) (if (js.%nullish %js.tmp1) (void) (vector-ref %js.tmp1 "b"))) 0)))',
  );
});

test("an optional element read and length read the receiver through its non-nullable type", () => {
  assert.equal(
    lowered("const g = (xs: number[] | null): number => (xs?.[0] ?? 0) + (xs?.length ?? 0);"),
    "(define js.g (lambda (js.xs) (js.%+ (or (letrec* ((%js.tmp1 js.xs)) (if (js.%nullish %js.tmp1) (void) (js.%index %js.tmp1 0))) 0) " +
      "(or (letrec* ((%js.tmp2 js.xs)) (if (js.%nullish %js.tmp2) (void) (length %js.tmp2))) 0))))",
  );
  assert.equal(
    lowered('const h = (o: { k: string } | undefined): string | undefined => o?.["k"];'),
    '(define js.h (lambda (js.o) (letrec* ((%js.tmp1 js.o)) (if (js.%nullish %js.tmp1) (void) (vector-ref %js.tmp1 "k")))))',
  );
});

test("the rest of an optional chain is read inside its guard", () => {
  assert.equal(
    lowered("const f = (o: { a: { c: number } } | undefined): number | undefined => o?.a.c;"),
    '(define js.f (lambda (js.o) (letrec* ((%js.tmp1 js.o)) (if (js.%nullish %js.tmp1) (void) (vector-ref (vector-ref %js.tmp1 "a") "c")))))',
  );
  assert.equal(
    lowered("const g = (o: { a?: { c: number } } | undefined): number | undefined => o?.a?.c;"),
    "(define js.g (lambda (js.o) (letrec* ((%js.tmp1 js.o)) (if (js.%nullish %js.tmp1) (void) " +
      '(letrec* ((%js.tmp2 (vector-ref %js.tmp1 "a"))) (if (js.%nullish %js.tmp2) (void) (vector-ref %js.tmp2 "c")))))))',
  );
});

test("an optional chain's element key is evaluated only inside the guard", () => {
  assert.equal(
    lowered("const f = (xs: number[] | undefined, n: number): number | undefined => xs?.[n - 1];"),
    "(define js.f (lambda (js.xs js.n) (letrec* ((%js.tmp1 js.xs)) (if (js.%nullish %js.tmp1) (void) (js.%index %js.tmp1 (- js.n 1))))))",
  );
});

test("a call inside an optional chain is not lowered", () => {
  unsupported("const f = (g: (() => number) | undefined): number | undefined => g?.();");
  unsupported("const f = (o: { m: () => number }): number | undefined => o.m?.();");
  unsupported("const f = (o: { m: () => number } | undefined): number | undefined => o?.m();");
  unsupported("const f = (o: { s: string } | undefined): string | undefined => o?.s.toUpperCase();");
  unsupported("const g = (xs: number[] | undefined): number[] | undefined => xs?.map((x: number) => x + 1);");
  unsupported("const h = (o: { xs: number[] } | undefined): number[] | undefined => o?.xs.slice(1);");
});

// HC-32: a direct call that omits an argument gets the parameter's literal default, or (void) for a
// bare `x?:`, so every direct call to it passes every formal. A call with too few arguments is one the
// analysis drops as an arity error, so it must never reach the IR.
test("a direct call fills an omitted default or optional argument at the call site", () => {
  assert.equal(
    lowered("function go(n: number, acc = 0): number { if (n <= 0) return acc; return go(n - 1, acc + n); } go(3);"),
    "(define (js.go js.n js.acc) (if (<= js.n 0) js.acc (js.go (- js.n 1) (js.%+ js.acc js.n)))) (js.go 3 0)",
  );
  assert.equal(
    lowered("function f(a: number, b?: number): number { return b ?? a; } f(1); f(1, 2);"),
    "(define (js.f js.a js.b) (or js.b js.a)) (js.f 1 (void)) (js.f 1 2)",
  );
  assert.equal(
    lowered('const j = (s: string, sep = ",", up = false, z: string | null = null, k = -1): string => s + sep; j("a"); j("a", ";", true);'),
    '(define js.j (lambda (js.s js.sep js.up js.z js.k) (js.%+ js.s js.sep))) (js.j "a" "," #f js.null (- 1)) (js.j "a" ";" #t js.null (- 1))',
  );
});

test("a default must be a literal", () => {
  unsupported("function f(n: number, m = n): number { return m; } f(1);");
  unsupported("function f(xs: number[], n = xs.length): number { return n; } f([1]);");
  unsupported("function f(o = { a: 1 }): number { return o.a; } f();");
});

test("an argument at a defaulted position may not admit undefined", () => {
  unsupported("function f(a = 0): number { return a; } function g(x?: number): number { return f(x); } g(1);");
  unsupported("function f(a = 0): number { return a; } function g(x: number | undefined): number { return f(x); } g(1);");
  unsupported("function f(a = 0): number { return a; } function g(x: unknown): number { return typeof x === \"number\" ? f(1) : f(undefined); } g(1);");
  // An optional position without a default takes undefined as it is.
  assert.equal(
    lowered("function f(a?: number): number { return a ?? 0; } function g(x?: number): number { return f(x); } g(1);"),
    "(define (js.f js.a) (or js.a 0)) (define (js.g js.x) (js.f js.x)) (js.g 1)",
  );
});

test("a function with a default or optional parameter is named only as the callee of a direct call", () => {
  unsupported("function f(x: number, i = 0): number { return x + i; } [1].map(f);");
  unsupported("function f(x: number, i?: number): number { return x; } const h = f; h(1);");
  unsupported("function f(x: number, i = 0): number { return x; } const o = { f }; console.log(o);");
  unsupported("function ap(g: (n: number) => number): number { return g(1); } function f(x: number, i = 0): number { return x; } ap(f);");
  unsupported("const f = (x: number, i = 0): number => x; console.log((f)(1));");
  unsupported("let f = (x: number, i = 0): number => x; f(1);");
  unsupported("[1, 2].map((x: number, i = 0) => x + i);");
  unsupported("function f(x: number, i = 0): number { return x; } const xs: [number] = [1]; f(...xs);");
});

test("a tool's optional parameter is not filled in, since a tool is a free name", () => {
  const { ir, violations } = lowerTypeScript("fetchPage(1);", {
    toolDeclarations: "declare function fetchPage(n: number, page?: number): Promise<number>;",
  });
  assert.deepEqual(violations, []);
  assert.equal(ir.map(write).join(" "), "(js.fetchPage 1)");
});

test("rest parameters and destructured defaults stay unsupported", () => {
  unsupported("function f(...xs: number[]): number { return xs.length; } f(1);");
  unsupported("function f({ a }: { a: number } = { a: 1 }): number { return a; } f();");
});

// HC-33: a field of a local const object literal may be assigned, as a statement, under a literal
// key. The write is the free call js.%put, so the analysis never reads the field as a stable value.
test("assigning to a field of a local object lowers to js.%put", () => {
  assert.equal(
    lowered("function f(): number { const o = { n: 0 }; o.n = 1; return o.n; } f();"),
    '(define (js.f) (letrec* ((js.o%1 (vector "n" 0))) (begin (js.%put js.o%1 "n" 1) (vector-ref js.o%1 "n")))) (js.f)',
  );
  assert.equal(
    lowered('const o = { n: 0, s: "" }; o["s"] = "x"; console.log(o.s);'),
    '(define js.o (vector "n" 0 "s" "")) (js.%put js.o "s" "x") (js.console.log (vector-ref js.o "s"))',
  );
});

test("a field assignment is refused outside the pushable()-style alias rules", () => {
  // Not a const bound to an object literal in the same function.
  unsupported("function f(o: { n: number }): number { o.n = 1; return o.n; } f({ n: 0 });");
  unsupported("function f(): number { let o = { n: 0 }; o.n = 1; return o.n; } f();");
  unsupported("function f(): number { const o = { n: 0 }; const g = (): void => { o.n = 1; }; g(); return o.n; } f();");
  unsupported("function f(): number { const o = { a: { n: 0 } }; o.a.n = 1; return o.a.n; } f();");
  // Only as a statement, and only with =.
  unsupported("function f(): number { const o = { n: 0 }; return (o.n = 1); } f();");
  unsupported("function f(): number { const o = { n: 0 }; o.n += 1; return o.n; } f();");
  // An alias the analysis cannot follow, a free call included.
  unsupported('const o = { n: 0 }; o.n = 1; console.log(o);');
  unsupported("function f(): number { const o = { n: 0 }; const p = o; o.n = 1; return p.n; } f();");
  unsupported("function g(o: { n: number }): number { return o.n; } function f(): number { const o = { n: 0 }; o.n = 1; return g(o); } f();");
  unsupported("function f(): { o: { n: number } } { const o = { n: 0 }; o.n = 1; return { o }; } f();");
  // A stored function, or a value that could hold one.
  unsupported("function f(): number { const o = { h: (): number => 0 }; o.h = (): number => 1; return 0; } f();");
  unsupported("function f(): number { const o = { h: { g: (): number => 0 } }; o.h = { g: (): number => 1 }; return 0; } f();");
  unsupported("function f(x: unknown): number { const o: { v: unknown } = { v: 0 }; o.v = x; return 0; } f(1);");
});

test("String.prototype.replace lowers as a free method call (HC-34)", () => {
  assert.equal(
    lowered('const f = (s: string): string => s.replace("a", "b");'),
    '(define js.f (lambda (js.s) (js.method.replace js.s "a" "b")))',
  );
});
