import { test } from "node:test";
import assert from "node:assert/strict";
import { runProgram, type RunResult } from "../src/run.ts";

const valueOf = (r: RunResult): unknown => (r.ok ? r.value : r.error);

test("the result is the program's completion value", async () => {
  const r = await runProgram(`const a: number = 1; a + 2;`);
  assert.deepEqual(r, { ok: true, value: 3, logs: [] });
});

test("console.log lines are captured", async () => {
  const r = await runProgram(`console.log("hi", 2, { a: [1] }); console.log("x");`);
  assert.deepEqual(r.logs, [`hi 2 {"a":[1]}`, "x"]);
});

test("a promise completion value is awaited, and tools are async host functions", async () => {
  const calls: unknown[] = [];
  const r = await runProgram(
    `async function main() { const w = await getWeather({ city: "Sydney" }); return { t: w.tempC + 1 }; } main();`,
    { tools: { getWeather: async (args) => { calls.push(args); return { tempC: 20 }; } } },
  );
  assert.deepEqual(r, { ok: true, value: { t: 21 }, logs: [] });
  assert.deepEqual(calls, [{ city: "Sydney" }]);
});

test("tool calls run concurrently under Promise.all", async () => {
  const r = await runProgram(
    `async function main() { return await Promise.all([t({ n: 1 }), t({ n: 2 })]); } main();`,
    { tools: { t: async (args) => (args as { n: number }).n * 10 } },
  );
  assert.deepEqual(valueOf(r), [10, 20]);
});

test("a tool that throws rejects inside the program, where it can be caught", async () => {
  const tools = { boom: async () => { throw new Error("no such city"); } };
  const caught = await runProgram(
    `async function main() { try { await boom({}); return "no"; } catch (e) { return "caught"; } } main();`,
    { tools },
  );
  assert.deepEqual(valueOf(caught), "caught");
  const uncaught = await runProgram(`async function main() { return await boom({}); } main();`, { tools });
  assert.equal(uncaught.ok, false);
  assert.match(uncaught.ok ? "" : uncaught.error, /no such city/);
});

test("a thrown error fails the run and keeps the logs", async () => {
  const r = await runProgram(`console.log("before"); throw new Error("bad");`);
  assert.equal(r.ok, false);
  assert.match(r.ok ? "" : r.error, /bad/);
  assert.deepEqual(r.logs, ["before"]);
});

test("a busy loop is interrupted by the time budget", async () => {
  const started = Date.now();
  const r = await runProgram(`let i = 0; while (true) { i++; }`, { timeoutMs: 200 });
  assert.equal(r.ok, false);
  assert.match(r.ok ? "" : r.error, /time budget/);
  assert.ok(Date.now() - started < 2000);
});

test("a tool that never settles is cut off by the time budget", async () => {
  const r = await runProgram(`async function main() { return await hang({}); } main();`,
                             { tools: { hang: () => new Promise(() => {}) }, timeoutMs: 200 });
  assert.equal(r.ok, false);
  assert.match(r.ok ? "" : r.error, /time budget/);
});

test("the realm holds no host globals", async () => {
  const r = await runProgram(
    `[typeof process, typeof require, typeof fetch, typeof setTimeout, typeof globalThis.os, typeof globalThis.std];`,
  );
  assert.deepEqual(valueOf(r), ["undefined", "undefined", "undefined", "undefined", "undefined", "undefined"]);
});

test("each run gets a fresh realm", async () => {
  await runProgram(`globalThis.leak = 1;`);
  const r = await runProgram(`typeof globalThis.leak;`);
  assert.equal(valueOf(r), "undefined");
});

test("tool results cross the boundary as data, not host references", async () => {
  const r = await runProgram(
    `async function main() { const v = await t({}); return [typeof v.f, Object.keys(v)]; } main();`,
    { tools: { t: async () => ({ a: 1, f: () => 1, d: new Date(0) }) } },
  );
  assert.equal(r.ok, true);
  assert.deepEqual(valueOf(r), ["undefined", ["a", "d"]]);
});

test("a tool result that is not JSON rejects inside the program", async () => {
  const circular: { self?: unknown } = {};
  circular.self = circular;
  const r = await runProgram(`async function main() { try { await t({}); return "no"; } catch (e) { return "caught"; } } main();`,
                             { tools: { t: async () => circular } });
  assert.equal(valueOf(r), "caught");
});

test("memory exhaustion fails the run instead of the host", async () => {
  const r = await runProgram(`const xs: number[][] = []; while (true) { xs.push([1, 2, 3, 4, 5, 6, 7, 8]); }`,
                             { timeoutMs: 5000, memoryLimitBytes: 16 * 1024 * 1024 });
  assert.equal(r.ok, false);
  assert.match(r.ok ? "" : r.error, /out of memory/);
  assert.deepEqual(await runProgram(`1;`), { ok: true, value: 1, logs: [] });
});

test("the memory limit bounds the bytes a program allocates, not only how many allocations it makes", async () => {
  // Each array holds 10000 eight-byte values, about 80 KB, so a 16 MiB realm fits a few hundred.
  // QuickJS here counts allocations rather than their sizes, so its own limit let this reach 2 GiB.
  const r = await runProgram(
    `const xs: number[][] = [];
     try { for (let i = 0; i < 1000000; i++) { xs.push(new Array<number>(10000).fill(i)); } } catch (e) { }
     xs.length;`,
    { memoryLimitBytes: 16 * 1024 * 1024 },
  );
  assert.equal(r.ok, true);
  assert.ok(r.ok && (r.value as number) < 1000, `allocated ${valueOf(r)} arrays of 10000 values`);
});

test("unbounded recursion fails the run, and the next run still works", async () => {
  for (let i = 0; i < 3; i++) {
    const r = await runProgram(`function f(n: number): number { return f(n + 1); } f(0);`);
    assert.equal(r.ok, false);
    assert.match(r.ok ? "" : r.error, /stack overflow/);
  }
  assert.deepEqual(await runProgram(`1;`), { ok: true, value: 1, logs: [] });
});

test("modest recursion depth still runs", async () => {
  const r = await runProgram(`function f(n: number): number { return n === 0 ? 0 : 1 + f(n - 1); } f(500);`);
  assert.deepEqual(r, { ok: true, value: 500, logs: [] });
});

// The rest of the realm belongs to the program, so how the host reads the result must not run
// anything the program can replace. These programs reach the executor only past a checker bypass.
async function withoutUnhandledRejections(body: () => Promise<void>): Promise<void> {
  const seen: unknown[] = [];
  const record = (reason: unknown) => { seen.push(reason); };
  process.on("unhandledRejection", record);
  try {
    await body();
    await new Promise((r) => setImmediate(r));
  } finally {
    process.off("unhandledRejection", record);
  }
  assert.deepEqual(seen.map(String), []);
}

test("a program that replaces Promise.prototype.then cannot reject on the host", async () => {
  await withoutUnhandledRejections(async () => {
    const r = await runProgram(`Promise.prototype.then = function () { throw new Error("x"); }; 1;`);
    assert.deepEqual(r, { ok: true, value: 1, logs: [] });
  });
});

test("a then that calls its resolver twice cannot abort runtime disposal", async () => {
  for (let i = 0; i < 20; i++) {
    const r = await runProgram(
      `Promise.prototype.then = function (a: any) { a({ x: 1 }); a({ x: 2 }); }; 1;`,
    );
    assert.deepEqual(r, { ok: true, value: 1, logs: [] });
  }
  assert.deepEqual(await runProgram(`1;`), { ok: true, value: 1, logs: [] });
});

test("an async result is read from the promise itself, not through a replaced then", async () => {
  await withoutUnhandledRejections(async () => {
    const r = await runProgram(
      `Promise.prototype.then = function () { throw new Error("x"); };
       async function main() { const v = await t({}); return v + 1; } main();`,
      { tools: { t: async () => 4 } },
    );
    assert.deepEqual(r, { ok: true, value: 5, logs: [] });
  });
});

test("a rejected async result fails the run with its error", async () => {
  const r = await runProgram(`async function main() { throw new Error("boom"); } main();`);
  assert.deepEqual(r, { ok: false, error: "Error: boom", logs: [] });
});

test("an interrupt while reading the result reports the time budget", async () => {
  const r = await runProgram(`({ toJSON() { while (true) {} } });`, { timeoutMs: 200 });
  assert.deepEqual(r, { ok: false, error: "the program exceeded its time budget of 200 ms", logs: [] });
});

test("a tool settling while the program floods the job queue fails on the budget, not on disposal", async () => {
  const r = await runProgram(
    `async function main() {
       const p = t({});
       async function spin(): Promise<void> { await null; return spin(); }
       spin();
       return await p;
     }
     main();`,
    { tools: { t: async () => 5 }, timeoutMs: 300 },
  );
  assert.deepEqual(r, { ok: false, error: "the program exceeded its time budget of 300 ms", logs: [] });
});

test("a QuickJS leak at disposal keeps the run's own error, and the next run gets a fresh module", async () => {
  // Interrupting an unbounded chain of async returns leaves objects QuickJS cannot free.
  for (let i = 0; i < 3; i++) {
    const r = await runProgram(`async function spin(): Promise<void> { await null; return spin(); } spin(); 1;`,
                               { timeoutMs: 200 });
    assert.deepEqual(r, { ok: false, error: "the program exceeded its time budget of 200 ms", logs: [] });
    assert.deepEqual(await runProgram(`1;`), { ok: true, value: 1, logs: [] });
  }
});

test("console.log output is capped, so a log flood cannot exhaust the host", async () => {
  const r = await runProgram(`const s: string = "x".repeat(100000); for (let i = 0; i < 200; i++) { console.log(s); } 1;`);
  assert.equal(r.ok, true);
  assert.ok(r.logs.join("\n").length <= 70 * 1024, `kept ${r.logs.join("\n").length} bytes of logs`);
  assert.match(r.logs.at(-1) ?? "", /console\.log output truncated at 65536 characters/);
});

test("a host call past the deadline throws, so slow host work cannot overrun the budget", async () => {
  const started = Date.now();
  const r = await runProgram(
    `const s: string = "x".repeat(1000000); for (let i = 0; i < 500; i++) { try { t({ s: s }); } catch (e) { } } 1;`,
    { tools: { t: async () => 1 }, timeoutMs: 200 },
  );
  assert.deepEqual(r, { ok: false, error: "the program exceeded its time budget of 200 ms", logs: [] });
  assert.ok(Date.now() - started < 500, `took ${Date.now() - started} ms`);
});

test("tool calls are capped per run and in flight", async () => {
  let calls = 0;
  const tools = { t: async () => { calls++; await new Promise((r) => setTimeout(r, 50)); return 1; } };
  const many = await runProgram(
    `async function main() { const ps: Promise<number>[] = []; for (let i = 0; i < 100; i++) { ps.push(t({})); } await Promise.all(ps); return 1; } main();`,
    { tools },
  );
  assert.deepEqual(many, { ok: false, error: "Error: more than 64 tool calls in flight", logs: [] });
  assert.equal(calls, 64);
  calls = 0;
  const serial = await runProgram(
    `async function main() { for (let i = 0; i < 2000; i++) { await t({}); } return 1; } main();`,
    { tools: { t: async () => { calls++; return 1; } } },
  );
  assert.deepEqual(serial, { ok: false, error: "Error: more than 1000 tool calls in one run", logs: [] });
  assert.equal(calls, 1000);
});

test("tools are handed an abort signal that fires when the run ends", async () => {
  const signals: AbortSignal[] = [];
  const r = await runProgram(`t({}); 1;`, {
    tools: { t: (_args, { signal }) => { signals.push(signal); return new Promise(() => {}); } },
  });
  assert.deepEqual(r, { ok: true, value: 1, logs: [] });
  assert.equal(signals.length, 1);
  assert.equal(signals[0]!.aborted, true);
});

test("a tool result the exhausted realm cannot hold leaves no unhandled rejection", async () => {
  await withoutUnhandledRejections(async () => {
    const r = await runProgram(
      `async function main(): Promise<number> {
         const p = t({});
         const xs: number[][] = [];
         try { for (let i = 0; i < 1000000000; i++) { xs.push(new Array<number>(10000).fill(i)); } } catch (e) { }
         try { for (let i = 0; i < 1000000000; i++) { xs.push([i]); } } catch (e) { }
         const v = await p;
         return v.length + xs.length;
       }
       main();`,
      { tools: { t: async () => "y".repeat(2_000_000) }, memoryLimitBytes: 16 * 1024 * 1024, timeoutMs: 3000 },
    );
    // The heap fills before the result arrives and main() rejects, so the run ends without copying
    // the result in. Before HC-36 the heap grew to 2 GiB, the copy wrote through null, and the suite hung.
    assert.deepEqual(r, { ok: false, error: "the program ran out of memory", logs: [] });
    await new Promise((r) => setTimeout(r, 100));
  });
});

test("a tool result copied into a full heap fails the run instead of writing through null", async () => {
  await withoutUnhandledRejections(async () => {
    // A write through null corrupts the module, which then aborts with the same result, so what tells
    // the two apart is the abort the module prints.
    const printed: string[] = [];
    const error = console.error;
    console.error = (...args: unknown[]) => { printed.push(args.map(String).join(" ")); };
    const r = await runProgram(
      `async function main(): Promise<number> {
         const p = t({});
         const xs: number[][] = [];
         try { for (let i = 0; i < 1000000000; i++) { xs.push(new Array<number>(10000).fill(i)); } } catch (e) { }
         xs.pop(); xs.pop();
         const v = await p;
         return v.length + xs.length;
       }
       main();`,
      { tools: { t: async () => "y".repeat(2_000_000) }, memoryLimitBytes: 16 * 1024 * 1024, timeoutMs: 3000 },
    ).finally(() => { console.error = error; });
    // The program frees a little room and is alive when the result arrives, so the host does copy it
    // in. The heap cannot hold 2 MB, and malloc's null once had the bindings write there (HC-36).
    assert.deepEqual(r, { ok: false, error: "the program ran out of memory", logs: [] });
    assert.deepEqual(printed.filter((line) => /Aborted/.test(line)).map((line) => line.slice(0, 40)), []);
    await new Promise((r) => setTimeout(r, 100));
  });
});

test("a program's own error is not relabelled after one of the heap's grows was refused", async () => {
  // Emscripten asks for its largest grow first and settles for a smaller one, so a refused grow
  // alone does not mean the heap is full.
  const r = await runProgram(
    `const xs: number[][] = [];
     for (let i = 0; i < 250; i++) { xs.push(new Array<number>(10000).fill(i)); }
     throw new Error("mine " + xs.length);`,
    { memoryLimitBytes: 16 * 1024 * 1024 },
  );
  assert.deepEqual(r, { ok: false, error: "Error: mine 250", logs: [] });
});

test("a program's own error is not relabelled after it filled the heap and freed it", async () => {
  const r = await runProgram(
    `let xs: number[][] = [];
     try { for (let i = 0; i < 1000000000; i++) { xs.push(new Array<number>(10000).fill(i)); } } catch (e) { }
     const filled = xs.length;
     xs = [];
     throw new Error("mine " + (filled > 0));`,
    { memoryLimitBytes: 16 * 1024 * 1024 },
  );
  assert.deepEqual(r, { ok: false, error: "Error: mine true", logs: [] });
});

test("a memory limit past the module's 2 GiB, or QuickJS's -1 for none, still runs the program", async () => {
  for (const memoryLimitBytes of [3 * 1024 ** 3, -1]) {
    const r = await runProgram(`const xs: number[] = new Array<number>(5000000).fill(1); xs.length;`, { memoryLimitBytes });
    assert.deepEqual(r, { ok: true, value: 5000000, logs: [] }, `memoryLimitBytes ${memoryLimitBytes}`);
  }
});

test("throwing or logging a promise does not double-free its handle", async () => {
  const thrown = await runProgram(`async function f(): Promise<number> { return 1; } throw f();`);
  assert.equal(thrown.ok, false);
  assert.doesNotMatch(thrown.ok ? "" : thrown.error, /Lifetime not alive/);
  const logged = await runProgram(`async function f(): Promise<number> { return 1; } console.log(f()); 2;`);
  assert.equal(logged.ok, true);
  assert.equal(logged.ok && logged.value, 2);
});

test("one console.log call with many large arguments is capped before it copies them", async () => {
  const started = Date.now();
  const args = Array.from({ length: 300 }, () => "s").join(", ");
  const r = await runProgram(`const s: string = "x".repeat(1000000); console.log(${args}); 1;`, { timeoutMs: 200 });
  assert.equal(r.ok, true);
  assert.ok(r.logs.join("\n").length <= 70 * 1024, `kept ${r.logs.join("\n").length} characters of logs`);
  assert.ok(Date.now() - started < 300, `took ${Date.now() - started} ms`);
});

test("the log cap counts characters and does not split a surrogate pair", async () => {
  const r = await runProgram(`console.log("a" + "\\u{1F600}".repeat(40000)); 1;`);
  const kept = r.logs[0] ?? "";
  assert.ok(kept.length <= 65536);
  assert.ok(!/[\uD800-\uDBFF]$/.test(kept), "ends in half a surrogate pair");
  assert.match(r.logs.at(-1) ?? "", /truncated at 65536 characters/);
});

test("tool arguments are measured in the realm and capped per run before they are copied out", async () => {
  // Each argument is 1000008 characters of JSON, so 8 calls fit under the 8 Mi budget and the 9th
  // throws before its text is copied out.
  let calls = 0;
  const started = Date.now();
  const r = await runProgram(
    `const s: string = "x".repeat(1000000);
     const ps: Promise<number>[] = [];
     for (let i = 0; i < 64; i++) { ps.push(t({ q: s })); }
     s.length;`,
    { tools: { t: async () => { calls++; return 1; } }, timeoutMs: 3000 },
  );
  assert.deepEqual(r, { ok: false, error: "Error: tool arguments exceeded 8388608 characters in one run", logs: [] });
  assert.equal(calls, 8);
  assert.ok(Date.now() - started < 1000, `took ${Date.now() - started} ms`);
});

test("a tool argument reaches the tool as JSON data", async () => {
  const seen: unknown[] = [];
  const r = await runProgram(`t({ a: [1, "x", null], b: { c: true } }); t(undefined as any); 1;`,
                             { tools: { t: (args) => { seen.push(args); return 1; } } });
  assert.deepEqual(r, { ok: true, value: 1, logs: [] });
  assert.deepEqual(seen, [{ a: [1, "x", null], b: { c: true } }, undefined]);
});

test("a non-string console.log argument is logged as its JSON, capped inside the realm", async () => {
  const small = await runProgram(`console.log({ a: [1, "x"] }, 2, null, undefined); 1;`);
  assert.deepEqual(small, { ok: true, value: 1, logs: ['{"a":[1,"x"]} 2 null undefined'] });
  const big = await runProgram(`const o = { s: "x".repeat(4000000) }; for (let i = 0; i < 50; i++) console.log(o); 1;`);
  assert.equal(big.ok, true);
  assert.equal(big.logs[0]!.length, 65536);
  assert.ok(big.logs[0]!.startsWith('{"s":"xxx'));
  assert.match(big.logs.at(-1) ?? "", /truncated at 65536 characters/);
});
