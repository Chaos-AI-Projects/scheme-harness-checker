import { test } from "node:test";
import assert from "node:assert/strict";
import { generateText, jsonSchema, stepCountIs, tool } from "ai";
import { MockLanguageModelV4 } from "ai/test";
import { z } from "zod";
import { createCheckedCodeTool, type CodeToolResult } from "../src/ai-sdk.ts";

const usage = {
  inputTokens: { total: 1, noCache: 1, cacheRead: undefined, cacheWrite: undefined },
  outputTokens: { total: 1, text: 1, reasoning: undefined },
};

const callCode = (id: string, code: string) => ({
  content: [{ type: "tool-call" as const, toolCallId: id, toolName: "runCode", input: JSON.stringify({ code }) }],
  finishReason: { unified: "tool-calls" as const, raw: undefined },
  usage,
  warnings: [],
});

const stop = (text: string) => ({
  content: [{ type: "text" as const, text }],
  finishReason: { unified: "stop" as const, raw: undefined },
  usage,
  warnings: [],
});

function weatherTool(calls: unknown[]) {
  return tool({
    description: "Current weather for a city",
    inputSchema: z.object({ city: z.string() }),
    outputSchema: z.object({ tempC: z.number() }),
    execute: async ({ city }) => { calls.push({ city }); return { tempC: city.length }; },
  });
}

test("generateText drives the code tool through a violation, a repair and a clean run", async () => {
  const calls: unknown[] = [];
  const runCode = await createCheckedCodeTool({ tools: { getWeather: weatherTool(calls) } });
  const model = new MockLanguageModelV4({
    doGenerate: [
      callCode("c1", `globalThis.process;`),
      callCode("c2", `async function main() { const w = await getWeather({ city: "Sydney" }); return w.tempC; } main();`),
      stop("done"),
    ],
  });

  const result = await generateText({ model, prompt: "weather?", tools: { runCode }, stopWhen: stepCountIs(5) });

  const outputs = result.steps.flatMap((s) => s.toolResults.map((r) => r.output as CodeToolResult));
  assert.equal(outputs.length, 2);
  assert.equal(outputs[0]!.status, "violation");
  assert.match((outputs[0] as { message: string }).message, /^VIOLATION: .*globalThis/);
  assert.deepEqual(outputs[1], { status: "ok", value: 6, logs: [] });
  assert.deepEqual(calls, [{ city: "Sydney" }]);
  assert.equal(result.text, "done");
});

test("the tool's description declares the app's tools as async functions", async () => {
  const runCode = await createCheckedCodeTool({ tools: { getWeather: weatherTool([]) } });
  assert.match(String(runCode.description), /declare function getWeather\(args: \{ city: string \}\): Promise<\{ tempC: number \}>;/);
});

test("a call the checker rejects never reaches a tool", async () => {
  const calls: unknown[] = [];
  const runCode = await createCheckedCodeTool({ tools: { getWeather: weatherTool(calls) } });
  const r = await runCode.execute!({ code: `while (true) { getWeather({ city: "x" }); }` }, { toolCallId: "t", messages: [] } as never);
  assert.equal((r as CodeToolResult).status, "violation");
  assert.deepEqual(calls, []);
});

test("arguments are validated against the tool's input schema at run time", async () => {
  // The declaration says string; the schema's min(3) is invisible to the type check.
  const calls: unknown[] = [];
  const shortName = tool({
    inputSchema: z.object({ city: z.string().min(3) }),
    execute: async ({ city }) => { calls.push(city); return city; },
  });
  const runCode = await createCheckedCodeTool({ tools: { shortName } });
  const code = `async function main() {
    try { await shortName({ city: "ab" }); return "ran"; } catch (e) { return "rejected"; }
  } main();`;
  const r = await runCode.execute!({ code }, { toolCallId: "t", messages: [] } as never);
  assert.deepEqual(r, { status: "ok", value: "rejected", logs: [] });
  assert.deepEqual(calls, []);
});

test("a runtime error comes back as an error result with the logs so far", async () => {
  const fail = tool({ inputSchema: z.object({}), execute: async (): Promise<string> => { throw new Error("empty"); } });
  const runCode = await createCheckedCodeTool({ tools: { fail } });
  const code = `async function main() { console.log("before"); return await fail({}); } main();`;
  const r = await runCode.execute!({ code }, { toolCallId: "t", messages: [] } as never);
  assert.deepEqual(r, { status: "error", error: "Error: empty", logs: ["before"] });
});

test("plain JSON schemas work, including ones whose JSON Schema resolves asynchronously", async () => {
  const lookup = tool({
    inputSchema: jsonSchema<{ id: number }>(async () => ({
      type: "object", properties: { id: { type: "number" } }, required: ["id"],
    })),
    execute: async ({ id }) => id * 2,
  });
  const runCode = await createCheckedCodeTool({ tools: { lookup } });
  assert.match(String(runCode.description), /declare function lookup\(args: \{ id: number \}\): Promise<unknown>;/);
  const r = await runCode.execute!({ code: `async function main() { return await lookup({ id: 21 }); } main();` },
    { toolCallId: "t", messages: [] } as never);
  assert.deepEqual(r, { status: "ok", value: 42, logs: [] });
});

test("a tool without execute is refused when the code tool is created", async () => {
  const clientSide = tool({ inputSchema: z.object({ q: z.string() }) });
  await assert.rejects(createCheckedCodeTool({ tools: { clientSide } }), /clientSide.*execute/);
});

test("a tool named after a global is refused when the code tool is created", async () => {
  const shadow = tool({ inputSchema: z.object({}), execute: async () => 1 });
  await assert.rejects(createCheckedCodeTool({ tools: { JSON: shadow } }), /Duplicate identifier 'JSON'/);
});

test("an app tool's abortSignal fires when the program's run ends", async () => {
  const signals: (AbortSignal | undefined)[] = [];
  const hang = tool({
    inputSchema: z.object({}),
    execute: async (_args, { abortSignal }) => { signals.push(abortSignal); return new Promise<number>(() => {}); },
  });
  const runCode = await createCheckedCodeTool({ tools: { hang } });
  const model = new MockLanguageModelV4({ doGenerate: [callCode("c1", `hang({}); 1;`), stop("done")] });
  const result = await generateText({ model, prompt: "go", tools: { runCode }, stopWhen: stepCountIs(3) });
  const output = result.steps.flatMap((s) => s.toolResults.map((r) => r.output))[0];
  assert.deepEqual(output, { status: "ok", value: 1, logs: [] });
  assert.equal(signals.length, 1);
  assert.equal(signals[0]?.aborted, true);
});
