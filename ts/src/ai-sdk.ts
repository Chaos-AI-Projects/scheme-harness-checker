// createCheckedCodeTool(): the Vercel AI SDK adapter. It returns one tool taking `{ code }`. Its
// execute runs the checker first; a violation goes back to the model as text so it can repair the
// program, as scheme-agent's execute_scheme_code does. A clean program runs in the QuickJS
// executor with the app's other tools exposed as async functions, each forwarding to that tool's
// own execute after validating its argument against the tool's input schema.
//
// This is the only file that imports `ai`, which is an optional peer dependency, so the checker and
// the executor work without the SDK.

import { asSchema, jsonSchema, tool, type Tool, type ToolExecutionOptions } from "ai";
import { checkTypeScript, type Violation } from "./check.ts";
import { runProgram, type ToolFunction } from "./run.ts";
import { toolDeclarations, type JsonSchema, type ToolSchema } from "./tool-decls.ts";

export interface CheckedCodeToolOptions {
  /** The app's tools, which the program may call. Each needs an `execute`. */
  tools: Record<string, Tool<any, any>>;
  /** Replaces the default first paragraph of the tool's description. */
  description?: string;
  /** Wall-clock budget for one run, tool calls included. Default 5000. */
  timeoutMs?: number;
  /** Heap limit for the QuickJS runtime. Default 64 MiB. */
  memoryLimitBytes?: number;
}

export type CodeToolResult =
  | { status: "ok"; value: unknown; logs: string[] }
  | { status: "violation"; message: string }
  | { status: "error"; error: string; logs: string[] };

const DEFAULT_DESCRIPTION =
  "Runs a TypeScript program that calls the tools declared below. The program is checked before it " +
  "runs: only the declared functions and safe builtins are available, `any` and `as` casts are " +
  "refused, and every loop and recursion must visibly terminate. A rejected program comes back as " +
  "VIOLATION lines to fix. The result is the program's completion value, so end with an expression " +
  "such as `main();`, where `main` is an async function returning the answer.";

/**
 * Builds the checked code tool. Async because a tool's JSON Schema may resolve asynchronously,
 * and the declarations go into the description the model sees.
 */
export async function createCheckedCodeTool(options: CheckedCodeToolOptions) {
  const schemas: Record<string, ToolSchema> = {};
  const functions: Record<string, (args: unknown, execOptions: ToolExecutionOptions<unknown>) => Promise<unknown>> = {};
  for (const [name, t] of Object.entries(options.tools)) {
    const execute = t.execute;
    if (typeof execute !== "function") {
      throw new Error(`harness-checker: tool ${JSON.stringify(name)} has no execute, so a program cannot call it`);
    }
    const input = asSchema(t.inputSchema);
    schemas[name] = {
      // A description computed from the call's context has no fixed text to declare.
      description: typeof t.description === "string" ? t.description : undefined,
      inputSchema: (await input.jsonSchema) as JsonSchema,
      outputSchema: t.outputSchema === undefined ? undefined : (await asSchema(t.outputSchema).jsonSchema) as JsonSchema,
    };
    functions[name] = async (args, execOptions) => {
      let value = args;
      if (input.validate) {
        const checked = await input.validate(args);
        if (!checked.success) throw new Error(`invalid arguments for ${name}: ${checked.error.message}`);
        value = checked.value;
      }
      return lastValue(await execute.call(t, value, execOptions));
    };
  }
  const declarations = toolDeclarations(schemas);
  // Compiling the declarations once here refuses a tool that shadows a global, such as `JSON`.
  checkTypeScript("0;", { toolDeclarations: declarations });

  return tool({
    description: `${options.description ?? DEFAULT_DESCRIPTION}\n\n${declarations}`,
    inputSchema: jsonSchema<{ code: string }>({
      type: "object",
      properties: { code: { type: "string", description: "The TypeScript program" } },
      required: ["code"],
      additionalProperties: false,
    }),
    execute: async ({ code }, execOptions): Promise<CodeToolResult> => {
      const checked = checkTypeScript(code, { toolDeclarations: declarations });
      if (!checked.ok) return { status: "violation", message: formatViolations(checked.violations) };
      const tools: Record<string, ToolFunction> = {};
      for (const [name, fn] of Object.entries(functions)) {
        // The app tool sees the run's own signal as well as the model call's, so a call the program
        // left behind can stop once the run ends.
        tools[name] = (args, { signal }) => fn(args, {
          ...execOptions,
          abortSignal: execOptions.abortSignal ? AbortSignal.any([execOptions.abortSignal, signal]) : signal,
        });
      }
      const run = await runProgram(code, {
        tools,
        timeoutMs: options.timeoutMs,
        memoryLimitBytes: options.memoryLimitBytes,
      });
      return run.ok ? { status: "ok", value: run.value, logs: run.logs }
                    : { status: "error", error: run.error, logs: run.logs };
    },
  });
}

/** One `VIOLATION:` line per finding, the shape scheme-agent's models already repair against. */
export function formatViolations(violations: Violation[]): string {
  return violations.map((v) => `VIOLATION: line ${v.line}:${v.column} ${v.kind}: ${v.message}`).join("\n");
}

// A streaming execute yields preliminary outputs; the last one is the result.
async function lastValue(output: unknown): Promise<unknown> {
  if (typeof output !== "object" || output === null || !(Symbol.asyncIterator in output)) return output;
  let last: unknown;
  for await (const item of output as AsyncIterable<unknown>) last = item;
  return last;
}
