// The executor for checked programs: QuickJS compiled to WebAssembly, one fresh runtime per run,
// holding the standard builtins plus only the globals injected here. Node's own `vm` module is not
// a security boundary, so it is not used. The checker is the gate; this realm is the layer a bypass
// of the gate still meets.
//
// Tools are async host functions. Values cross the boundary as JSON in both directions, so the
// program never holds a host reference. The time budget is a wall-clock deadline: the interrupt
// handler enforces it while QuickJS runs, and a timer enforces it while the program awaits a tool.

import {
  newQuickJSWASMModule,
  shouldInterruptAfterDeadline,
  type QuickJSDeferredPromise,
  type QuickJSHandle,
  type QuickJSWASMModule,
} from "quickjs-emscripten";
import ts from "typescript";

/** A tool. Its signal aborts when the run ends, so work the program left behind can stop. */
export type ToolFunction = (args: unknown, options: { signal: AbortSignal }) => Promise<unknown> | unknown;

export interface RunOptions {
  /** The program's tools, by the names its `declare function` lines use. */
  tools?: Record<string, ToolFunction>;
  /** Wall-clock budget for the whole run, tool calls included. Default 5000. */
  timeoutMs?: number;
  /** Heap limit for the QuickJS runtime. Default 64 MiB. */
  memoryLimitBytes?: number;
}

export type RunResult =
  | { ok: true; value: unknown; logs: string[] }
  | { ok: false; error: string; logs: string[] };

const DEFAULT_TIMEOUT_MS = 5000;
const DEFAULT_MEMORY_LIMIT = 64 * 1024 * 1024;
// Below the WebAssembly stack, so QuickJS reports an overflow before the host stack does. At 512
// KiB and above, unbounded recursion overflowed the host stack or aborted runtime disposal.
const MAX_STACK_BYTES = 256 * 1024;
// Host-side limits. QuickJS polls its interrupt handler only every few thousand ticks, so a program
// spending its time in host calls would otherwise run, and allocate, unchecked by the budget.
const MAX_LOG_CHARS = 64 * 1024;
const MAX_TOOL_CALLS = 1000;
const MAX_TOOL_CALLS_IN_FLIGHT = 64;
// Tool arguments are serialised inside the realm and measured there, so the host copies out at most
// this many characters of them across the whole run.
const MAX_TOOL_ARG_CHARS = 8 * 1024 * 1024;

// A module of our own rather than getQuickJS()'s shared one, so that if disposal ever aborts the
// WebAssembly instance, only this module is dropped and the next run loads a fresh one.
let quickjsModule: Promise<QuickJSWASMModule> | undefined;
const loadQuickJS = () => (quickjsModule ??= newQuickJSWASMModule());

/** Strips the types from a checked program, leaving a classic script. */
export function transpile(code: string): string {
  return ts.transpileModule(code, {
    compilerOptions: {
      target: ts.ScriptTarget.ES2022,
      module: ts.ModuleKind.ESNext,
      moduleDetection: ts.ModuleDetectionKind.Legacy,
      removeComments: true,
    },
  }).outputText;
}

/**
 * Runs a TypeScript program the checker accepted. The result is the program's completion value,
 * awaited when it is a promise, so a program ending in `main();` returns what `main` resolves to.
 */
export async function runProgram(code: string, options: RunOptions = {}): Promise<RunResult> {
  const timeoutMs = options.timeoutMs ?? DEFAULT_TIMEOUT_MS;
  const deadline = Date.now() + timeoutMs;
  const quickjs = await loadQuickJS();
  const runtime = quickjs.newRuntime();
  runtime.setMemoryLimit(options.memoryLimitBytes ?? DEFAULT_MEMORY_LIMIT);
  runtime.setMaxStackSize(MAX_STACK_BYTES);
  runtime.setInterruptHandler(shouldInterruptAfterDeadline(deadline));
  const context = runtime.newContext();

  const logs: string[] = [];
  let logChars = 0;
  let toolCalls = 0;
  let toolArgChars = 0;
  const aborter = new AbortController();
  const deferreds = new Set<QuickJSDeferredPromise>();
  const inflight = new Set<Promise<void>>();
  let disposed = false;
  const overBudget = () => `the program exceeded its time budget of ${timeoutMs} ms`;
  // Called first in every host function: past the deadline the program gets an exception instead
  // of more host work, and its next interrupt poll ends the run.
  const checkDeadline = () => {
    if (Date.now() >= deadline) throw new Error(overBudget());
  };
  const fail = (error: string): RunResult => ({ ok: false, error, logs });

  // Captured before the program runs, so the program cannot replace the parser tool results use, or
  // the serialiser tool arguments and logged values go through.
  const [parse, stringify] = context.getProp(context.global, "JSON").consume((json) =>
    [context.getProp(json, "parse"), context.getProp(json, "stringify")]);
  // Likewise String.prototype.slice, which shortens a long log argument before it leaves the realm.
  const slice = context.getProp(context.global, "String").consume((string) =>
    context.getProp(string, "prototype").consume((proto) => context.getProp(proto, "slice")));

  const toHandle = (value: unknown): QuickJSHandle => {
    const text = JSON.stringify(value);
    if (text === undefined) return context.undefined;
    const result = context.newString(text).consume((s) => context.callFunction(parse, context.undefined, s));
    return context.unwrapResult(result);
  };

  const outcome = await (async (): Promise<RunResult> => {
    try {
      const consoleObject = context.newObject();
      // Arguments are copied out one at a time, each shortened to the room left under the cap, so
      // one call passing the same long string many times copies no more than the cap.
      context.newFunction("log", (...args) => {
        checkDeadline();
        if (logChars >= MAX_LOG_CHARS) return;
        const parts: string[] = [];
        let room = MAX_LOG_CHARS - logChars;
        for (const arg of args) {
          if (room <= 0) break;
          checkDeadline();
          const part = truncate(dumpLogArg(arg, room), room);
          parts.push(part);
          room -= part.length + 1;
        }
        const line = parts.join(" ");
        logs.push(line);
        logChars += line.length + 1;
        if (room <= 0 || logChars >= MAX_LOG_CHARS) {
          logChars = MAX_LOG_CHARS;
          logs.push(`[console.log output truncated at ${MAX_LOG_CHARS} characters]`);
        }
      }).consume((log) => context.setProp(consoleObject, "log", log));
      context.setProp(context.global, "console", consoleObject);
      consoleObject.dispose();

      for (const [name, fn] of Object.entries(options.tools ?? {})) {
        context.newFunction(name, (argHandle) => {
          checkDeadline();
          if (inflight.size >= MAX_TOOL_CALLS_IN_FLIGHT) {
            throw new Error(`more than ${MAX_TOOL_CALLS_IN_FLIGHT} tool calls in flight`);
          }
          if (++toolCalls > MAX_TOOL_CALLS) throw new Error(`more than ${MAX_TOOL_CALLS} tool calls in one run`);
          const args = argHandle === undefined ? undefined : toolArgs(argHandle);
          const deferred = context.newPromise();
          deferreds.add(deferred);
          // Settling can itself fail, as when the realm is out of memory. The run then ends on its own
          // error, so a failure here is dropped rather than left as an unhandled rejection.
          const settle = (outcome: () => void) => {
            if (disposed || !deferred.alive) return;
            try {
              outcome();
            } catch {
              // See above.
            } finally {
              deferreds.delete(deferred);
              deferred.dispose();
            }
          };
          const call = Promise.resolve()
            .then(() => fn(args, { signal: aborter.signal }))
            .then((value) => (disposed ? undefined : toHandle(value)))
            .then(
              (handle) => {
                if (handle === undefined) return;
                settle(() => { try { deferred.resolve(handle); } finally { handle.dispose(); } });
              },
              (error: unknown) => settle(() => {
                context.newError(error instanceof Error ? error.message : String(error))
                  .consume((e) => deferred.reject(e));
              }),
            )
            .catch(() => {});
          inflight.add(call);
          void call.finally(() => inflight.delete(call));
          return deferred.handle.dup();
        }).consume((f) => context.setProp(context.global, name, f));
      }

      const evaluated = context.evalCode(transpile(code), "program.js");
      if (evaluated.error) {
        const error = evaluated.error.consume(dump);
        return fail(Date.now() >= deadline ? overBudget() : formatError(error));
      }

      // The result is read from the promise's internal state. Promise.resolve and then belong to the
      // program, which may have replaced them, so the host never calls them.
      const result = evaluated.value;
      try {
        for (;;) {
          const jobs = runtime.executePendingJobs();
          if (jobs.error) {
            const error = jobs.error.consume(dump);
            return fail(Date.now() >= deadline ? overBudget() : formatError(error));
          }
          const state = context.getPromiseState(result);
          if (state.type !== "pending") {
            const read = state.type === "fulfilled" ? { value: dumpResult(state.value, state.notAPromise) }
                                                    : { error: state.error.consume(dump) };
            if (Date.now() >= deadline) return fail(overBudget());
            return "error" in read ? fail(formatError(read.error))
                                   : { ok: true, value: read.value, logs };
          }
          await new Promise((r) => setImmediate(r));
          const remaining = deadline - Date.now();
          if (remaining <= 0) return fail(overBudget());
          // A tool that settled during the await above has already run its jobs.
          if (!isPending(result)) continue;
          if (inflight.size === 0 && !runtime.hasPendingJob()) {
            return fail("the program's result never settled");
          }
          if (inflight.size > 0 && !runtime.hasPendingJob()) {
            let timer: NodeJS.Timeout | undefined;
            await Promise.race([
              Promise.race(inflight),
              new Promise((r) => { timer = setTimeout(r, remaining); }),
            ]);
            clearTimeout(timer);
          }
        }
      } finally {
        result.dispose();
      }
    } catch (error) {
      if (Date.now() >= deadline) return fail(overBudget());
      return fail(error instanceof Error ? error.message : String(error));
    }
  })();

  disposed = true;
  aborter.abort();
  try {
    for (const d of deferreds) if (d.alive) d.dispose();
    parse.dispose();
    stringify.dispose();
    slice.dispose();
    context.dispose();
    runtime.dispose();
  } catch (error) {
    // Freeing a runtime that still holds live objects aborts the WebAssembly instance. QuickJS
    // itself leaks this way when the budget interrupts an unbounded chain of async returns. The
    // module is dropped so the next run loads a new one, and a run that had succeeded now fails.
    quickjsModule = undefined;
    if (outcome.ok) return { ok: false, error: `the QuickJS runtime could not be released: ${String(error)}`, logs };
  }
  return outcome;

  function isPending(handle: QuickJSHandle): boolean {
    const state = context.getPromiseState(handle);
    if (state.type === "fulfilled" && !state.notAPromise) state.value.dispose();
    if (state.type === "rejected") state.error.dispose();
    return state.type === "pending";
  }

  function dumpResult(handle: QuickJSHandle, notAPromise: boolean | undefined): unknown {
    // For a value that is not a promise, getPromiseState hands back the handle it was given.
    return notAPromise ? dump(handle) : handle.consume(dump);
  }

  // Serialises a value inside the realm. The handle it returns is a string, or undefined for a value
  // JSON has no text for, such as a function.
  function stringifyInRealm(handle: QuickJSHandle): QuickJSHandle {
    return context.unwrapResult(context.callFunction(stringify, context.undefined, handle));
  }

  function lengthOf(text: QuickJSHandle): number {
    return context.getProp(text, "length").consume((n) => context.getNumber(n));
  }

  // The argument's JSON text is measured against the run's budget before any of it is copied out.
  function toolArgs(handle: QuickJSHandle): unknown {
    return stringifyInRealm(handle).consume((text) => {
      if (context.typeof(text) !== "string") return undefined;
      toolArgChars += lengthOf(text);
      if (toolArgChars > MAX_TOOL_ARG_CHARS) {
        throw new Error(`tool arguments exceeded ${MAX_TOOL_ARG_CHARS} characters in one run`);
      }
      return JSON.parse(context.getString(text));
    });
  }

  // A log argument becomes text inside the realm: a string as itself, anything else as its JSON.
  // Text longer than the room left is sliced there too, before it is copied out.
  function dumpLogArg(handle: QuickJSHandle, room: number): string {
    if (context.typeof(handle) === "string") return copyText(handle, room);
    return stringifyInRealm(handle).consume((text) =>
      context.typeof(text) === "string" ? copyText(text, room) : String(dump(handle)));
  }

  function copyText(text: QuickJSHandle, room: number): string {
    if (lengthOf(text) <= room) return context.getString(text);
    const sliced = context.newNumber(0).consume((start) => context.newNumber(room).consume((end) =>
      context.callFunction(slice, text, start, end)));
    return context.unwrapResult(sliced).consume((h) => context.getString(h));
  }

  // context.dump disposes a promise handle it is given, which double-frees a handle its owner
  // disposes later. It is given a duplicate instead.
  function dump(handle: QuickJSHandle): unknown {
    const copy = handle.dup();
    try {
      return context.dump(copy);
    } finally {
      if (copy.alive) copy.dispose();
    }
  }
}

/** Cuts text to at most `max` UTF-16 units without leaving half a surrogate pair at the end. */
function truncate(text: string, max: number): string {
  if (text.length <= max) return text;
  const cut = text.slice(0, max);
  return /[\uD800-\uDBFF]$/.test(cut) ? cut.slice(0, -1) : cut;
}

function formatError(error: unknown): string {
  if (typeof error === "object" && error !== null && "message" in error) {
    const e = error as { name?: unknown; message?: unknown };
    return e.name ? `${String(e.name)}: ${String(e.message)}` : String(e.message);
  }
  return typeof error === "string" ? error : JSON.stringify(error) ?? String(error);
}
