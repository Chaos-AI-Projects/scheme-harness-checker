#!/usr/bin/env node
// harness-checker-ts: checkTypeScript() on one file, with the Scheme main.ss exit codes, 0 for a
// clean program and 1 for violations. A usage or input error exits 2, so a caller gating on 1
// never mistakes a missing file for a rejected program.

import { readFileSync } from "node:fs";
import { formatViolations } from "./format.ts";
import { checkTypeScript, type CheckResult } from "./check.ts";
import { toolDeclarations, type ToolSchema } from "./tool-decls.ts";

const USAGE = `usage: harness-checker-ts [--tool-schemas <tools.json>] <program.ts | ->

Checks a TypeScript tool-calling program. "-" reads it from stdin.
--tool-schemas  JSON object mapping each tool name to
                {"description"?, "inputSchema", "outputSchema"?} as JSON Schema.
Exit codes: 0 no violations, 1 violations, 2 usage or input error.`;

class UsageError extends Error {}

function parseArgs(argv: string[]): { file: string; schemas?: string } | "help" {
  let file: string | undefined;
  let schemas: string | undefined;
  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (arg === "--help" || arg === "-h") return "help";
    if (arg === "--tool-schemas") {
      schemas = argv[++i];
      if (schemas === undefined) throw new UsageError("--tool-schemas needs a path");
    } else if (arg.startsWith("-") && arg !== "-") {
      throw new UsageError(`unknown option ${arg}`);
    } else if (file !== undefined) {
      throw new UsageError("expected exactly one program file");
    } else {
      file = arg;
    }
  }
  if (file === undefined) throw new UsageError("expected exactly one program file");
  return { file, schemas };
}

function main(argv: string[]): number {
  let args: ReturnType<typeof parseArgs>;
  try {
    args = parseArgs(argv);
  } catch (e) {
    if (!(e instanceof UsageError)) throw e;
    process.stderr.write(`harness-checker-ts: ${e.message}\n${USAGE}\n`);
    return 2;
  }
  if (args === "help") {
    process.stdout.write(USAGE + "\n");
    return 0;
  }
  let result: CheckResult;
  try {
    const code = readFileSync(args.file === "-" ? 0 : args.file, "utf8");
    let decls: string | undefined;
    if (args.schemas !== undefined) {
      const tools = JSON.parse(readFileSync(args.schemas, "utf8")) as Record<string, ToolSchema>;
      decls = toolDeclarations(tools);
    }
    // Throws when the tool declarations do not compile on their own: a bad input, not a violation.
    result = checkTypeScript(code, { toolDeclarations: decls });
  } catch (e) {
    process.stderr.write(`harness-checker-ts: ${e instanceof Error ? e.message : String(e)}\n`);
    return 2;
  }
  if (result.ok) {
    process.stdout.write("OK: No violations found.\n");
    return 0;
  }
  process.stdout.write(`${formatViolations(result.violations)}\n${result.violations.length} violation(s) total.\n`);
  return 1;
}

process.exitCode = main(process.argv.slice(2));
