// The package root. It works without the AI SDK; createCheckedCodeTool() is under
// "harness-checker/ai-sdk" because `ai` is an optional peer dependency.

export { checkTypeScript, lowerTypeScript, type CheckOptions, type CheckResult } from "./check.ts";
export type { Violation, ViolationKind } from "./violation.ts";
export { formatViolations } from "./format.ts";
export { toolDeclarations, schemaToType, type JsonSchema, type ToolSchema } from "./tool-decls.ts";
export { runProgram, transpile, type RunOptions, type RunResult, type ToolFunction } from "./run.ts";
