// JSON Schema to `declare function` lines: the TypeScript form of the Scheme checker's
// --tool-schemas. Each tool becomes an async function taking its input object and resolving to its
// output. A schema that says nothing, or uses a keyword this file does not read, becomes `unknown`
// and never `any`, so the program must narrow a value before it can use it.

import ts from "typescript";
import { ALWAYS_FORBIDDEN } from "./names.ts";

export type JsonSchema = boolean | { [key: string]: unknown } | undefined;

export interface ToolSchema {
  description?: string;
  inputSchema: JsonSchema;
  outputSchema?: JsonSchema;
}

export function toolDeclarations(tools: Record<string, ToolSchema>): string {
  const lines: string[] = [];
  for (const [name, tool] of Object.entries(tools)) {
    assertToolName(name);
    if (tool.description) lines.push(`/** ${tool.description.replace(/\*\//g, "* /").replace(/\s+/g, " ").trim()} */`);
    const output = tool.outputSchema === undefined ? "unknown" : schemaToType(tool.outputSchema);
    lines.push(`declare function ${name}(args: ${schemaToType(tool.inputSchema)}): Promise<${output}>;`);
  }
  return lines.join("\n") + "\n";
}

function assertToolName(name: string): void {
  const scanner = ts.createScanner(ts.ScriptTarget.ES2022, true, ts.LanguageVariant.Standard, name);
  const plain = /^[A-Za-z_$][\w$]*$/.test(name) && scanner.scan() === ts.SyntaxKind.Identifier &&
    scanner.scan() === ts.SyntaxKind.EndOfFileToken;
  if (!plain || ALWAYS_FORBIDDEN.has(name)) {
    throw new Error(`harness-checker: tool name ${JSON.stringify(name)} is not a plain identifier`);
  }
  // Programs are told to end with `main();`, so a tool by that name would clash with their own.
  if (name === "main") throw new Error(`harness-checker: tool name "main" is reserved for the program`);
}

export function schemaToType(schema: JsonSchema): string {
  if (typeof schema !== "object" || schema === null) return "unknown";
  const s = schema as Record<string, unknown>;
  if ("const" in s) return literal(s.const);
  if (Array.isArray(s.enum)) return union(s.enum.map(literal));
  if (Array.isArray(s.anyOf)) return union(s.anyOf.map((m) => schemaToType(m as JsonSchema)));
  if (Array.isArray(s.oneOf)) return union(s.oneOf.map((m) => schemaToType(m as JsonSchema)));
  if (Array.isArray(s.allOf)) {
    return s.allOf.length === 0 ? "unknown" : s.allOf.map((m) => `(${schemaToType(m as JsonSchema)})`).join(" & ");
  }
  if (Array.isArray(s.type)) return union(s.type.map((t) => schemaToType({ ...s, type: t })));
  switch (s.type) {
    case "string": return "string";
    case "number":
    case "integer": return "number";
    case "boolean": return "boolean";
    case "null": return "null";
    case "array": return arrayType(s.items);
    case "object": return objectType(s);
    default: return "unknown";
  }
}

function arrayType(items: unknown): string {
  if (typeof items !== "object" || items === null || Array.isArray(items)) return "unknown[]";
  const element = schemaToType(items as JsonSchema);
  return /^[\w$]+(\[\])*$/.test(element) ? `${element}[]` : `(${element})[]`;
}

function objectType(s: Record<string, unknown>): string {
  const props = s.properties;
  if (typeof props !== "object" || props === null) {
    const extra = s.additionalProperties;
    const value = typeof extra === "object" && extra !== null ? schemaToType(extra as JsonSchema) : "unknown";
    return `{ [key: string]: ${value} }`;
  }
  const required = new Set(Array.isArray(s.required) ? s.required : []);
  const fields = Object.entries(props as Record<string, JsonSchema>).map(([key, value]) => {
    const name = /^[A-Za-z_$][\w$]*$/.test(key) ? key : JSON.stringify(key);
    return `${name}${required.has(key) ? "" : "?"}: ${schemaToType(value)}`;
  });
  return fields.length === 0 ? "{}" : `{ ${fields.join("; ")} }`;
}

function literal(value: unknown): string {
  if (value === null) return "null";
  if (typeof value === "string" || typeof value === "boolean") return JSON.stringify(value);
  if (typeof value === "number" && Number.isFinite(value)) return String(value);
  return "unknown";
}

function union(members: string[]): string {
  const unique = [...new Set(members)];
  if (unique.length === 0) return "never";
  return unique.includes("unknown") ? "unknown" : unique.join(" | ");
}
