import type { Violation } from "./violation.ts";

/** One `VIOLATION:` line per finding, the shape scheme-agent's models already repair against. */
export function formatViolations(violations: Violation[]): string {
  return violations.map((v) => `VIOLATION: line ${v.line}:${v.column} ${v.kind}: ${v.message}`).join("\n");
}
