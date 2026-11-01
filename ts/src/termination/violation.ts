// The termination pass's violation record, termination.ss:64 termination-violation.

import type { Datum, Sym } from "../sexp.ts";

/** The kinds termination.ss reports. */
export type TerminationKind = "infinite-loop" | "no-base-case" | "no-decreasing-arg" | "size-change-limit";

export interface TerminationViolation {
  kind: TerminationKind;
  /** The offending function or loop name; null for a do-form. */
  function: Sym | null;
  /** The offending form, by identity. */
  expr: Datum;
  reason: string;
}
