import type { TerminationKind } from "./termination/violation.ts";

// The front-end's own kinds, then termination's, reported under the names termination.ss uses.
export type ViolationKind =
  | "unsupported-syntax"
  | "not-whitelisted"
  | "forbidden-member"
  | "any-type"
  | "cast"
  | "ts-directive"
  | "computed-access"
  | "type-error"
  | TerminationKind;

export interface Violation {
  kind: ViolationKind;
  message: string;
  /** 1-based line in the checked program. */
  line: number;
  /** 1-based column in the checked program. */
  column: number;
}
