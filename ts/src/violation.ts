export type ViolationKind =
  | "unsupported-syntax"
  | "not-whitelisted"
  | "forbidden-member"
  | "any-type"
  | "cast"
  | "ts-directive"
  | "computed-access"
  | "type-error";

export interface Violation {
  kind: ViolationKind;
  message: string;
  /** 1-based line in the checked program. */
  line: number;
  /** 1-based column in the checked program. */
  column: number;
}
