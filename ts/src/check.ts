// checkTypeScript(): the TypeScript front-end of the harness checker. It runs the subset gate,
// then compiles the program in strict mode against data/ts-safe.d.ts as the only lib, so an
// undeclared global or member is a compile error. A program that passes is lowered to the IR and the
// termination port judges that.

import { readFileSync } from "node:fs";
import ts from "typescript";
import { lower, type Lowered } from "./lower.ts";
import { declaredNames } from "./names.ts";
import { checkSubset } from "./subset.ts";
import { isSym, type Datum } from "./sexp.ts";
import { checkTermination } from "./termination/check.ts";
import type { TerminationViolation } from "./termination/violation.ts";
import type { Violation, ViolationKind } from "./violation.ts";

export type { Violation, ViolationKind } from "./violation.ts";

export interface CheckOptions {
  /** `declare function` lines for the app's tools. Trusted: errors here throw. */
  toolDeclarations?: string;
}

export interface CheckResult {
  ok: boolean;
  violations: Violation[];
}

const LIB_PATH = "/ts-safe.d.ts";
const TOOLS_PATH = "/tools.d.ts";
const PROGRAM_PATH = "/program.ts";

const COMPILER_OPTIONS: ts.CompilerOptions = {
  strict: true,
  noLib: true,
  noResolve: true,
  noEmit: true,
  types: [],
  target: ts.ScriptTarget.ES2022,
  module: ts.ModuleKind.ESNext,
  moduleDetection: ts.ModuleDetectionKind.Legacy,
  allowUnreachableCode: true,
  allowUnusedLabels: false,
};

const LIB_SOURCE = ts.createSourceFile(
  LIB_PATH,
  readFileSync(new URL("../../data/ts-safe.d.ts", import.meta.url), "utf8"),
  ts.ScriptTarget.ES2022,
  true,
);

const LIB_NAMES = declaredNames(LIB_SOURCE);
// Lib globals holding numbers are plain values; Symbol has its own rule in the subset gate.
const LIB_OBJECTS = new Set([...LIB_NAMES.values].filter((n) => !["NaN", "Infinity", "Symbol"].includes(n)));

// Undeclared names and members: the whitelist rejecting something.
const NOT_WHITELISTED = new Set([2304, 2552, 2339, 2550, 2551, 2576, 2582, 2583, 2584, 2585, 2591, 2693, 2867, 2868]);

export function checkTypeScript(code: string, options: CheckOptions = {}): CheckResult {
  return withinStack(() => {
    const gated = gate(code, options);
    if (gated.violations.length > 0) return result(gated.violations);
    const lowered = lower(gated.program, gated.checker!, numericKeys(gated.program, gated.checker!));
    if (lowered.violations.length > 0) return result(lowered.violations);
    return result(checkTermination(lowered.ir, null, { numbers: "double" }).map((v) => fromTermination(v, gated.program)));
  }, result);
}

// Each const lowers to one more nested let*, and the gate, the lowering and the termination walkers
// all recurse over that nesting (HC-26). A program nested past the stack is the program's fault, so
// it is rejected as a violation; any other throw still escapes.
function withinStack<T>(check: () => T, rejected: (violations: Violation[]) => T): T {
  try {
    return check();
  } catch (e) {
    if (!(e instanceof RangeError && /call stack/i.test(e.message))) throw e;
    return rejected([{
      kind: "unsupported-syntax",
      message: "the program nests too deeply for the checker; split long statement chains into functions",
      line: 1,
      column: 1,
    }]);
  }
}

// Lowering prefixes every user name with `js.`, which no TypeScript identifier contains, so the
// prefix comes off for the report. The violation is placed at the declaration of the function it
// names; a renamed local or a do-loop has none, and is placed at the start of the program.
function fromTermination(v: TerminationViolation, sf: ts.SourceFile): Violation {
  const unprefix = (s: string) => s.replace(/(^|[^\w$.%])js\./g, "$1");
  const fn = v.function !== null && isSym(v.function as Datum) ? unprefix(String(v.function.name)) : null;
  const at = fn === null ? undefined : declarationOf(sf, fn);
  const { line, character } = at ? sf.getLineAndCharacterOfPosition(at.getStart(sf)) : { line: 0, character: 0 };
  const message = fn === null ? unprefix(v.reason) : `${fn}: ${unprefix(v.reason)}`;
  return { kind: v.kind, message, line: line + 1, column: character + 1 };
}

function declarationOf(sf: ts.SourceFile, name: string): ts.Node | undefined {
  let found: ts.Node | undefined;
  const visit = (node: ts.Node): void => {
    if (found) return;
    if ((ts.isFunctionDeclaration(node) || ts.isVariableDeclaration(node)) &&
        node.name && ts.isIdentifier(node.name) && node.name.text === name) {
      found = node;
      return;
    }
    ts.forEachChild(node, visit);
  };
  visit(sf);
  return found;
}

/** The IR of a program that passes every gate, else the gates' violations and no IR (HC-18). */
export function lowerTypeScript(code: string, options: CheckOptions = {}): Lowered {
  return withinStack(() => {
    const gated = gate(code, options);
    if (gated.violations.length > 0) return { ir: [], violations: gated.violations };
    return lower(gated.program, gated.checker!, numericKeys(gated.program, gated.checker!));
  }, (violations) => ({ ir: [], violations }));
}

function gate(code: string, options: CheckOptions): { program: ts.SourceFile; violations: Violation[]; checker?: ts.TypeChecker } {
  const result = (violations: Violation[], checker?: ts.TypeChecker) => ({ program, violations, checker });
  const program = ts.createSourceFile(PROGRAM_PATH, code, ts.ScriptTarget.ES2022, true, ts.ScriptKind.TS);

  const syntax = (program as unknown as { parseDiagnostics: ts.Diagnostic[] }).parseDiagnostics;
  if (syntax.length > 0) return result(syntax.map((d) => fromDiagnostic(d, "unsupported-syntax")));

  const tools = ts.createSourceFile(TOOLS_PATH, options.toolDeclarations ?? "", ts.ScriptTarget.ES2022, true);
  const toolNames = declaredNames(tools);
  const subset = checkSubset(program, {
    libObjects: LIB_OBJECTS,
    reserved: new Set([...LIB_NAMES.values, ...LIB_NAMES.types, ...toolNames.values, ...toolNames.types]),
    declaredMembers: new Set([...LIB_NAMES.members, ...toolNames.members]),
  });
  if (subset.length > 0) return result(subset);

  const { tsProgram, internal } = compile(tools, program);
  if (internal.length > 0) {
    // The program can break the lib by merging with it. Blame the declarations only if they fail
    // to compile on their own.
    const alone = compile(tools, ts.createSourceFile(PROGRAM_PATH, "", ts.ScriptTarget.ES2022, true)).internal;
    if (alone.length > 0) {
      const text = alone.map((d) => ts.flattenDiagnosticMessageText(d.messageText, "\n")).join("; ");
      throw new Error(`harness-checker: lib or tool declarations do not compile: ${text}`);
    }
    return result(internal.map((d) => ({
      kind: "type-error" as const,
      message: `the program conflicts with the lib or a tool: ${ts.flattenDiagnosticMessageText(d.messageText, "\n")}`,
      line: 1,
      column: 1,
    })));
  }

  const typeErrors = tsProgram.getSemanticDiagnostics(program).map((d) =>
    fromDiagnostic(d, classify(d.code)));
  if (typeErrors.length > 0) return result(typeErrors);

  const checker = tsProgram.getTypeChecker();
  return result(checkTyped(program, checker), checker);
}

function compile(tools: ts.SourceFile, program: ts.SourceFile) {
  const files = new Map([[LIB_PATH, LIB_SOURCE], [TOOLS_PATH, tools], [PROGRAM_PATH, program]]);
  const host: ts.CompilerHost = {
    getSourceFile: (name) => files.get(name),
    getDefaultLibFileName: () => LIB_PATH,
    writeFile: () => {},
    getCurrentDirectory: () => "/",
    getCanonicalFileName: (name) => name,
    useCaseSensitiveFileNames: () => true,
    getNewLine: () => "\n",
    fileExists: (name) => files.has(name),
    readFile: () => undefined,
  };
  const tsProgram = ts.createProgram([LIB_PATH, TOOLS_PATH, PROGRAM_PATH], COMPILER_OPTIONS, host);

  const internal = [
    ...tsProgram.getGlobalDiagnostics(),
    ...tsProgram.getSemanticDiagnostics(LIB_SOURCE),
    ...tsProgram.getSyntacticDiagnostics(tools),
    ...tsProgram.getSemanticDiagnostics(tools),
  ];
  return { tsProgram, internal };
}

function classify(code: number): ViolationKind {
  if (NOT_WHITELISTED.has(code)) return "not-whitelisted";
  if (code >= 7000 && code < 8000) return "any-type";
  return "type-error";
}

const NUMERIC_BINARY = new Set<ts.SyntaxKind>([
  ts.SyntaxKind.MinusToken, ts.SyntaxKind.AsteriskToken, ts.SyntaxKind.SlashToken,
  ts.SyntaxKind.PercentToken, ts.SyntaxKind.AsteriskAsteriskToken, ts.SyntaxKind.AmpersandToken,
  ts.SyntaxKind.BarToken, ts.SyntaxKind.CaretToken, ts.SyntaxKind.LessThanLessThanToken,
  ts.SyntaxKind.GreaterThanGreaterThanToken, ts.SyntaxKind.GreaterThanGreaterThanGreaterThanToken,
]);
const NUMERIC_COMPOUND = new Set<ts.SyntaxKind>([
  ts.SyntaxKind.MinusEqualsToken, ts.SyntaxKind.AsteriskEqualsToken, ts.SyntaxKind.SlashEqualsToken,
  ts.SyntaxKind.PercentEqualsToken,
]);
const ASSIGNING = new Set<ts.SyntaxKind>([
  ts.SyntaxKind.EqualsToken, ts.SyntaxKind.PlusEqualsToken, ts.SyntaxKind.AmpersandAmpersandEqualsToken,
  ts.SyntaxKind.BarBarEqualsToken, ts.SyntaxKind.QuestionQuestionEqualsToken, ...NUMERIC_COMPOUND,
]);

// A type can say number while the value is a string: covariant arrays and method bivariance let a
// program store "constructor" where number[] is declared. So a dynamic member key is allowed only
// when it is a number at run time by construction: arithmetic that coerces, or a local variable
// whose every assignment is one.
export function numericKeys(sf: ts.SourceFile, checker: ts.TypeChecker): (key: ts.Expression) => boolean {
  // Fail closed: every occurrence of a variable in a write position is recorded. Only a whole,
  // bare target of = or a compound operator keeps its value; any other write is non-numeric.
  const writes = new Map<ts.Symbol, (ts.Expression | undefined)[]>();
  const ONE = ts.factory.createNumericLiteral(1);
  const collect = (node: ts.Node): void => {
    if (ts.isIdentifier(node)) {
      const p = node.parent;
      const sym = ts.isShorthandPropertyAssignment(p) && p.name === node
        ? checker.getShorthandAssignmentValueSymbol(p)
        : checker.getSymbolAtLocation(node);
      const value = sym && writtenValue(node, ONE);
      if (sym && value !== null) writes.set(sym, [...(writes.get(sym) ?? []), value]);
    }
    ts.forEachChild(node, collect);
  };
  collect(sf);

  const safeSymbol = (sym: ts.Symbol, seen: Set<ts.Symbol>): boolean => {
    if (seen.has(sym)) return true;
    seen.add(sym);
    const decls = sym.declarations ?? [];
    if (decls.length !== 1) return false;
    const decl = decls[0];
    if (!ts.isVariableDeclaration(decl) || !ts.isIdentifier(decl.name) || !decl.initializer) return false;
    return [decl.initializer, ...(writes.get(sym) ?? [])].every((e) => e !== undefined && numeric(e, seen));
  };
  const numeric = (e: ts.Expression, seen: Set<ts.Symbol>): boolean => {
    if (ts.isNumericLiteral(e)) return true;
    if (ts.isParenthesizedExpression(e)) return numeric(e.expression, seen);
    if (ts.isPrefixUnaryExpression(e) || ts.isPostfixUnaryExpression(e)) {
      if (e.operator === ts.SyntaxKind.ExclamationToken) return false;
      return true;
    }
    if (ts.isBinaryExpression(e)) {
      const op = e.operatorToken.kind;
      if (NUMERIC_BINARY.has(op)) return true;
      if (op === ts.SyntaxKind.PlusToken) return numeric(e.left, seen) && numeric(e.right, seen);
      return false;
    }
    if (ts.isConditionalExpression(e)) return numeric(e.whenTrue, seen) && numeric(e.whenFalse, seen);
    // Math cannot be redeclared, written through or passed as a value, so its calls return numbers.
    if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression) &&
        ts.isIdentifier(e.expression.expression) && e.expression.expression.text === "Math") return true;
    if (ts.isIdentifier(e)) {
      const sym = checker.getSymbolAtLocation(e);
      return sym !== undefined && safeSymbol(sym, seen);
    }
    return false;
  };
  return (key) => numeric(key, new Set());
}

// What an identifier occurrence writes: null for a read, undefined for a write whose value is not
// followed, else the expression the variable holds afterwards.
function writtenValue(id: ts.Identifier, numeric: ts.Expression): ts.Expression | undefined | null {
  let node: ts.Node = id;
  while (ts.isParenthesizedExpression(node.parent)) node = node.parent;
  const p = node.parent;
  if ((ts.isPrefixUnaryExpression(p) || ts.isPostfixUnaryExpression(p)) &&
      (p.operator === ts.SyntaxKind.PlusPlusToken || p.operator === ts.SyntaxKind.MinusMinusToken)) {
    return numeric;
  }
  if (ts.isBinaryExpression(p) && p.left === node && ASSIGNING.has(p.operatorToken.kind)) {
    // `[i = 5] = xs` is a default inside a pattern: i may get xs[0].
    if (inPattern(p)) return undefined;
    const kind = p.operatorToken.kind;
    if (NUMERIC_COMPOUND.has(kind)) return numeric;
    if (kind === ts.SyntaxKind.PlusEqualsToken) {
      return ts.factory.createBinaryExpression(p.left, ts.SyntaxKind.PlusToken, p.right);
    }
    return p.right;
  }
  if (ts.isForOfStatement(p) && p.initializer === node) return undefined;
  return inPattern(node) ? undefined : null;
}

// Whether a node sits inside a destructuring assignment target or a for...of target.
function inPattern(start: ts.Node): boolean {
  let up = start;
  for (;;) {
    const q = up.parent;
    if (ts.isParenthesizedExpression(q) || ts.isArrayLiteralExpression(q) || ts.isSpreadElement(q) ||
        ts.isSpreadAssignment(q) || ts.isShorthandPropertyAssignment(q) || ts.isObjectLiteralExpression(q) ||
        (ts.isPropertyAssignment(q) && q.initializer === up)) {
      up = q;
      continue;
    }
    return (ts.isBinaryExpression(q) && q.left === up && ASSIGNING.has(q.operatorToken.kind)) ||
           (ts.isForOfStatement(q) && q.initializer === up);
  }
}


// Rules that need types: no expression may have type any, however it got there; a computed member
// key must be a literal or a number by construction; for...of iterates arrays only.
function checkTyped(sf: ts.SourceFile, checker: ts.TypeChecker): Violation[] {
  const out: Violation[] = [];
  const isNumericKey = numericKeys(sf, checker);
  const report = (node: ts.Node, kind: ViolationKind, message: string) => {
    const { line, character } = sf.getLineAndCharacterOfPosition(node.getStart(sf));
    out.push({ kind, message, line: line + 1, column: character + 1 });
  };
  const visit = (node: ts.Node): void => {
    if (ts.isTypeNode(node)) return;
    if (ts.isElementAccessExpression(node)) {
      const key = node.argumentExpression;
      if (!ts.isStringLiteralLike(key) && !isNumericKey(key)) {
        report(key, "computed-access",
               "a computed member key must be a literal, arithmetic, or a local only ever assigned numbers; .at(i) takes any index");
      }
    }
    if (ts.isForOfStatement(node)) {
      const t = checker.getTypeAtLocation(node.expression);
      if (!checker.isArrayType(t) && !checker.isTupleType(t)) {
        report(node.expression, "unsupported-syntax", "for...of iterates arrays only");
      }
    }
    // A BindingElement's propertyName (`tempC` in `{ tempC: t }`) is a key, not a value, and the
    // checker gives it the error type, which carries the Any flag.
    const isBindingKey = ts.isIdentifier(node) && ts.isBindingElement(node.parent) &&
      node.parent.propertyName === node;
    if (!isBindingKey && (ts.isIdentifier(node) || ts.isCallExpression(node) ||
        ts.isPropertyAccessExpression(node) || ts.isElementAccessExpression(node) ||
        ts.isAwaitExpression(node))) {
      if (checker.getTypeAtLocation(node).flags & ts.TypeFlags.Any) {
        report(node, "any-type", `${node.getText(sf)} has type any`);
        return;
      }
    }
    ts.forEachChild(node, visit);
  };
  visit(sf);
  return out;
}

function fromDiagnostic(d: ts.Diagnostic, kind: ViolationKind): Violation {
  const { line, character } = d.file && d.start !== undefined
    ? d.file.getLineAndCharacterOfPosition(d.start)
    : { line: 0, character: 0 };
  return {
    kind,
    message: ts.flattenDiagnosticMessageText(d.messageText, "\n"),
    line: line + 1,
    column: character + 1,
  };
}

function result(violations: Violation[]): CheckResult {
  return { ok: violations.length === 0, violations };
}
