// The syntax gate. Deny by default: a node kind not listed here is unsupported-syntax, the
// TypeScript counterpart of the Scheme checker's macro ban. It also rejects the ways out of the
// type-level whitelist that exist before type checking: the any type, casts (type predicates and
// definite assignment included), ts directives, builtin member names the whitelist leaves out, lib
// globals used as values or written through, and names that shadow the lib or a tool.

import ts from "typescript";
import { ALWAYS_FORBIDDEN, BUILTIN_MEMBERS } from "./names.ts";
import type { Violation, ViolationKind } from "./violation.ts";

export interface SubsetContext {
  /** Lib globals that hold objects: usable only as a member receiver or a callee. */
  libObjects: ReadonlySet<string>;
  /** Value and type names declared by the lib or the tools; a program may not declare them. */
  reserved: ReadonlySet<string>;
  /** Member names declared by the lib or the tools, which a builtin may share. */
  declaredMembers: ReadonlySet<string>;
}

const K = ts.SyntaxKind;

const ALLOWED = new Set<ts.SyntaxKind>([
  K.SourceFile, K.EndOfFileToken,
  // statements
  K.Block, K.EmptyStatement, K.ExpressionStatement, K.VariableStatement, K.VariableDeclarationList,
  K.VariableDeclaration, K.FunctionDeclaration, K.Parameter, K.ReturnStatement, K.IfStatement,
  K.SwitchStatement, K.CaseBlock, K.CaseClause, K.DefaultClause, K.BreakStatement,
  K.ContinueStatement, K.ThrowStatement, K.TryStatement, K.CatchClause, K.ForStatement,
  K.ForOfStatement, K.WhileStatement, K.TypeAliasDeclaration,
  // expressions
  K.Identifier, K.NumericLiteral, K.StringLiteral, K.NoSubstitutionTemplateLiteral,
  K.TemplateExpression, K.TemplateHead, K.TemplateMiddle, K.TemplateTail, K.TemplateSpan,
  K.TrueKeyword, K.FalseKeyword, K.NullKeyword, K.BinaryExpression, K.PrefixUnaryExpression,
  K.PostfixUnaryExpression, K.ConditionalExpression, K.CallExpression, K.PropertyAccessExpression,
  K.ElementAccessExpression, K.ArrowFunction, K.ObjectLiteralExpression, K.PropertyAssignment,
  K.ShorthandPropertyAssignment, K.SpreadAssignment, K.ArrayLiteralExpression, K.SpreadElement,
  K.ParenthesizedExpression, K.AwaitExpression, K.TypeOfExpression, K.OmittedExpression,
  K.ObjectBindingPattern, K.ArrayBindingPattern, K.BindingElement, K.QuestionDotToken,
  K.ComputedPropertyName,
  // casts are reported by their own rule; as const is allowed
  K.AsExpression, K.TypeAssertionExpression, K.NonNullExpression,
  // modifiers and operator tokens that appear as children
  K.AsyncKeyword, K.ReadonlyKeyword, K.EqualsGreaterThanToken, K.DotDotDotToken, K.QuestionToken,
  K.ColonToken, K.EqualsToken, K.ExclamationToken,
]);

const BINARY_OPERATORS = new Set<ts.SyntaxKind>([
  K.PlusToken, K.MinusToken, K.AsteriskToken, K.SlashToken, K.PercentToken, K.AsteriskAsteriskToken,
  K.LessThanToken, K.GreaterThanToken, K.LessThanEqualsToken, K.GreaterThanEqualsToken,
  K.EqualsEqualsToken, K.ExclamationEqualsToken, K.EqualsEqualsEqualsToken,
  K.ExclamationEqualsEqualsToken, K.AmpersandAmpersandToken, K.BarBarToken, K.QuestionQuestionToken,
  K.AmpersandToken, K.BarToken, K.CaretToken, K.LessThanLessThanToken, K.GreaterThanGreaterThanToken,
  K.GreaterThanGreaterThanGreaterThanToken, K.EqualsToken, K.PlusEqualsToken, K.MinusEqualsToken,
  K.AsteriskEqualsToken, K.SlashEqualsToken, K.PercentEqualsToken, K.AmpersandAmpersandEqualsToken,
  K.BarBarEqualsToken, K.QuestionQuestionEqualsToken,
]);

// Names the compiler binds even with no lib loaded.
const BUILTIN_GLOBALS = new Set(["globalThis", "Symbol"]);

// Type positions are erased at run time, so they are allowed apart from `any` and `import(...)`.
const DISALLOWED_TYPES = new Set<ts.SyntaxKind>([K.ImportType]);

// Comment directives that change what the compiler checks or which files it loads.
const DIRECTIVE = /@ts-(ignore|expect-error|nocheck|check)\b|^\/\/\/\s*</i;

const ASSIGNMENT_OPERATORS = new Set<ts.SyntaxKind>([
  K.EqualsToken, K.PlusEqualsToken, K.MinusEqualsToken, K.AsteriskEqualsToken, K.SlashEqualsToken,
  K.PercentEqualsToken, K.AmpersandAmpersandEqualsToken, K.BarBarEqualsToken,
  K.QuestionQuestionEqualsToken,
]);

export function checkSubset(sf: ts.SourceFile, ctx: SubsetContext): Violation[] {
  const out: Violation[] = [];
  const report = (node: ts.Node | number, kind: ViolationKind, message: string) => {
    const pos = typeof node === "number" ? node : node.getStart(sf);
    const { line, character } = sf.getLineAndCharacterOfPosition(pos);
    out.push({ kind, message, line: line + 1, column: character + 1 });
  };

  checkComments(sf, report);
  checkDirectiveFields(sf, report);
  checkHtmlComments(sf, report);

  // A member read by name. A builtin name is allowed only where the lib or a tool declares it.
  const readable = (name: string) =>
    !ALWAYS_FORBIDDEN.has(name) && (!BUILTIN_MEMBERS.has(name) || ctx.declaredMembers.has(name));
  const checkRead = (node: ts.Node, name: string) => {
    if (ALWAYS_FORBIDDEN.has(name)) report(node, "forbidden-member", `member ${name} is forbidden`);
    else if (!readable(name)) {
      report(node, "forbidden-member",
             `member ${name} is a builtin the whitelist leaves out; rename the property if it is your own`);
    }
  };
  // Writes through a lib global would change what every later call to it does.
  const checkWrite = (target: ts.Node): void => {
    if (ts.isParenthesizedExpression(target)) return checkWrite(target.expression);
    if (ts.isArrayLiteralExpression(target)) return target.elements.forEach(checkWrite);
    if (ts.isSpreadElement(target)) return checkWrite(target.expression);
    if (ts.isObjectLiteralExpression(target)) {
      for (const p of target.properties) {
        if (ts.isPropertyAssignment(p)) checkWrite(p.initializer);
        else if (ts.isSpreadAssignment(p)) checkWrite(p.expression);
      }
      return;
    }
    if (ts.isBinaryExpression(target) && target.operatorToken.kind === K.EqualsToken) {
      return checkWrite(target.left);
    }
    let root: ts.Expression = target as ts.Expression;
    while (ts.isPropertyAccessExpression(root) || ts.isElementAccessExpression(root) ||
           ts.isParenthesizedExpression(root)) {
      root = root.expression;
    }
    if (root !== target && ts.isIdentifier(root) && ctx.libObjects.has(root.text)) {
      report(target, "forbidden-member", `${root.text} is read-only`);
    }
  };

  const visit = (node: ts.Node): void => {
    if (ts.isTypeNode(node) && !ts.isExpressionWithTypeArguments(node)) {
      visitType(node);
      return;
    }
    if (node.kind === K.TypeParameter) {
      ts.forEachChild(node, visitType);
      return;
    }
    if (!ALLOWED.has(node.kind)) {
      report(node, "unsupported-syntax", `${K[node.kind]} is outside the supported subset`);
      return;
    }
    switch (node.kind) {
      case K.VariableDeclarationList: {
        const flags = (node as ts.VariableDeclarationList).flags;
        if (!(flags & (ts.NodeFlags.Let | ts.NodeFlags.Const)) || flags & ts.NodeFlags.Using) {
          report(node, "unsupported-syntax", "only let and const bindings are supported");
          return;
        }
        break;
      }
      case K.FunctionDeclaration: {
        const fn = node as ts.FunctionDeclaration;
        if (fn.asteriskToken) {
          report(node, "unsupported-syntax", "generators are outside the supported subset");
          return;
        }
        if (!fn.body) {
          report(node, "unsupported-syntax", "a function declaration needs a body");
          return;
        }
        break;
      }
      case K.Parameter: {
        const p = node as ts.ParameterDeclaration;
        if (ts.isIdentifier(p.name) && p.name.text === "this") {
          report(node, "unsupported-syntax", "this is outside the supported subset");
          return;
        }
        break;
      }
      case K.ForOfStatement: {
        const loop = node as ts.ForOfStatement;
        if (loop.awaitModifier) {
          report(node, "unsupported-syntax", "for await is outside the supported subset");
          return;
        }
        if (!ts.isVariableDeclarationList(loop.initializer)) checkWrite(loop.initializer);
        break;
      }
      case K.BreakStatement:
      case K.ContinueStatement:
        if ((node as ts.BreakOrContinueStatement).label) {
          report(node, "unsupported-syntax", "labelled break and continue are unsupported");
          return;
        }
        break;
      case K.Identifier: {
        const text = (node as ts.Identifier).text;
        if (text === "arguments") {
          report(node, "unsupported-syntax", "arguments is outside the supported subset");
        } else if (BUILTIN_GLOBALS.has(text) && isValueReference(node as ts.Identifier)) {
          report(node, "not-whitelisted", `${text} is not whitelisted`);
        } else if (ctx.reserved.has(text) && isDeclarationName(node as ts.Identifier)) {
          report(node, "unsupported-syntax", `${text} is declared by the lib or a tool and cannot be redeclared`);
        } else if (ctx.libObjects.has(text) && isValueReference(node as ts.Identifier) &&
                   !isReceiverOrCallee(node as ts.Identifier)) {
          report(node, "not-whitelisted", `${text} may only be called or have a member read`);
        }
        break;
      }
      case K.PropertyAccessExpression: {
        const name = (node as ts.PropertyAccessExpression).name;
        if (ts.isPrivateIdentifier(name)) {
          report(name, "unsupported-syntax", "private names are outside the supported subset");
          return;
        }
        checkRead(name, name.text);
        break;
      }
      case K.ElementAccessExpression: {
        const arg = (node as ts.ElementAccessExpression).argumentExpression;
        if (ts.isStringLiteralLike(arg)) checkRead(arg, arg.text);
        break;
      }
      case K.PropertyAssignment:
      case K.ShorthandPropertyAssignment: {
        const name = (node as ts.PropertyAssignment).name;
        const text = ts.isIdentifier(name) || ts.isStringLiteralLike(name) ? name.text : undefined;
        if (text !== undefined && isAssignmentPattern(node.parent)) {
          // In a destructuring assignment the key is a member read.
          checkRead(name, text);
        } else if (text !== undefined && ALWAYS_FORBIDDEN.has(text)) {
          report(name, "forbidden-member", `member ${text} is forbidden`);
        }
        if (ts.isComputedPropertyName(name)) {
          report(name, "unsupported-syntax", "computed property names are unsupported");
          return;
        }
        break;
      }
      case K.ComputedPropertyName:
        report(node, "unsupported-syntax", "computed property names are unsupported");
        return;
      case K.BindingElement: {
        const prop = (node as ts.BindingElement).propertyName;
        const name = (node as ts.BindingElement).name;
        // In an object pattern the property name, or a shorthand name, is a member read.
        const key = ts.isObjectBindingPattern((node as ts.BindingElement).parent) ? prop ?? name : undefined;
        if (key && (ts.isIdentifier(key) || ts.isStringLiteralLike(key))) checkRead(key, key.text);
        if (ts.isIdentifier(name) && ALWAYS_FORBIDDEN.has(name.text)) {
          report(name, "forbidden-member", `member ${name.text} is forbidden`);
        }
        if (prop && ts.isComputedPropertyName(prop)) {
          report(prop, "unsupported-syntax", "computed property names are unsupported");
          return;
        }
        break;
      }
      case K.BinaryExpression: {
        const bin = node as ts.BinaryExpression;
        if (!BINARY_OPERATORS.has(bin.operatorToken.kind)) {
          report(bin.operatorToken, "unsupported-syntax",
                 `operator ${bin.operatorToken.getText(sf)} is outside the supported subset`);
        }
        if (ASSIGNMENT_OPERATORS.has(bin.operatorToken.kind)) checkWrite(bin.left);
        visit(bin.left);
        visit(bin.right);
        return;
      }
      case K.AsExpression: {
        const as = node as ts.AsExpression;
        if (!isConstAssertion(as.type)) {
          report(node, "cast", "as casts are forbidden; only as const is allowed");
        }
        visit(as.expression);
        return;
      }
      case K.PrefixUnaryExpression:
      case K.PostfixUnaryExpression: {
        const op = (node as ts.PrefixUnaryExpression).operator;
        if (op === K.PlusPlusToken || op === K.MinusMinusToken) {
          checkWrite((node as ts.PrefixUnaryExpression).operand);
        }
        break;
      }
      case K.VariableDeclaration:
        if ((node as ts.VariableDeclaration).exclamationToken) {
          report(node, "cast", "definite assignment assertions are forbidden");
        }
        break;
      case K.TypeAssertionExpression:
        report(node, "cast", "type assertions are forbidden");
        break;
      case K.NonNullExpression:
        report(node, "cast", "non-null assertions are forbidden");
        break;
    }
    ts.forEachChild(node, visit);
  };

  const visitType = (node: ts.Node): void => {
    if (node.kind === K.AnyKeyword) {
      report(node, "any-type", "the any type is forbidden");
      return;
    }
    if (ts.isTypePredicateNode(node)) {
      report(node, "cast", "type predicates and asserts signatures are forbidden");
      return;
    }
    if (DISALLOWED_TYPES.has(node.kind)) {
      report(node, "unsupported-syntax", `${K[node.kind]} is outside the supported subset`);
      return;
    }
    if (ts.isTypeQueryNode(node)) {
      visit(node.exprName);
      return;
    }
    ts.forEachChild(node, visitType);
  };

  for (const stmt of sf.statements) visit(stmt);
  return out;
}

function isConstAssertion(type: ts.TypeNode): boolean {
  return ts.isTypeReferenceNode(type) && ts.isIdentifier(type.typeName) &&
    type.typeName.text === "const" && !type.typeArguments;
}

function isValueReference(id: ts.Identifier): boolean {
  const p = id.parent;
  if (ts.isPropertyAccessExpression(p) && p.name === id) return false;
  if (ts.isBindingElement(p) && p.propertyName === id) return false;
  if (ts.isPropertyAssignment(p) && p.name === id) return false;
  return true;
}

// Whether an object or array literal is a destructuring assignment or for...of target.
function isAssignmentPattern(start: ts.Node): boolean {
  let up = start;
  for (;;) {
    const q = up.parent;
    if (ts.isParenthesizedExpression(q) || ts.isArrayLiteralExpression(q) || ts.isSpreadElement(q) ||
        ts.isSpreadAssignment(q) || ts.isObjectLiteralExpression(q) ||
        (ts.isPropertyAssignment(q) && q.initializer === up) ||
        (ts.isBinaryExpression(q) && q.operatorToken.kind === K.EqualsToken && q.left === up &&
         isAssignmentPattern(q))) {
      up = q;
      continue;
    }
    return (ts.isBinaryExpression(q) && q.left === up && q.operatorToken.kind === K.EqualsToken) ||
           (ts.isForOfStatement(q) && q.initializer === up);
  }
}

function isReceiverOrCallee(id: ts.Identifier): boolean {
  const p = id.parent;
  return ((ts.isPropertyAccessExpression(p) || ts.isElementAccessExpression(p) || ts.isCallExpression(p)) &&
          p.expression === id);
}

function isDeclarationName(id: ts.Identifier): boolean {
  const p = id.parent;
  return ((ts.isVariableDeclaration(p) || ts.isFunctionDeclaration(p) || ts.isParameter(p) ||
           ts.isBindingElement(p) || ts.isTypeAliasDeclaration(p) || ts.isTypeParameterDeclaration(p)) &&
          p.name === id);
}

// Annex B lets a script parser read `<!--` and a `-->` as line comments, where TypeScript reads
// `<` `!` `--` and `--` `>`. Code the checker sees as text would then run, so reject both spellings.
function checkHtmlComments(sf: ts.SourceFile,
                           report: (pos: number, kind: ViolationKind, message: string) => void): void {
  const text = sf.text;
  const visit = (node: ts.Node): void => {
    if (node.kind === ts.SyntaxKind.LessThanToken && text.startsWith("!--", node.end)) {
      report(node.getStart(sf), "unsupported-syntax", "<!-- is an HTML-like comment to a script parser; add spaces");
    } else if (node.kind === ts.SyntaxKind.MinusMinusToken && text.startsWith(">", node.end)) {
      report(node.getStart(sf), "unsupported-syntax", "--> is an HTML-like comment to a script parser; add spaces");
    }
    node.getChildren(sf).forEach(visit);
  };
  visit(sf);
}

// What the compiler took from directive comments, in case a spelling gets past DIRECTIVE.
function checkDirectiveFields(sf: ts.SourceFile,
                              report: (pos: number, kind: ViolationKind, message: string) => void): void {
  const internal = sf as unknown as { commentDirectives?: unknown[]; checkJsDirective?: unknown;
                                      pragmas?: ReadonlyMap<string, unknown> };
  if ((internal.commentDirectives?.length ?? 0) > 0 || internal.checkJsDirective !== undefined ||
      (internal.pragmas?.size ?? 0) > 0 || sf.referencedFiles.length > 0 ||
      sf.typeReferenceDirectives.length > 0 || sf.libReferenceDirectives.length > 0) {
    report(0, "ts-directive", "the program carries a compiler directive");
  }
}

// Every comment in the file, found from the leading and trailing trivia of every token. A
// directive inside a string or template is text, not a comment, so it is not reported.
function checkComments(sf: ts.SourceFile,
                       report: (pos: number, kind: ViolationKind, message: string) => void): void {
  const text = sf.text;
  const seen = new Set<number>();
  const check = (ranges: ts.CommentRange[] | undefined) => {
    for (const r of ranges ?? []) {
      if (seen.has(r.pos)) continue;
      seen.add(r.pos);
      const comment = text.slice(r.pos, r.end);
      if (DIRECTIVE.test(comment)) {
        report(r.pos, "ts-directive", `comment directive ${comment.split("\n")[0]} is forbidden`);
      }
    }
  };
  const walk = (node: ts.Node): void => {
    check(ts.getLeadingCommentRanges(text, node.pos));
    check(ts.getTrailingCommentRanges(text, node.end));
    for (const child of node.getChildren(sf)) walk(child);
  };
  check(ts.getLeadingCommentRanges(text, 0));
  walk(sf);
}
