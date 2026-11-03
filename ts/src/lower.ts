// Lowering (HC-18): a type-checked TypeScript program to the IR that the termination port reads. The
// IR is only analysed, never run. Lowering is deny-by-default: a construct it does not know becomes
// an unsupported-syntax violation, never a silently dropped node.
//
// User names get a `js.` prefix. No TypeScript identifier can contain a dot, so a program's `list`
// or `do` can never be read as the Scheme form of that name.
//
// A block lowers as a statement list with its rest as the continuation. An `if` that falls through
// gets a fresh lowering of the rest in each branch, because the termination port keys its tables on
// forms by identity. MAX_NODES caps the growth that copying causes.
//
// A binding statement in a block becomes `letrec*`, which is the scope JavaScript gives `const` and
// `let`: an arrow's own name and earlier bindings of the same statement are in scope in its body.
// A plain `let` would leave a self-calling arrow's name free, and a free name is a leaf to the
// analysis, so it would hide the recursion.
//
// An if branch, a try or catch block, a nested block and a case clause are spliced in front of the
// statements after them, so a binding one declares would scope over those too (HC-29). Every binding
// declared in a block, and a catch variable, gets a fresh name `js.y%N`. Every identifier is resolved to its
// symbol, so a later statement naming an outer `y` keeps `js.y`.
//
// A classic `for` and a narrow `while` become `do` loops and `for...of` a `for-each`, so the existing loop rules judge
// them. A loop body is lowered as a closed block that may not `return`, `break` or `continue`: each
// leaves the loop early, and lowering it as a value would lose the function's result.

import ts from "typescript";
import { Sym, sym, type Datum } from "./sexp.ts";
import type { Violation } from "./violation.ts";

const MAX_NODES = 20000;
// How many consts deep a call argument is followed (HC-22). A longer chain keeps its name, which is
// sound, rather than recursing until the stack runs out.
const MAX_LINKS = 32;
const LIB_PATH = "/ts-safe.d.ts";

const S = {
  define: sym("define"), lambda: sym("lambda"), letrec: sym("letrec*"), if: sym("if"), begin: sym("begin"),
  set: sym("set!"), do: sym("do"), and: sym("and"), or: sym("or"), not: sym("not"), void: sym("void"), eqv: sym("eqv?"),
  guard: sym("guard"),
};

// Each array HOF, the Scheme HOF that models it, and how many parameters its callback must take.
// The Scheme HOFs pass one element per call, plus the accumulator for fold-left, so a callback that
// also wants JavaScript's index argument has no lowering. find's #f for a miss stands in for
// undefined; the IR is only analysed.
const HOFS = new Map<string, { prim: string; arity: number }>([
  ["map", { prim: "map", arity: 1 }], ["filter", { prim: "filter", arity: 1 }],
  ["forEach", { prim: "for-each", arity: 1 }], ["find", { prim: "find", arity: 1 }],
  ["some", { prim: "exists", arity: 1 }], ["every", { prim: "for-all", arity: 1 }],
  ["reduce", { prim: "fold-left", arity: 2 }],
]);

// Members JavaScript calls with no call in the program text: string and number conversion,
// JSON.stringify and await. An object that defines one could recurse through a template or a `+`
// that the IR models as data, so no object literal may define one.
const IMPLICIT = new Set(["toString", "valueOf", "toJSON", "then"]);

// Array methods that cannot change the array. The one mutator lowered is push, under pushable().
const ARRAY_READERS = new Set(["at", "concat", "findIndex", "includes", "indexOf", "join", "slice"]);
// Mutators that only reorder. The length holds, so a loop bound is not affected, and sort's
// comparator escapes to the free call like any other callback. slice(1) is no cdr: [].slice(1) is
// [], a fixed point, so it stays the free call that size-change cannot read as a decrease.
const REORDERS = new Set(["sort", "reverse"]);
// Members the lowering reads as an array's. A narrowing that TypeScript keeps across a call lets a
// record pass as an array, and then the record's own field would run where the IR has a Scheme
// primitive. So no object literal may define one, nor an index key.
const ARRAY_MEMBERS = new Set([...HOFS.keys(), ...ARRAY_READERS, ...REORDERS, "length", "push"]);

const BINARY = new Map<ts.SyntaxKind, string>([
  [ts.SyntaxKind.PlusToken, "+"], [ts.SyntaxKind.MinusToken, "-"], [ts.SyntaxKind.AsteriskToken, "*"],
  [ts.SyntaxKind.SlashToken, "/"], [ts.SyntaxKind.PercentToken, "remainder"],
  [ts.SyntaxKind.LessThanToken, "<"], [ts.SyntaxKind.LessThanEqualsToken, "<="],
  [ts.SyntaxKind.GreaterThanToken, ">"], [ts.SyntaxKind.GreaterThanEqualsToken, ">="],
]);

// The comparison that is true exactly when the key's comparison is false, NaN aside.
const FLIPPED = new Map<ts.SyntaxKind, string>([
  [ts.SyntaxKind.LessThanToken, ">="], [ts.SyntaxKind.LessThanEqualsToken, ">"],
  [ts.SyntaxKind.GreaterThanToken, "<="], [ts.SyntaxKind.GreaterThanEqualsToken, "<"],
]);

// The syntax a const initializer may use to be seen through (HC-22). Each is a
// JavaScript operator with no effect that always returns. A record read is not one, since a record
// field can be assigned. `length` can change after the binding, since an array can be pushed to, so
// arcShape below never lets a length through to size-change.
const PURE_OPERATORS = new Set([
  ts.SyntaxKind.PlusToken, ts.SyntaxKind.MinusToken, ts.SyntaxKind.AsteriskToken, ts.SyntaxKind.SlashToken,
  ts.SyntaxKind.PercentToken,
]);
const pureSyntax = (expression: ts.Expression): boolean => {
  const e = skipParens(expression);
  if (ts.isIdentifier(e) || ts.isNumericLiteral(e)) return true;
  if (ts.isBinaryExpression(e)) return PURE_OPERATORS.has(e.operatorToken.kind) && pureSyntax(e.left) && pureSyntax(e.right);
  if (ts.isPrefixUnaryExpression(e)) return e.operator === ts.SyntaxKind.MinusToken && pureSyntax(e.operand);
  if (ts.isPropertyAccessExpression(e)) return e.name.text === "length" && pureSyntax(e.expression);
  return false;
};
// The only argument shapes size-change reads: a name, or a name plus or minus a literal. Seeing through
// nothing larger keeps an inlined argument at three forms, so a const used twice cannot double the
// lowering. A constant gives size-change no arc, so a const bound to one keeps its name.
const PLUS = sym("+");
const MINUS = sym("-");
const arcShape = (d: Datum): boolean =>
  d instanceof Sym ||
  (Array.isArray(d) && d.length === 3 && (d[0] === PLUS || d[0] === MINUS) &&
    ((d[1] instanceof Sym && typeof d[2] === "number") || (d[0] === PLUS && typeof d[1] === "number" && d[2] instanceof Sym)));

const skipParens = (e: ts.Expression): ts.Expression => (ts.isParenthesizedExpression(e) ? skipParens(e.expression) : e);

class Unsupported extends Error {
  readonly node: ts.Node;
  constructor(node: ts.Node, message: string) {
    super(message);
    this.node = node;
  }
}

export interface Lowered {
  ir: Datum[];
  violations: Violation[];
}

// The checker decides what a member means: `xs.length` is `length` only when `xs` is an array. A
// type can say number while the value is a string, so `+` is arithmetic only where byConstruction
// says both operands are numbers at run time.
export function lower(sf: ts.SourceFile, checker: ts.TypeChecker, byConstruction: (e: ts.Expression) => boolean): Lowered {
  let nodes = 0;
  const count = <T extends Datum>(d: T): T => {
    if (++nodes > MAX_NODES) throw new Unsupported(sf, `lowering grew past ${MAX_NODES} forms; split the early returns into functions`);
    return d;
  };
  const fresh = new Map<ts.Symbol, Sym>();
  const name = (id: ts.Node): Datum => {
    if (!ts.isIdentifier(id)) throw new Unsupported(id, "only a plain identifier may be bound here");
    // On the name of a shorthand property the checker answers with the property, so `{ a }` asks for
    // the variable it reads.
    const s = ts.isShorthandPropertyAssignment(id.parent) && id.parent.name === id
      ? checker.getShorthandAssignmentValueSymbol(id.parent)
      : checker.getSymbolAtLocation(id);
    if (!s?.valueDeclaration || !spliced(s.valueDeclaration)) return sym(`js.${id.text}`);
    // A case's binding scopes over the whole switch, so a later case can name it before it is bound.
    const clause = ts.findAncestor(s.valueDeclaration, (n) => ts.isCaseOrDefaultClause(n) || ts.isFunctionLike(n));
    if (clause && ts.isCaseOrDefaultClause(clause) && !ts.findAncestor(id, (n) => n === clause)) {
      throw new Unsupported(id, `${id.text} is bound in another case of the switch`);
    }
    // HC-35: a statement's letrec* scopes only over what follows it, so a closure naming a binding of
    // a later statement would read a free name, a leaf to the analysis, and any cycle through it would
    // vanish. Bindings of one statement share its letrec*, so they may name each other.
    const statement = ts.findAncestor(s.valueDeclaration, ts.isVariableStatement);
    if (statement && id.getStart(sf) < statement.getStart(sf)) {
      throw new Unsupported(id, `${id.text} is named before the statement that declares it: declare it first, or bind both in one const statement`);
    }
    let v = fresh.get(s);
    if (!v) fresh.set(s, (v = sym(`js.${id.text}%${fresh.size + 1}`)));
    return v;
  };
  // Whether a declaration is bound in a block rather than at the top level. A function body's binding
  // is fresh too: its letrec* sits at the declaration, so a closure defined above it would read an
  // outer binding of the same name. A while loop lifts its body's last statement outside the letrec*.
  const spliced = (d: ts.Declaration): boolean => {
    if (ts.isVariableDeclaration(d) && ts.isCatchClause(d.parent)) return true;
    let n: ts.Node = d;
    while (ts.isBindingElement(n) || ts.isObjectBindingPattern(n) || ts.isArrayBindingPattern(n) || ts.isVariableDeclaration(n)) n = n.parent;
    if (!ts.isVariableDeclarationList(n) || !ts.isVariableStatement(n.parent)) return false;
    const home = n.parent.parent;
    if (ts.isCaseClause(home) || ts.isDefaultClause(home)) return true;
    return ts.isBlock(home);
  };
  // A destructuring parameter becomes a temporary, and its bindings open the body as a letrec*.
  const params = (fn: ts.SignatureDeclaration): { formals: Datum[]; bindings: Datum[][] } => {
    const bindings: Datum[][] = [];
    if (fn.parameters.some(omittable)) calledOnlyDirectly(fn);
    const formals = fn.parameters.map((p) => {
      if (p.dotDotDotToken) throw new Unsupported(p, "rest parameters are not lowered yet");
      if (omittable(p)) {
        if (!ts.isIdentifier(p.name)) throw new Unsupported(p, "a destructuring parameter may not be optional or have a default");
        if (p.initializer && !literalDefault(p.initializer)) {
          throw new Unsupported(p.initializer, "a default must be a number, string, boolean or null literal");
        }
      }
      if (ts.isIdentifier(p.name)) return name(p.name);
      if (ts.isObjectBindingPattern(p.name) ? !isRecord(p.name) : !isArrayNode(p.name)) {
        throw new Unsupported(p.name, "a destructuring pattern must match an object or array type");
      }
      const t = sym(`%js.tmp${++temps}`);
      destructure(p.name, t, bindings);
      return t;
    });
    return { formals, bindings };
  };
  const withBindings = (bindings: Datum[][], body: Datum): Datum => (bindings.length > 0 ? count([S.letrec, bindings, body]) : body);

  // HC-32: a call may omit an optional or defaulted argument, and the analysis drops a call whose
  // arity cannot match its lambda. So a direct call fills each omitted argument in, and a function
  // with such a parameter may be named only as the callee of one. An alias, a callback or a field
  // would call it with too few arguments where the IR cannot see the call.
  const omittable = (p: ts.ParameterDeclaration): boolean => !!p.initializer || !!p.questionToken;
  const literalDefault = (init: ts.Expression): boolean => {
    const e = skipParens(init);
    if (ts.isPrefixUnaryExpression(e)) return e.operator === ts.SyntaxKind.MinusToken && ts.isNumericLiteral(e.operand);
    return ts.isNumericLiteral(e) || ts.isStringLiteral(e) || ts.isNoSubstitutionTemplateLiteral(e) ||
      e.kind === ts.SyntaxKind.TrueKeyword || e.kind === ts.SyntaxKind.FalseKeyword || e.kind === ts.SyntaxKind.NullKeyword;
  };
  // The name a function is bound to when its definition is fixed: a function declaration, or an arrow
  // that is the whole initializer of a const.
  const fixedName = (fn: ts.SignatureDeclaration): ts.Identifier | undefined => {
    if (ts.isFunctionDeclaration(fn)) return fn.name;
    let n: ts.Node = fn;
    while (ts.isParenthesizedExpression(n.parent)) n = n.parent;
    const d = n.parent;
    if (!ts.isArrowFunction(fn) || !ts.isVariableDeclaration(d) || d.initializer !== n || !ts.isIdentifier(d.name)) return undefined;
    return ts.getCombinedNodeFlags(d) & ts.NodeFlags.Const ? d.name : undefined;
  };
  const calledOnlyDirectly = (fn: ts.SignatureDeclaration): void => {
    const id = fixedName(fn);
    const target = id && checker.getSymbolAtLocation(id);
    if (!id || !target) throw new Unsupported(fn, "a function with an optional or default parameter must be a function declaration or a const arrow");
    const visit = (n: ts.Node): void => {
      if (ts.isIdentifier(n) && n !== id && symbolOf(n) === target) {
        const p = n.parent;
        if (!ts.isCallExpression(p) || p.expression !== n || p.questionDotToken) {
          throw new Unsupported(n, `${id.text} has an optional or default parameter, so it may only be called directly by name`);
        }
      }
      n.getChildren(sf).forEach(visit);
    };
    visit(sf);
  };
  // The parameters of the program function a direct call names, when its definition is fixed. A
  // tool is a free name, so it needs no filling.
  const fixedParameters = (callee: ts.Identifier): readonly ts.ParameterDeclaration[] | undefined => {
    const decls = checker.getSymbolAtLocation(callee)?.declarations ?? [];
    const d = decls.length === 1 ? decls[0]! : undefined;
    if (!d || d.getSourceFile() !== sf) return undefined;
    if (ts.isFunctionDeclaration(d)) return d.parameters;
    if (ts.isVariableDeclaration(d) && d.initializer && (ts.getCombinedNodeFlags(d) & ts.NodeFlags.Const)) {
      const f = skipParens(d.initializer);
      if (ts.isArrowFunction(f)) return f.parameters;
    }
    return undefined;
  };
  // A passed undefined becomes the default at run time, which the IR would not see.
  // A passed null stays null. A type parameter or other deferred type may be instantiated with
  // undefined, so it counts as admitting it.
  const MAY_BE_UNDEFINED = ts.TypeFlags.Undefined | ts.TypeFlags.Void | ts.TypeFlags.Unknown | ts.TypeFlags.Any |
    ts.TypeFlags.TypeParameter | ts.TypeFlags.IndexedAccess | ts.TypeFlags.Conditional | ts.TypeFlags.Substitution;
  const admitsUndefined = (t: ts.Type): boolean => (t.isUnion() ? t.types.some(admitsUndefined) : (t.flags & MAY_BE_UNDEFINED) !== 0);
  const filled = (callee: ts.Identifier, args: readonly ts.Expression[]): Datum[] => {
    const ps = fixedParameters(callee);
    if (!ps || !ps.some(omittable)) return [];
    if (args.some(ts.isSpreadElement)) throw new Unsupported(callee, `${callee.text} has an optional or default parameter, so a call to it may not spread`);
    // A const's annotation can declare more parameters than its arrow.
    if (args.length > ps.length) throw new Unsupported(callee, `${callee.text} declares ${ps.length} parameters, so a call may not pass more`);
    ps.forEach((p, k) => {
      const a = args[k];
      if (a && p.initializer && admitsUndefined(checker.getTypeAtLocation(a))) {
        throw new Unsupported(a, "an argument at a defaulted position may not admit undefined, since the default would replace it");
      }
    });
    return ps.slice(args.length).map((p) => (p.initializer ? expr(p.initializer) : count([S.void])));
  };

  // In an optional chain the receiver's type admits null or undefined, which the guard has ruled out
  // by the time the member is read, so the member is judged on the type without them (HC-31).
  const typeOf = (e: ts.Node, nonNullable = false): ts.Type => {
    const t = checker.getTypeAtLocation(e);
    return nonNullable ? checker.getNonNullableType(t) : t;
  };
  const isArray = (e: ts.Expression, nonNullable = false): boolean => {
    const t = typeOf(e, nonNullable);
    return checker.isArrayType(t) || checker.isTupleType(t);
  };
  const isRecord = (e: ts.Node, nonNullable = false): boolean => {
    const t = typeOf(e, nonNullable);
    return (t.flags & ts.TypeFlags.Object) !== 0 && !checker.isArrayType(t) && !checker.isTupleType(t) && t.getCallSignatures().length === 0;
  };
  const isArrayNode = (e: ts.Node): boolean => {
    const t = checker.getTypeAtLocation(e);
    return checker.isArrayType(t) || checker.isTupleType(t);
  };

  // The gate reserves every lib name, so a lib global is never shadowed by the program.
  const isLibGlobal = (id: ts.Identifier): boolean =>
    checker.getSymbolAtLocation(id)?.declarations?.some((d) => d.getSourceFile().fileName === LIB_PATH) ?? false;
  const isPrimitive = (e: ts.Expression): boolean =>
    (checker.getTypeAtLocation(e).flags & (ts.TypeFlags.StringLike | ts.TypeFlags.NumberLike)) !== 0;
  const isNumber = (e: ts.Expression): boolean => (checker.getTypeAtLocation(e).flags & ts.TypeFlags.NumberLike) !== 0;

  // Arithmetic and comparison are the Scheme primitive only when both operands are numbers. On a
  // string, + concatenates and < compares text, and the loop and size-change rules would read either
  // as numeric progress. So any other operand makes it a free call the analysis does not model.
  // The type is enough for the operators that convert to a number, and for a comparison, since
  // only the first test of a counter they step can see a string. `+` keeps a string a string, so it
  // needs both operands to be numbers by construction: a parameter never is.
  const arith = (prim: string, left: ts.Expression, right: ts.Expression): Datum => {
    const numeric = prim === "+" ? byConstruction(left) && byConstruction(right) : isNumber(left) && isNumber(right);
    return count([sym(numeric ? prim : `js.%${prim}`), expr(left), expr(right)]);
  };

  // The [name, value] pairs a declaration binds, in order. A destructuring source that is not a
  // variable is bound to a temporary first, so it is evaluated once.
  let temps = 0;
  const declare = (d: ts.VariableDeclaration): Datum[][] => {
    if (!d.initializer) throw new Unsupported(d, "a binding needs an initializer");
    if (ts.isIdentifier(d.name)) return [[name(d.name), expr(d.initializer)]];
    const pattern = d.name;
    const source = skipParens(d.initializer);
    if (ts.isObjectBindingPattern(pattern) ? !isRecord(source) : !isArray(source)) {
      throw new Unsupported(pattern, "a destructuring pattern must match an object or array type");
    }
    const out: Datum[][] = [];
    let src: Datum;
    if (ts.isIdentifier(source)) {
      src = name(source);
    } else {
      src = sym(`%js.tmp${++temps}`);
      out.push([src, expr(source)]);
    }
    destructure(pattern, src, out);
    return out;
  };

  // Binds each element of a pattern to its read of src. A nested pattern reads its field into a
  // temporary and destructures that, and its own type must match the pattern's kind.
  const destructure = (pattern: ts.BindingPattern, src: Datum, out: Datum[][]): void => {
    pattern.elements.forEach((el, k) => {
      if (ts.isOmittedExpression(el)) return;
      if (el.initializer) throw new Unsupported(el, "a destructuring default is not lowered yet");
      let v: Datum;
      let nested: ts.BindingPattern | undefined;
      if (ts.isIdentifier(el.name)) {
        v = name(el.name);
      } else {
        nested = el.name;
        if (el.dotDotDotToken || (ts.isObjectBindingPattern(nested) ? !isRecord(nested) : !isArrayNode(nested))) {
          throw new Unsupported(nested, "a nested destructuring pattern must match an object or array type");
        }
        v = sym(`%js.tmp${++temps}`);
      }
      if (ts.isObjectBindingPattern(pattern)) {
        if (el.dotDotDotToken) throw new Unsupported(el, "an object rest is not lowered yet");
        const key = el.propertyName ?? el.name;
        if (!ts.isIdentifier(key) && !ts.isStringLiteral(key)) throw new Unsupported(key, "a computed destructuring key is not lowered");
        out.push([v, count([sym("vector-ref"), src, key.text])]);
      } else if (el.dotDotDotToken) {
        // Not cdr: the rest of [] is [], a fixed point that size-change would read as a decrease.
        out.push([v, k === 0 ? src : count([sym("js.method.slice"), src, k])]);
      } else {
        out.push([v, count([sym("js.%index"), src, k])]);
      }
      if (nested) destructure(nested, v, out);
    });
  };

  // A spread list as the arguments of append: each spread array as itself, each run of plain
  // elements between them as one list. Only an array is spread, since a string or other iterable has
  // no list in the IR.
  const appendArgs = (els: readonly ts.Expression[]): Datum[] => {
    const out: Datum[] = [];
    let run: Datum[] | undefined;
    for (const el of els) {
      if (ts.isSpreadElement(el)) {
        if (!isArray(el.expression)) throw new Unsupported(el, "only an array may be spread");
        run = undefined;
        out.push(expr(el.expression));
      } else {
        if (!run) {
          run = count([sym("list")]);
          out.push(run);
        }
        run.push(expr(el));
      }
    }
    return out;
  };

  // A call whose arguments may spread becomes apply: the plain arguments before the first spread are
  // passed directly, and everything from it on is one list.
  const call = (head: Datum, leading: Datum[], args: readonly ts.Expression[], throughConsts = false): Datum => {
    const k = args.findIndex(ts.isSpreadElement);
    if (k < 0) return count([head, ...leading, ...args.map(throughConsts ? argument : expr)]);
    const tail = appendArgs(args.slice(k));
    const list = tail.length === 1 && ts.isSpreadElement(args[k]) ? tail[0] : count([sym("append"), ...tail]);
    return count([sym("apply"), head, ...leading, ...args.slice(0, k).map(expr), list]);
  };

  // How many parameters a callback's own text declares. A type can claim fewer than the function
  // takes, through a narrowing TypeScript keeps across a call or an assignment that drops optional
  // parameters, and a HOF passes the array to a parameter the type hid. So only a function whose
  // definition is fixed is counted: an arrow at the call, a const bound to an arrow, or a function
  // declaration, which TypeScript forbids assigning to.
  const arityOf = (callback: ts.Expression): number | undefined => {
    const e = skipParens(callback);
    if (ts.isArrowFunction(e)) return e.parameters.length;
    if (!ts.isIdentifier(e)) return undefined;
    const decls = checker.getSymbolAtLocation(e)?.declarations ?? [];
    if (decls.length !== 1) return undefined;
    const d = decls[0];
    if (ts.isFunctionDeclaration(d)) return d.parameters.length;
    if (ts.isVariableDeclaration(d) && (d.parent.flags & ts.NodeFlags.Const) && d.initializer && ts.isArrowFunction(skipParens(d.initializer))) {
      return (skipParens(d.initializer) as ts.ArrowFunction).parameters.length;
    }
    return undefined;
  };

  // HC-22: a call argument naming a const bound to a pure expression lowers as that expression, so
  // size-change sees `const m = n - 1; return f(m)` as f(n - 1). Only an argument, because that is
  // all size-change reads. A const inside the expression is followed in turn.
  //
  // Pure means arithmetic and length alone: it has no effect and always returns, so evaluating it at
  // the use instead of the binding changes nothing the analysis can see. Every name in it must be a
  // parameter or a const that means the same thing at the use. useSite is the outermost use while a
  // chain of consts is followed. Purity does not depend on the use, so it is decided once per const,
  // and only an initializer whose syntax could be pure is lowered to find out.
  let useSite: ts.Identifier | undefined;
  let links = 0;
  const pureConst = new Map<ts.VariableDeclaration, boolean>();
  const seeThrough = (id: ts.Identifier): Datum | undefined => {
    const site = useSite ?? id;
    const d = constDeclaration(id);
    if (!d || pureConst.get(d) === false || d.end > site.getStart()) return undefined;
    if (!pureSyntax(d.initializer!)) {
      pureConst.set(d, false);
      return undefined;
    }
    if (!freeNamesStable(d.initializer!, site) || links >= MAX_LINKS) return undefined;
    const saved = useSite;
    useSite = site;
    links++;
    try {
      const v = expr(d.initializer!);
      const pure = arcShape(v);
      pureConst.set(d, pure);
      return pure ? v : undefined;
    } finally {
      useSite = saved;
      links--;
    }
  };
  const argument = (a: ts.Expression): Datum => {
    const e = skipParens(a);
    return (ts.isIdentifier(e) ? seeThrough(e) : undefined) ?? expr(a);
  };
  // Size-change reads only the arguments of a call that can come back to its caller, so a const is
  // seen through there alone. Anywhere else inlining it only grows the lowering, which every
  // fall-through if then copies (HC-22 review 3). A call counts when the callee is a function of this
  // file whose body, followed through every function it names, names the caller's function again.
  const userFunction = (id: ts.Identifier): ts.Node | undefined => {
    const decls = checker.getSymbolAtLocation(id)?.declarations ?? [];
    const d = decls.length === 1 ? decls[0]! : undefined;
    if (!d || d.getSourceFile() !== sf) return undefined;
    if (ts.isFunctionDeclaration(d) && d.body) return d;
    if (ts.isVariableDeclaration(d) && d.initializer) {
      const f = skipParens(d.initializer);
      if (ts.isArrowFunction(f) || ts.isFunctionExpression(f)) return d;
    }
    return undefined;
  };
  const namedCaller = (n: ts.Node): ts.Node | undefined => {
    for (let p = n.parent; p; p = p.parent) {
      if (ts.isFunctionDeclaration(p) && p.name) return p;
      if (ts.isVariableDeclaration(p) && p.initializer && ts.isIdentifier(p.name) && userFunction(p.name) === p) return p;
    }
    return undefined;
  };
  const named = new Map<ts.Node, Set<ts.Node>>();
  const namedFunctions = (fn: ts.Node): Set<ts.Node> => {
    let out = named.get(fn);
    if (out) return out;
    out = new Set();
    const visit = (n: ts.Node): void => {
      const f = ts.isIdentifier(n) ? userFunction(n) : undefined;
      if (f) out!.add(f);
      ts.forEachChild(n, visit);
    };
    ts.forEachChild(fn, visit);
    named.set(fn, out);
    return out;
  };
  const recursesBack = (callee: ts.Identifier): boolean => {
    const target = userFunction(callee);
    const caller = namedCaller(callee);
    if (!target || !caller) return false;
    const seen = new Set<ts.Node>([target]);
    const work = [target];
    while (work.length > 0) {
      const f = work.pop()!;
      if (f === caller) return true;
      for (const g of namedFunctions(f)) if (!seen.has(g)) (seen.add(g), work.push(g));
    }
    return false;
  };
  const constDeclaration = (id: ts.Identifier): ts.VariableDeclaration | undefined => {
    const decls = checker.getSymbolAtLocation(id)?.declarations ?? [];
    if (decls.length !== 1) return undefined;
    const d = decls[0]!;
    if (!ts.isVariableDeclaration(d) || !ts.isIdentifier(d.name) || !d.initializer) return undefined;
    return ts.getCombinedNodeFlags(d) & ts.NodeFlags.Const ? d : undefined;
  };
  const freeNamesStable = (init: ts.Node, site: ts.Identifier): boolean => {
    let ok = true;
    const visit = (n: ts.Node): void => {
      if (!ok) return;
      if (ts.isPropertyAccessExpression(n)) return visit(n.expression);
      if (ts.isIdentifier(n)) {
        const s = checker.getSymbolAtLocation(n);
        const d = s?.declarations?.length === 1 ? s.declarations[0]! : undefined;
        const fixed = d !== undefined && (ts.isParameter(d) || constDeclaration(n) !== undefined);
        ok = fixed && checker.resolveName(n.text, site, ts.SymbolFlags.Value, false) === s;
        return;
      }
      ts.forEachChild(n, visit);
    };
    visit(init);
    return ok;
  };

  const expr = (e: ts.Expression): Datum => {
    if (ts.isParenthesizedExpression(e)) return expr(e.expression);
    if (ts.isAwaitExpression(e)) return expr(e.expression);
    if (ts.isNumericLiteral(e)) return count(Number(e.text));
    if (ts.isStringLiteral(e) || ts.isNoSubstitutionTemplateLiteral(e)) return count(e.text);
    if (e.kind === ts.SyntaxKind.TrueKeyword) return count(true);
    if (e.kind === ts.SyntaxKind.FalseKeyword) return count(false);
    // Like `undefined`, null is a leaf to the analysis. No identifier can be named null.
    if (e.kind === ts.SyntaxKind.NullKeyword) return count(sym("js.null"));
    if (ts.isIdentifier(e)) return (useSite ? seeThrough(e) : undefined) ?? count(name(e));
    if (ts.isAsExpression(e) && ts.isConstTypeReference(e.type)) return expr(e.expression);
    if (ts.isArrowFunction(e)) {
      const { formals, bindings } = params(e);
      const body = ts.isBlock(e.body) ? block(e.body.statements, 0) : expr(e.body);
      return count([S.lambda, formals, withBindings(bindings, body)]);
    }
    // typeof has no effect, always returns and calls no user code, so a free call is sound. It is
  // conservative: the operand escapes, so `typeof g` inside g reads as g escaping.
    if (ts.isTypeOfExpression(e)) return count([sym("js.%typeof"), expr(e.expression)]);
    if (ts.isConditionalExpression(e)) return count([S.if, expr(e.condition), expr(e.whenTrue), expr(e.whenFalse)]);
    if (ts.isPrefixUnaryExpression(e)) {
      if (e.operator === ts.SyntaxKind.ExclamationToken) return count([S.not, expr(e.operand)]);
      if (e.operator === ts.SyntaxKind.MinusToken) return count([sym(isNumber(e.operand) ? "-" : "js.%-"), expr(e.operand)]);
      if (e.operator === ts.SyntaxKind.PlusToken) return count([sym(isNumber(e.operand) ? "+" : "js.%+"), expr(e.operand)]);
    }
    if (ts.isBinaryExpression(e)) {
      const op = e.operatorToken.kind;
      const prim = BINARY.get(op);
      if (prim) return arith(prim, e.left, e.right);
      if (op === ts.SyntaxKind.AmpersandAmpersandToken) return count([S.and, expr(e.left), expr(e.right)]);
      if (op === ts.SyntaxKind.BarBarToken) return count([S.or, expr(e.left), expr(e.right)]);
      // `or` passes a different set of left values through than `??`, but the analysis only needs
      // that either side may be the result.
      if (op === ts.SyntaxKind.QuestionQuestionToken) return count([S.or, expr(e.left), expr(e.right)]);
      if (op === ts.SyntaxKind.EqualsEqualsEqualsToken) return count([S.eqv, expr(e.left), expr(e.right)]);
      if (op === ts.SyntaxKind.ExclamationEqualsEqualsToken) return count([S.not, [S.eqv, expr(e.left), expr(e.right)]]);
      if (op === ts.SyntaxKind.EqualsToken && (ts.isPropertyAccessExpression(e.left) || ts.isElementAccessExpression(e.left))) {
        return fieldAssignment(e, e.left);
      }
      if (op === ts.SyntaxKind.EqualsToken) return count([S.set, name(e.left), expr(e.right)]);
      if (op === ts.SyntaxKind.PlusEqualsToken || op === ts.SyntaxKind.MinusEqualsToken) {
        const [v, step] = update(e, false);
        return count([S.set, name(v), step]);
      }
    }
    if ((ts.isPostfixUnaryExpression(e) || ts.isPrefixUnaryExpression(e)) &&
        (e.operator === ts.SyntaxKind.PlusPlusToken || e.operator === ts.SyntaxKind.MinusMinusToken)) {
      if (!ts.isExpressionStatement(e.parent)) throw new Unsupported(e, "++ and -- are lowered only as statements");
      const [v, step] = update(e, false);
      return count([S.set, name(v), step]);
    }
    if (ts.isTemplateExpression(e)) {
      const parts: Datum[] = e.head.text ? [e.head.text] : [];
      for (const span of e.templateSpans) {
        parts.push(expr(span.expression));
        if (span.literal.text) parts.push(span.literal.text);
      }
      return count([sym("string-append"), ...parts]);
    }
    if (ts.isArrayLiteralExpression(e)) {
      if (e.elements.some(ts.isSpreadElement)) return count([sym("append"), ...appendArgs(e.elements)]);
      return count([sym("list"), ...e.elements.map(expr)]);
    }
    if (ts.isObjectLiteralExpression(e) && e.properties.some(ts.isSpreadAssignment)) {
      // A spread copies fields the IR cannot place, so the object is a free call the analysis does
      // not model: a function read from it and called is an unresolved call. Each run of plain
      // properties is lowered as an object of its own, so the same rules apply to it.
      const parts: Datum[] = [];
      let run: ts.ObjectLiteralElementLike[] = [];
      const flush = () => {
        if (run.length > 0) parts.push(expr(ts.factory.updateObjectLiteralExpression(e, run)));
        run = [];
      };
      for (const p of e.properties) {
        if (!ts.isSpreadAssignment(p)) {
          run.push(p);
          continue;
        }
        if (!isRecord(p.expression)) throw new Unsupported(p, "only an object may be spread into an object");
        flush();
        parts.push(expr(p.expression));
      }
      flush();
      return count([sym("js.%spread"), ...parts]);
    }
    if (ts.isObjectLiteralExpression(e)) {
      // Keys are kept as strings so a member read can name its field. The termination port's cells
      // do not distinguish fields, so a vector is all the analysis needs.
      return count([sym("vector"), ...e.properties.flatMap((p): Datum[] => {
        if (p.name && (ts.isIdentifier(p.name) || ts.isStringLiteral(p.name)) && IMPLICIT.has(p.name.text)) {
          throw new Unsupported(p, `an object may not define ${p.name.text}, which JavaScript calls implicitly`);
        }
        if (p.name && (ts.isIdentifier(p.name) || ts.isStringLiteral(p.name)) && (ARRAY_MEMBERS.has(p.name.text) || /^\d+$/.test(p.name.text))) {
          throw new Unsupported(p, `an object may not define ${p.name.text}, which the checker reads as an array member`);
        }
        if (ts.isPropertyAssignment(p) && (ts.isIdentifier(p.name) || ts.isStringLiteral(p.name))) return [p.name.text, expr(p.initializer)];
        if (ts.isShorthandPropertyAssignment(p) && !p.objectAssignmentInitializer) return [p.name.text, count(name(p.name))];
        throw new Unsupported(p, "only plain `key: value` and shorthand properties are lowered yet");
      })]);
    }
    if ((ts.isPropertyAccessExpression(e) || ts.isElementAccessExpression(e)) && ts.isOptionalChain(e)) return optionalChain(e, (d) => d);
    if (ts.isPropertyAccessExpression(e) || ts.isElementAccessExpression(e)) {
      const read = member(e, () => expr(e.expression), false);
      if (read) return read;
    }
    // A call in an optional chain would have to run only when the receiver is not nullish, and a
    // method's lowering judges its receiver by a type that still admits undefined. `g?.()` on a
    // plain name is refused too: it would lower to an unconditional call.
    if (ts.isCallExpression(e) && ts.isOptionalChain(e)) {
      throw new Unsupported(e, "a call inside an optional chain is not lowered");
    }
    if (
      ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression) && !e.expression.questionDotToken &&
      HOFS.has(e.expression.name.text) && isArray(e.expression.expression)
    ) {
      const { prim, arity } = HOFS.get(e.expression.name.text)!;
      const [callback, ...rest] = e.arguments;
      if (!callback || rest.length !== arity - 1) throw new Unsupported(e, `${e.expression.name.text} takes a callback${arity > 1 ? " and an initial value" : ""}`);
      const taken = arityOf(callback);
      if (taken !== arity) {
        throw new Unsupported(callback, `the callback of ${e.expression.name.text} must take exactly ${arity} parameter${arity > 1 ? "s" : ""}`);
      }
      return count([sym(prim), expr(callback), ...rest.map(expr), expr(e.expression.expression)]);
    }
    // Any other method the lowering can vouch for is a call of a free name the analysis does not
    // model, so its arguments escape: a callback handed to it may be called with anything.
    if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression) && !e.expression.questionDotToken) {
      const receiver = e.expression.expression;
      const method = e.expression.name.text;
      if (ts.isIdentifier(receiver) && isLibGlobal(receiver)) {
        return call(sym(`js.${receiver.text}.${method}`), [], e.arguments);
      }
      if (isPrimitive(receiver) || (isArray(receiver) && (ARRAY_READERS.has(method) || REORDERS.has(method)))) {
        return call(sym(`js.method.${method}`), [expr(receiver)], e.arguments);
      }
      if (method === "push") {
        pushable(e, receiver);
        return call(sym("js.method.push"), [expr(receiver)], e.arguments);
      }
    }
    if (ts.isCallExpression(e) && ts.isIdentifier(e.expression)) {
      const omitted = filled(e.expression, e.arguments);
      const c = call(name(e.expression), [], e.arguments, recursesBack(e.expression));
      if (omitted.length > 0) (c as Datum[]).push(...omitted);
      return c;
    }
    throw new Unsupported(e, `${ts.SyntaxKind[e.kind]} is not lowered yet`);
  };

  // A member read on a receiver already lowered by `receiver`, or undefined when the lowering has no
  // form for it. nonNullable judges the receiver as the guard of an optional chain leaves it.
  const member = (e: ts.PropertyAccessExpression | ts.ElementAccessExpression, receiver: () => Datum, nonNullable: boolean): Datum | undefined => {
    const r = e.expression;
    if (ts.isPropertyAccessExpression(e)) {
      if (isArray(r, nonNullable) && e.name.text === "length") return count([sym("length"), receiver()]);
      if (isRecord(r, nonNullable)) return count([sym("vector-ref"), receiver(), e.name.text]);
      if (e.name.text === "length" && (typeOf(r, nonNullable).flags & ts.TypeFlags.StringLike) !== 0) return count([sym("string-length"), receiver()]);
      return undefined;
    }
    if (isRecord(r, nonNullable) && ts.isStringLiteral(e.argumentExpression)) return count([sym("vector-ref"), receiver(), e.argumentExpression.text]);
    // Not car or list-ref, whatever the type says. An optional property, an index signature, {} or
    // a narrowing kept across a call lets a string pass as an array, and "a"[0] is "a", a fixed point
    // that size-change would read as a decrease. The free call's arguments escape.
    if (isArray(r, nonNullable)) return count([sym("js.%index"), receiver(), expr(e.argumentExpression)]);
    return undefined;
  };

  // An optional chain, in continuation-passing style: k builds the rest of the chain around the value
  // of e. At a `?.` the receiver is bound to a temporary and everything after it, the rest of the
  // chain included, runs only when the temporary is not nullish, as `a?.b.c` skips `.c` too. A
  // parenthesis ends the chain, so `(a?.b).c` reads `.c` on the result like any other read.
  const optionalChain = (e: ts.PropertyAccessExpression | ts.ElementAccessExpression, k: (d: Datum) => Datum): Datum => {
    const r = e.expression;
    const inChain = (ts.isPropertyAccessExpression(r) || ts.isElementAccessExpression(r)) && ts.isOptionalChain(r);
    const readOn = (receiver: Datum): Datum => {
      const read = member(e, () => receiver, true);
      if (!read) throw new Unsupported(e, `${ts.SyntaxKind[e.kind]} is not lowered yet`);
      return k(read);
    };
    if (!e.questionDotToken) {
      if (!inChain) throw new Unsupported(e, `${ts.SyntaxKind[e.kind]} is not lowered yet`);
      return optionalChain(r, readOn);
    }
    const guarded = (receiver: Datum): Datum => {
      const t = sym(`%js.tmp${++temps}`);
      return count([S.letrec, [[t, receiver]], count([S.if, count([sym("js.%nullish"), t]), count([S.void]), readOn(t)])]);
    };
    return inChain ? optionalChain(r, guarded) : guarded(expr(r));
  };

  // A growing array breaks a loop bounded by its length, which assumes the length holds still. So
  // push is lowered only as a statement on a const bound to an array literal in the same function,
  // whose every other use is a length, an element read, a for...of or a return: nothing that could
  // alias it. A loop around the push may not read the array in its test or iterate it.
  const enclosingFunction = (n: ts.Node): ts.Node | undefined => {
    for (let p = n.parent; p; p = p.parent) if (ts.isFunctionLike(p)) return p;
    return undefined;
  };
  // On the name of a shorthand property the checker answers with the property, so `{ a }` asks for
  // the variable it reads.
  const symbolOf = (id: ts.Identifier): ts.Symbol | undefined =>
    ts.isShorthandPropertyAssignment(id.parent) && id.parent.name === id
      ? checker.getShorthandAssignmentValueSymbol(id.parent)
      : checker.getSymbolAtLocation(id);
  const pushable = (call: ts.CallExpression, receiver: ts.Expression): void => {
    const refuse = (why: string): never => {
      throw new Unsupported(call, `push is lowered only ${why}`);
    };
    if (!ts.isExpressionStatement(call.parent)) refuse("as a statement");
    const target = ts.isIdentifier(receiver) ? checker.getSymbolAtLocation(receiver) : undefined;
    const decl = target?.valueDeclaration;
    if (
      !target || !decl || !ts.isVariableDeclaration(decl) || !ts.isIdentifier(decl.name) ||
      !(decl.parent.flags & ts.NodeFlags.Const) || !decl.initializer || !ts.isArrayLiteralExpression(skipParens(decl.initializer))
    ) {
      throw new Unsupported(call, "push is lowered only on a const bound to an array literal");
    }
    const home = enclosingFunction(decl);
    if (enclosingFunction(call) !== home) refuse("in the function that declares the array");
    const refs = (n: ts.Node): ts.Identifier[] =>
      ts.isIdentifier(n) && n !== decl.name && symbolOf(n) === target ? [n] : n.getChildren(sf).flatMap(refs);
    for (const r of refs(sf)) {
      const p = r.parent;
      const ok =
        (ts.isPropertyAccessExpression(p) && p.expression === r &&
          (p.name.text === "length" || (p.name.text === "push" && ts.isCallExpression(p.parent) && ts.isExpressionStatement(p.parent.parent)))) ||
        (ts.isElementAccessExpression(p) && p.expression === r && !(ts.isBinaryExpression(p.parent) && p.parent.left === p)) ||
        (ts.isForOfStatement(p) && p.expression === r) ||
        // A HOF, a reader or a spread copies the elements out and keeps no hold on the array. A
        // HOF's callback cannot reach it either, since its arity, read from its definition, leaves out the array argument.
        (ts.isPropertyAccessExpression(p) && p.expression === r && ts.isCallExpression(p.parent) && p.parent.expression === p &&
          (HOFS.has(p.name.text) || (ARRAY_READERS.has(p.name.text) && p.name.text !== "slice"))) ||
        (ts.isSpreadElement(p) && p.expression === r) ||
        // A return hands the array out of the function, so only the declaring function may return it.
        (ts.isReturnStatement(p) && p.expression === r && enclosingFunction(r) === home);
      if (!ok) throw new Unsupported(r, "an array that is pushed to may only be read by length, index, for...of or return");
    }
    const mentions = (n: ts.Node | undefined): boolean =>
      !!n && ((ts.isIdentifier(n) && symbolOf(n) === target) || n.getChildren(sf).some(mentions));
    for (let n: ts.Node = call; n.parent && n.parent !== home; n = n.parent) {
      const loop = n.parent;
      const header =
        ts.isForStatement(loop) ? [loop.initializer, loop.condition, loop.incrementor] :
        ts.isForOfStatement(loop) ? [loop.expression] :
        ts.isWhileStatement(loop) || ts.isDoStatement(loop) ? [loop.expression] : [];
      if (header.some(mentions)) throw new Unsupported(call, "a loop may not push to the array it iterates or tests");
    }
  };

  // HC-33: a field write breaks a loop or a recursion bounded by that field, as push breaks one
  // bounded by a length. So it is lowered under rules that mirror pushable(): a statement `o.k = v`
  // with a literal key, on a const bound to an object literal in the same function, whose every other
  // use is a field read, Object.keys/entries/values or a return. The object may not appear in a loop
  // header, the condition of an if in a recursive function, or an argument of a recursive call. The
  // write is the free call js.%put, and vector-ref is no stable bound, so the IR already refuses such
  // a loop; the rules keep the field out of every place a bound is read. A string key reaching the
  // field from a variable stays refused by the computed-access gate, since it could name constructor.
  const fieldAssignment = (e: ts.BinaryExpression, target: ts.PropertyAccessExpression | ts.ElementAccessExpression): Datum => {
    const refuse = (n: ts.Node, why: string): never => {
      throw new Unsupported(n, `a field is assigned only ${why}`);
    };
    if (ts.isOptionalChain(target)) refuse(target, "without ?.");
    const key = ts.isPropertyAccessExpression(target) ? target.name.text
      : ts.isStringLiteral(target.argumentExpression) ? target.argumentExpression.text : refuse(target, "under a literal key");
    if (IMPLICIT.has(key) || ARRAY_MEMBERS.has(key) || /^\d+$/.test(key)) {
      refuse(target, `under a key other than ${key}, which JavaScript calls implicitly or the checker reads as an array member`);
    }
    if (!callFree(checker.getTypeAtLocation(e.right), e.right)) refuse(e.right, "a value whose type can hold no function");
    assignable(e, skipParens(target.expression));
    return count([sym("js.%put"), expr(target.expression), key, expr(e.right)]);
  };
  // Whether no value of type t can be or hold a function. A stored closure is one 0CFA would not see,
  // and an object holding one could define a member JavaScript calls implicitly. A type that hides
  // its values, unknown or object, could hold anything.
  const HIDES = ts.TypeFlags.Any | ts.TypeFlags.Unknown | ts.TypeFlags.NonPrimitive | ts.TypeFlags.TypeParameter |
    ts.TypeFlags.IndexedAccess | ts.TypeFlags.Conditional | ts.TypeFlags.Substitution;
  const callFree = (t: ts.Type, at: ts.Node, seen = new Set<ts.Type>()): boolean => {
    if (seen.has(t)) return true;
    seen.add(t);
    if (t.flags & HIDES) return false;
    if (t.isUnionOrIntersection()) return t.types.every((u) => callFree(u, at, seen));
    if (!(t.flags & ts.TypeFlags.Object)) return true;
    if (t.getCallSignatures().length > 0 || t.getConstructSignatures().length > 0) return false;
    if (checker.isArrayType(t) || checker.isTupleType(t)) {
      return checker.getTypeArguments(t as ts.TypeReference).every((u) => callFree(u, at, seen));
    }
    return checker.getPropertiesOfType(t).every((p) => callFree(checker.getTypeOfSymbolAtLocation(p, at), at, seen)) &&
      checker.getIndexInfosOfType(t).every((i) => callFree(i.type, at, seen));
  };
  const OBJECT_READERS = new Set(["keys", "entries", "values"]);
  const recursive = (fn: ts.Node): boolean => {
    const seen = new Set<ts.Node>();
    const work = [...namedFunctions(fn)];
    while (work.length > 0) {
      const f = work.pop()!;
      if (f === fn) return true;
      if (seen.has(f)) continue;
      seen.add(f);
      work.push(...namedFunctions(f));
    }
    return false;
  };
  const assignable = (e: ts.BinaryExpression, receiver: ts.Expression): void => {
    if (!ts.isExpressionStatement(e.parent)) throw new Unsupported(e, "a field is assigned only as a statement");
    const target = ts.isIdentifier(receiver) ? checker.getSymbolAtLocation(receiver) : undefined;
    const decl = target?.valueDeclaration;
    if (
      !target || !decl || !ts.isVariableDeclaration(decl) || !ts.isIdentifier(decl.name) ||
      !(decl.parent.flags & ts.NodeFlags.Const) || !decl.initializer || !ts.isObjectLiteralExpression(skipParens(decl.initializer)) ||
      (skipParens(decl.initializer) as ts.ObjectLiteralExpression).properties.some(ts.isSpreadAssignment)
    ) {
      throw new Unsupported(e, "a field is assigned only on a const bound to an object literal without spread");
    }
    const home = enclosingFunction(decl);
    if (enclosingFunction(e) !== home) throw new Unsupported(e, "a field is assigned only in the function that declares the object");
    const refs = (n: ts.Node): ts.Identifier[] =>
      ts.isIdentifier(n) && n !== decl.name && symbolOf(n) === target ? [n] : n.getChildren(sf).flatMap(refs);
    const fieldWrite = (p: ts.Node): boolean =>
      ts.isBinaryExpression(p.parent) && p.parent.left === p && p.parent.operatorToken.kind === ts.SyntaxKind.EqualsToken &&
      ts.isExpressionStatement(p.parent.parent);
    const assigning = (p: ts.Node): boolean =>
      (ts.isBinaryExpression(p.parent) && p.parent.left === p &&
        p.parent.operatorToken.kind >= ts.SyntaxKind.FirstAssignment && p.parent.operatorToken.kind <= ts.SyntaxKind.LastAssignment) ||
      ((ts.isPostfixUnaryExpression(p.parent) || ts.isPrefixUnaryExpression(p.parent)) &&
        (p.parent.operator === ts.SyntaxKind.PlusPlusToken || p.parent.operator === ts.SyntaxKind.MinusMinusToken));
    const objectReader = (p: ts.Node, r: ts.Identifier): boolean =>
      ts.isCallExpression(p) && p.arguments.length === 1 && p.arguments[0] === r && ts.isPropertyAccessExpression(p.expression) &&
      ts.isIdentifier(p.expression.expression) && p.expression.expression.text === "Object" && isLibGlobal(p.expression.expression) &&
      OBJECT_READERS.has(p.expression.name.text);
    for (const r of refs(sf)) {
      const p = r.parent;
      const field =
        (ts.isPropertyAccessExpression(p) || (ts.isElementAccessExpression(p) && ts.isStringLiteral(p.argumentExpression))) &&
        p.expression === r && !(ts.isCallExpression(p.parent) && p.parent.expression === p) && (!assigning(p) || fieldWrite(p));
      const ok = field || objectReader(p, r) || (ts.isReturnStatement(p) && p.expression === r && enclosingFunction(r) === home);
      if (!ok) throw new Unsupported(r, "an object whose field is assigned may only be read by field, Object.keys/entries/values or return");
      for (let n: ts.Node = r; n.parent; n = n.parent) {
        const q = n.parent;
        const inHeader =
          ts.isForStatement(q) ? n === q.initializer || n === q.condition || n === q.incrementor :
          ts.isWhileStatement(q) || ts.isDoStatement(q) ? n === q.expression :
          ts.isForOfStatement(q) ? n === q.expression && !(objectReader(p, r) && skipParens(q.expression) === p) : false;
        if (inHeader) throw new Unsupported(r, "a loop may not test or iterate an object whose field is assigned");
        const inTest = (ts.isIfStatement(q) && n === q.expression) || (ts.isConditionalExpression(q) && n === q.condition);
        const caller = inTest ? namedCaller(q) : undefined;
        if (caller && recursive(caller)) throw new Unsupported(r, "a recursive function may not test an object whose field is assigned");
        if (ts.isCallExpression(q) && q.arguments.includes(n as ts.Expression) && ts.isIdentifier(q.expression) && recursesBack(q.expression)) {
          throw new Unsupported(r, "a recursive call may not pass an object whose field is assigned");
        }
      }
    }
  };

  // An update statement or the counter update of a loop: which variable it steps, and the step
  // expression. A loop may only step a number, since the loop rules read the step as arithmetic.
  const update = (e: ts.Expression, loop: boolean): [ts.Identifier, Datum] => {
    const target = ts.isBinaryExpression(e) ? e.left : ts.isPostfixUnaryExpression(e) || ts.isPrefixUnaryExpression(e) ? e.operand : e;
    if (loop && ts.isIdentifier(target) && !isNumber(target)) throw new Unsupported(e, "a loop's update must step a number");
    if ((ts.isPostfixUnaryExpression(e) || ts.isPrefixUnaryExpression(e)) && ts.isIdentifier(e.operand)) {
      const prim = isNumber(e.operand) ? "" : "js.%";
      if (e.operator === ts.SyntaxKind.PlusPlusToken) return [e.operand, count([sym(`${prim}+`), name(e.operand), 1])];
      if (e.operator === ts.SyntaxKind.MinusMinusToken) return [e.operand, count([sym(`${prim}-`), name(e.operand), 1])];
    }
    if (ts.isBinaryExpression(e) && ts.isIdentifier(e.left)) {
      const op = e.operatorToken.kind;
      if (op === ts.SyntaxKind.PlusEqualsToken) return [e.left, arith("+", e.left, e.right)];
      if (op === ts.SyntaxKind.MinusEqualsToken) return [e.left, arith("-", e.left, e.right)];
      if (op === ts.SyntaxKind.EqualsToken) return [e.left, expr(e.right)];
    }
    throw new Unsupported(e, "a loop's update must be ++, --, +=, -= or = on one variable");
  };

  // The do loop rebinds a loop's variable, so a write to it from inside another function would
  // change the outer binding and never the one the loop tests. Every write must sit in the function
  // that holds the loop.
  const writtenOnlyHere = (v: ts.Identifier, loop: ts.Node): void => {
    const target = checker.getSymbolAtLocation(v);
    const home = enclosingFunction(loop);
    const isWrite = (id: ts.Identifier): boolean => {
      const p = id.parent;
      if (ts.isBinaryExpression(p) && p.left === id) {
        const k = p.operatorToken.kind;
        return k >= ts.SyntaxKind.FirstAssignment && k <= ts.SyntaxKind.LastAssignment;
      }
      return (ts.isPostfixUnaryExpression(p) || ts.isPrefixUnaryExpression(p)) &&
        (p.operator === ts.SyntaxKind.PlusPlusToken || p.operator === ts.SyntaxKind.MinusMinusToken);
    };
    const visit = (n: ts.Node): void => {
      if (ts.isIdentifier(n) && checker.getSymbolAtLocation(n) === target && isWrite(n) && enclosingFunction(n) !== home) {
        throw new Unsupported(n, `a loop's variable ${v.text} may not be assigned from inside another function`);
      }
      n.getChildren(sf).forEach(visit);
    };
    if (target) visit(sf);
  };

  const loopBody = (b: ts.Statement): Datum => block(ts.isBlock(b) ? b.statements : [b], 0, true);

  const forLoop = (s: ts.ForStatement): Datum => {
    const init = s.initializer;
    if (!init || !ts.isVariableDeclarationList(init) || !(init.flags & ts.NodeFlags.Let)) {
      throw new Unsupported(s, "a for loop must declare its variables with let");
    }
    if (!s.condition) throw new Unsupported(s, "a for loop needs a condition");
    if (!s.incrementor) throw new Unsupported(s, "a for loop needs an update");
    const [counter, step] = update(s.incrementor, true);
    writtenOnlyHere(counter, s);
    if (!init.declarations.some((d) => ts.isIdentifier(d.name) && d.name.text === counter.text)) {
      throw new Unsupported(s.incrementor, "a for loop's update must step a variable the loop declares");
    }
    // do evaluates its inits outside the loop's scope, where a name the loop declares would be free.
    const declared = new Set(init.declarations.flatMap((d) => (ts.isIdentifier(d.name) ? [d.name.text] : [])));
    const mentions = (n: ts.Node): ts.Node | undefined =>
      ts.isIdentifier(n) && declared.has(n.text) ? n : ts.forEachChild(n, mentions);
    const bindings = init.declarations.map((d): Datum => {
      if (!d.initializer) throw new Unsupported(d, "a binding needs an initializer");
      const inner = mentions(d.initializer);
      if (inner) throw new Unsupported(inner, "a for initializer may not name a variable of the same loop");
      const v = name(d.name);
      return ts.isIdentifier(d.name) && d.name.text === counter.text ? [v, expr(d.initializer), step] : [v, expr(d.initializer)];
    });
    return count([S.do, bindings, [exitTest(s.condition)], loopBody(s.statement)]);
  };

  // A for loop exits when its condition is false. The do-loop rules read a comparison, not its
  // negation, so `i < n` exits on (>= i n). The two differ only when an operand is NaN, where the
  // JavaScript loop exits at once and the IR's loop would not, so the flip can only over-reject.
  const exitTest = (c: ts.Expression): Datum => {
    const e = skipParens(c);
    if (ts.isBinaryExpression(e)) {
      const flipped = FLIPPED.get(e.operatorToken.kind);
      if (flipped) return isNumber(e.left) && isNumber(e.right) ? count([sym(flipped), expr(e.left), expr(e.right)]) : count([S.not, expr(c)]);
    }
    return count([S.not, expr(c)]);
  };

  // The narrow while of the plan: the body ends in one update of the stepped variable, which also
  // rules out a `continue` that would skip it. The do loop rebinds that variable, so its final value
  // is assigned back to the outer binding the rest of the function reads.
  const whileLoop = (s: ts.WhileStatement): Datum => {
    const body = ts.isBlock(s.statement) ? s.statement.statements : [s.statement];
    const last = body[body.length - 1];
    if (!last || !ts.isExpressionStatement(last)) throw new Unsupported(s, "a while body must end in an update of the variable it tests");
    const [v, step] = update(last.expression, true);
    writtenOnlyHere(v, s);
    const loop = [S.do, [[name(v), name(v), step]], [exitTest(s.expression), name(v)], block(body.slice(0, -1), 0, true)];
    return count([S.set, name(v), count(loop)]);
  };

  const forOf = (s: ts.ForOfStatement): Datum => {
    const init = s.initializer;
    if (s.awaitModifier) throw new Unsupported(s, "for await is not lowered");
    if (!ts.isVariableDeclarationList(init) || init.declarations.length !== 1 || !(init.flags & (ts.NodeFlags.Let | ts.NodeFlags.Const))) {
      throw new Unsupported(s, "a for...of loop must declare one element with const or let");
    }
    if (!isArray(s.expression)) throw new Unsupported(s.expression, "for...of is lowered only over an array");
    const head = init.declarations[0].name;
    if (ts.isIdentifier(head)) return count([sym("for-each"), [S.lambda, [name(head)], loopBody(s.statement)], expr(s.expression)]);
    // HC-38: a pattern in the head binds a temporary, destructured at the top of the body, as a
    // destructuring parameter is.
    if (ts.isObjectBindingPattern(head) ? !isRecord(head) : !isArrayNode(head)) {
      throw new Unsupported(head, "a destructuring pattern must match an object or array type");
    }
    const t = sym(`%js.tmp${++temps}`);
    const bindings: Datum[][] = [];
    destructure(head, t, bindings);
    return count([sym("for-each"), [S.lambda, [t], withBindings(bindings, loopBody(s.statement))], expr(s.expression)]);
  };

  // stmts[i..] as one expression; falling off the end is (void). Inside a loop body a return has no
  // lowering, because the loop would have to stop.
  const block = (stmts: readonly ts.Statement[], i: number, inLoop = false): Datum => {
    if (i >= stmts.length) return count([S.void]);
    const s = stmts[i];
    if (ts.isReturnStatement(s)) {
      if (inLoop) throw new Unsupported(s, "a return inside a loop is not lowered");
      return s.expression ? expr(s.expression) : count([S.void]);
    }
    if (ts.isThrowStatement(s)) return count([sym("raise"), expr(s.expression)]);
    if (isTypeOnly(s)) return block(stmts, i + 1, inLoop);
    if (ts.isBlock(s)) return block([...s.statements, ...stmts.slice(i + 1)], 0, inLoop);
    if (ts.isForStatement(s)) return count([S.begin, forLoop(s), block(stmts, i + 1, inLoop)]);
    if (ts.isForOfStatement(s)) return count([S.begin, forOf(s), block(stmts, i + 1, inLoop)]);
    if (ts.isWhileStatement(s)) return count([S.begin, whileLoop(s), block(stmts, i + 1, inLoop)]);
    if (ts.isVariableStatement(s)) {
      const bindings = s.declarationList.declarations.flatMap(declare);
      return count([S.letrec, bindings, block(stmts, i + 1, inLoop)]);
    }
    if (ts.isIfStatement(s)) {
      const branch = (b: ts.Statement | undefined): Datum =>
        block([...(b ? (ts.isBlock(b) ? b.statements : [b]) : []), ...stmts.slice(i + 1)], 0, inLoop);
      return count([S.if, expr(s.expression), branch(s.thenStatement), branch(s.elseStatement)]);
    }
    if (ts.isSwitchStatement(s)) return switchStatement(s, stmts.slice(i + 1), inLoop);
    if (ts.isTryStatement(s)) {
      // The rest of the block runs inside the guard, so the IR also catches what the rest raises.
      // That only adds paths, so it can over-reject but never accept a loop the program has.
      if (s.finallyBlock) throw new Unsupported(s.finallyBlock, "finally is not lowered yet");
      const rest = stmts.slice(i + 1);
      const c = s.catchClause!;
      const v = c.variableDeclaration ? name(c.variableDeclaration.name) : sym("%e");
      return count([S.guard, [v, [true, block([...c.block.statements, ...rest], 0, inLoop)]], block([...s.tryBlock.statements, ...rest], 0, inLoop)]);
    }
    if (ts.isExpressionStatement(s)) return count([S.begin, expr(s.expression), block(stmts, i + 1, inLoop)]);
    throw new Unsupported(s, `${ts.SyntaxKind[s.kind]} is not lowered yet`);
  };

  // A switch becomes nested ifs on eqv?, which is ===, so the discriminant must be a variable to be
  // read more than once. A case ends in return, throw or a final break, which continues with the rest
  // of the block; empty cases share the next body. A break anywhere else is a BreakStatement and stays
  // unsupported, as does a default that is not last.
  const switchStatement = (s: ts.SwitchStatement, rest: readonly ts.Statement[], inLoop: boolean): Datum => {
    if (!ts.isIdentifier(skipParens(s.expression))) throw new Unsupported(s.expression, "a switch must test a variable");
    const subject = name(skipParens(s.expression));
    const clauses = s.caseBlock.clauses;
    const lowerFrom = (k: number): Datum => {
      if (k >= clauses.length) return block(rest, 0, inLoop);
      const tests: Datum[] = [];
      let j = k;
      while (ts.isCaseClause(clauses[j]) && clauses[j].statements.length === 0 && j + 1 < clauses.length) {
        tests.push(count([S.eqv, subject, expr((clauses[j] as ts.CaseClause).expression)]));
        j++;
      }
      const clause = clauses[j];
      if (ts.isDefaultClause(clause) && (j !== clauses.length - 1 || tests.length > 0)) {
        throw new Unsupported(clause, "default must be the last case of a switch, on its own");
      }
      const body = clause.statements;
      const last = body[body.length - 1];
      const ends = last && (ts.isReturnStatement(last) || ts.isThrowStatement(last));
      if (!last || (!ends && !ts.isBreakStatement(last)) || (ts.isBreakStatement(last) && last.label)) {
        throw new Unsupported(clause, "a case must end in return, throw or break; falling through is not lowered");
      }
      const lowered = block([...(ends ? body : body.slice(0, -1)), ...rest], 0, inLoop);
      if (ts.isDefaultClause(clause)) return lowered;
      tests.push(count([S.eqv, subject, expr(clause.expression)]));
      const test = tests.length === 1 ? tests[0] : count([S.or, ...tests]);
      return count([S.if, test, lowered, lowerFrom(j + 1)]);
    };
    return lowerFrom(0);
  };

  // Types are erased at run time, so a type alias or an interface lowers to nothing.
  const isTypeOnly = (s: ts.Statement): boolean => ts.isTypeAliasDeclaration(s) || ts.isInterfaceDeclaration(s);

  const top = (s: ts.Statement): Datum[] => {
    if (isTypeOnly(s)) return [];
    if (ts.isFunctionDeclaration(s) && s.name && s.body) {
      const { formals, bindings } = params(s);
      return [count([S.define, [name(s.name), ...formals], withBindings(bindings, block(s.body.statements, 0))])];
    }
    if (ts.isVariableStatement(s)) {
      return s.declarationList.declarations.flatMap(declare).map(([v, init]) => count([S.define, v, init]));
    }
    if (ts.isExpressionStatement(s)) return [expr(s.expression)];
    // Any other statement lowers as a block of its own. No return can reach the top level, so the
    // statements after it need not be copied into its branches.
    return [block([s], 0)];
  };

  try {
    return { ir: sf.statements.flatMap(top), violations: [] };
  } catch (err) {
    if (!(err instanceof Unsupported)) throw err;
    const { line, character } = sf.getLineAndCharacterOfPosition(err.node.getStart(sf));
    return { ir: [], violations: [{ kind: "unsupported-syntax", message: err.message, line: line + 1, column: character + 1 }] };
  }
}
