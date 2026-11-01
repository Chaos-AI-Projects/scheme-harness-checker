// Name sets the gate needs. Type lies are cheap in TypeScript (covariant arrays, method
// bivariance, type predicates), so a member's declared type cannot be what keeps a program away
// from the builtins. These sets work by name instead.

import ts from "typescript";

// Denied in every position, whatever the lib or the tools declare.
export const ALWAYS_FORBIDDEN = new Set([
  "constructor", "__proto__", "prototype", "caller", "callee", "arguments",
  "__defineGetter__", "__defineSetter__", "__lookupGetter__", "__lookupSetter__",
]);

// Every property name on the intrinsics a program can hold a reference to whose value is a
// function or an object, or which is an accessor. Read from this realm, walked to a fixed point
// through property values and prototypes, so it covers the members ts-safe.d.ts leaves out.
export const BUILTIN_MEMBERS: ReadonlySet<string> = (() => {
  const roots: unknown[] = [
    Object, Function, Array, String, Number, Boolean, Symbol, Math, JSON, Promise, Error,
    TypeError, RangeError, SyntaxError, ReferenceError, EvalError, URIError, AggregateError,
    () => 1, async () => 1, Promise.resolve(), [][Symbol.iterator](), ""[Symbol.iterator](),
    new Map().entries(),
  ];
  const names = new Set<string>();
  const seen = new Set<unknown>();
  const queue = [...roots];
  while (queue.length > 0) {
    const value = queue.pop();
    if ((typeof value !== "object" && typeof value !== "function") || value === null) continue;
    if (seen.has(value) || value === globalThis) continue;
    seen.add(value);
    queue.push(Object.getPrototypeOf(value));
    for (const name of Object.getOwnPropertyNames(value)) {
      const d = Object.getOwnPropertyDescriptor(value, name);
      if (!d) continue;
      if (d.get || d.set) {
        names.add(name);
        queue.push(d.get, d.set);
      } else if ((typeof d.value === "object" && d.value !== null) || typeof d.value === "function") {
        names.add(name);
        queue.push(d.value);
      }
    }
  }
  return names;
})();

// A known limit: declared member names form one flat set, not one set per receiver. A name the lib
// declares on one type (entries on Object) is readable on any value a type lie reaches, such as
// Array.prototype.entries, and a tool's member names widen the set the same way. No path from
// those names to Function is known; the QuickJS realm is the layer that covers what remains.

export interface Declared {
  /** Value names declared at top level: lib globals or tool functions. */
  values: Set<string>;
  /** Interface and type alias names. */
  types: Set<string>;
  /** Property and method names in any declared type. */
  members: Set<string>;
}

export function declaredNames(sf: ts.SourceFile): Declared {
  const out: Declared = { values: new Set(), types: new Set(), members: new Set() };
  for (const stmt of sf.statements) {
    if (ts.isVariableStatement(stmt)) {
      for (const d of stmt.declarationList.declarations) {
        if (ts.isIdentifier(d.name)) out.values.add(d.name.text);
      }
    } else if ((ts.isFunctionDeclaration(stmt) || ts.isClassDeclaration(stmt) || ts.isEnumDeclaration(stmt) ||
                ts.isModuleDeclaration(stmt)) && stmt.name && ts.isIdentifier(stmt.name)) {
      out.values.add(stmt.name.text);
    } else if (ts.isInterfaceDeclaration(stmt) || ts.isTypeAliasDeclaration(stmt)) {
      out.types.add(stmt.name.text);
    }
  }
  const visit = (node: ts.Node): void => {
    if ((ts.isPropertySignature(node) || ts.isMethodSignature(node) || ts.isPropertyDeclaration(node) ||
         ts.isMethodDeclaration(node)) && (ts.isIdentifier(node.name) || ts.isStringLiteralLike(node.name))) {
      out.members.add(node.name.text);
    }
    ts.forEachChild(node, visit);
  };
  visit(sf);
  return out;
}
