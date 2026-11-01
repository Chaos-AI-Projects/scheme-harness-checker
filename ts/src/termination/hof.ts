// Phase 7 of termination.ss (HC-17): HOF callbacks. A user-defined function passed by name to a
// collection HOF, or to a user-defined HOF that is itself proven terminating, must be proven
// terminating too.

import { car, cdr, isList, isPair, isSym, sym, type Datum, type Sym } from "../sexp.ts";
import { isCollectionHof, properPrefix, type Definition } from "./callgraph.ts";
import { findFormalsFor } from "./directrec.ts";
import type { TerminationViolation } from "./violation.ts";

const QUOTE = sym("quote");
const DEFINE = sym("define");
const ELLIPSIS = sym("...");

// termination.ss:138 collection-hof-callback-position. Every other collection HOF takes no callback.
// cfa.ss keeps its own table, which also has partition, so this one is not cfaHofCallbackPosition.
const CALLBACK_AT_ZERO = new Set(
  [
    "map", "for-each", "filter", "remove", "remp", "fold-left", "fold-right", "find", "exists",
    "for-all", "memp", "vector-map", "vector-for-each", "string-for-each",
  ].map(sym),
);

/** termination.ss:149 hof-callback-position: a collection HOF's callback index, or null. */
export function hofCallbackPosition(name: Datum): number | null {
  return isSym(name) && CALLBACK_AT_ZERO.has(name) ? 0 : null;
}

/** A call passing a callback by name: the caller, the HOF called, and the callback's name. */
export type CallbackEdge = readonly [caller: Sym, hof: Sym, callback: Sym];

/**
 * The calls in bodyExprs whose operator is a HOF, per hofPosition, and whose argument at that
 * position is a symbol, as termination.ss's walkers find them: an application's operands before its
 * operator, quoted forms skipped. Edges come last-found first, as the Scheme conses them.
 */
function callbackEdges(
  bodyExprs: readonly Datum[],
  caller: Sym,
  hofPosition: (head: Sym) => number | null,
): CallbackEdge[] {
  const edges: CallbackEdge[] = [];
  function walk(expr: Datum): void {
    if (!isPair(expr) || car(expr) === QUOTE) return;
    const head = car(expr);
    const args = cdr(expr);
    if (isSym(head)) {
      const pos = hofPosition(head);
      if (pos !== null && isList(args) && args.length > pos && isSym(args[pos]!)) edges.push([caller, head, args[pos]]);
    }
    properPrefix(args).forEach(walk);
    if (isPair(head)) walk(head);
  }
  properPrefix(bodyExprs as Datum[]).forEach(walk);
  return edges.reverse();
}

/** termination.ss:332 collect-hof-callback-edges: callbacks passed by name to collection HOFs. */
export function collectHofCallbackEdges(bodyExprs: readonly Datum[], caller: Sym): CallbackEdge[] {
  return callbackEdges(bodyExprs, caller, (head) => (isCollectionHof(head) ? hofCallbackPosition(head) : null));
}

/** A user-defined HOF and the index of its first formal called as a function. */
export type UserHof = readonly [name: Sym, position: number];

/** termination.ss:355 collect-user-hof-callback-edges: callbacks passed by name to user HOFs. */
export function collectUserHofCallbackEdges(bodyExprs: readonly Datum[], caller: Sym, userHofs: readonly UserHof[]): CallbackEdge[] {
  return callbackEdges(bodyExprs, caller, (head) => userHofs.find(([n]) => n === head)?.[1] ?? null);
}

/** termination.ss:377 param-in-call-position?: whether name is the operator of some application. */
export function paramInCallPosition(name: Sym, bodyExprs: readonly Datum[]): boolean {
  let found = false;
  function walk(expr: Datum): void {
    if (found || !isPair(expr) || car(expr) === QUOTE) return;
    if (car(expr) === name) found = true;
    if (isPair(car(expr))) walk(car(expr));
    properPrefix(cdr(expr)).forEach(walk);
  }
  properPrefix(bodyExprs as Datum[]).forEach(walk);
  return found;
}

/**
 * termination.ss:398 detect-user-defined-hofs: each definition that calls one of its formals, with
 * the first such formal's index, in definition order. Collection HOFs are excluded, and a name
 * defined twice takes its first entry.
 */
export function detectUserDefinedHofs(defs: readonly Definition[], exprs: readonly Datum[]): UserHof[] {
  const result: UserHof[] = [];
  for (const [name, body] of defs) {
    const formals = findFormalsFor(exprs, name);
    if (formals === null || formals.length === 0 || isCollectionHof(name)) continue;
    for (let pos = 0; pos < formals.length && !result.some(([n]) => n === name); pos++) {
      const f = formals[pos]!;
      if (isSym(f) && paramInCallPosition(f, body)) result.push([name, pos]);
    }
  }
  return result;
}

/**
 * termination.ss:2847 check-hof-callbacks: a violation for each user-defined callback not proven
 * terminating, passed to a collection HOF or to a user-defined HOF that is proven terminating. A
 * HOF not proven terminating is flagged on its own. The violation's form is a stand-in
 * (define name ...), as the Scheme's is.
 */
export function checkHofCallbacks(
  defs: readonly Definition[],
  definedNames: readonly Sym[],
  provenTerminating: readonly Sym[],
  userHofs: readonly UserHof[] = [],
): TerminationViolation[] {
  const violations: TerminationViolation[] = [];
  const unproven = (cb: Sym): boolean => definedNames.includes(cb) && !provenTerminating.includes(cb);
  for (const [fname, body] of defs) {
    const add = (reason: string): void => {
      violations.push({ kind: "hof-callback-not-terminating", function: fname, expr: [DEFINE, fname, ELLIPSIS], reason });
    };
    for (const [, , cb] of collectHofCallbackEdges(body, fname)) {
      if (unproven(cb)) add(`HOF callback "${cb.name}" passed in function "${fname.name}" is not proven terminating`);
    }
    for (const [, hof, cb] of collectUserHofCallbackEdges(body, fname, userHofs)) {
      if (provenTerminating.includes(hof) && unproven(cb)) {
        add(`HOF callback "${cb.name}" passed to user-defined HOF "${hof.name}" in function "${fname.name}" is not proven terminating`);
      }
    }
  }
  return violations;
}
