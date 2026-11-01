// Termination Phase 2, ported from src/harness-checker/termination.ss: definition extraction, the
// call graph over defined names, and Tarjan's strongly connected components.
//
// The graph sees a call only when its operator is a defined name; cfa-rewrite-program (Phase 2b)
// is what makes other calls visible to it. Results keep the Scheme's list order, which the later
// phases' violation order follows.

import { Dotted, car, cdr, elements, isList, isPair, isSym, sym, type Datum, type Sym } from "../sexp.ts";

/** A definition: its name and its body expressions, every clause's for a case-lambda. */
export type Definition = readonly [name: Sym, body: Datum[]];

/** Each definition's name and the defined names it calls, in definition order. */
export type CallGraph = readonly (readonly [name: Sym, callees: Sym[]])[];

const QUOTE = sym("quote");
const DEFINE = sym("define");
const LAMBDA = sym("lambda");
const CASE_LAMBDA = sym("case-lambda");
const LETREC = sym("letrec");
const LETREC_STAR = sym("letrec*");

// Built-in HOFs that iterate over a finite collection. set-cdr! is not on the harness whitelist, so
// their inputs are proper lists and the iteration terminates; the callbacks are Phase 7's to check.
const COLLECTION_HOF_NAMES = new Set(
  [
    "map", "for-each", "filter", "remove", "remp", "remv", "remq", "fold-left", "fold-right", "find",
    "exists", "for-all", "memp", "memv", "memq", "assoc", "assv", "assq", "vector-map",
    "vector-for-each", "string-for-each",
  ].map(sym),
);

export function isCollectionHof(d: Datum): boolean {
  return isSym(d) && COLLECTION_HOF_NAMES.has(d);
}

/**
 * Scheme's for-each-sub: the elements of a list's proper prefix. A dotted form such as the formals
 * (f a . rest) ends in a symbol, and a walker that recurses into it must not raise (HC-3).
 */
export function properPrefix(d: Datum): Datum[] {
  if (Array.isArray(d)) return d;
  if (d instanceof Dotted) return d.items;
  return [];
}

// The bodies of a case-lambda's clauses, concatenated. A dotted clause body keeps its proper prefix,
// as the Scheme's append keeps it, so a self-call there stays on the graph (HC-17).
function caseLambdaBodies(clauses: Datum): Datum[] {
  return elements(clauses).flatMap((c) => (isPair(c) ? properPrefix(cdr(c)) : []));
}

const isLambdaHead = (d: Datum): boolean => isPair(d) && (car(d) === LAMBDA || car(d) === CASE_LAMBDA);

/**
 * Every function definition in exprs, nested ones included, in the order the Scheme finds them:
 * a definition before those inside it. Handles (define (f . formals) body ...), (define f (lambda
 * ...)), (define f (case-lambda ...)), and letrec/letrec* bindings to either kind of lambda.
 */
export function extractDefinitions(exprs: readonly Datum[]): Definition[] {
  const defs: Definition[] = [];

  function processExpr(expr: Datum): void {
    // Quoted data, dotted or not, is never code (HC-2 round 11, I1).
    if (!isList(expr) || expr.length === 0 || expr[0] === QUOTE) return;
    const head = expr[0];
    const second = expr[1];
    const third = expr[2];
    if (head === DEFINE && second !== undefined && isPair(second) && isSym(car(second))) {
      const body = expr.slice(2);
      defs.push([car(second) as Sym, body]);
      body.forEach(processExpr);
    } else if (
      head === DEFINE && second !== undefined && isSym(second) && third !== undefined &&
      isPair(third) && car(third) === LAMBDA && isPair(cdr(third))
    ) {
      const body = properPrefix(cdr(cdr(third)));
      defs.push([second, body]);
      body.forEach(processExpr);
    } else if (head === DEFINE && second !== undefined && isSym(second) && third !== undefined && isPair(third) && car(third) === CASE_LAMBDA) {
      const body = caseLambdaBodies(cdr(third));
      defs.push([second, body]);
      body.forEach(processExpr);
    } else if ((head === LETREC || head === LETREC_STAR) && second !== undefined && isPair(second)) {
      for (const binding of properPrefix(second)) {
        if (!isPair(binding)) continue;
        const name = car(binding);
        const rest = cdr(binding);
        if (!isPair(rest)) continue;
        const init = car(rest);
        if (isSym(name) && isLambdaHead(init) && isPair(cdr(init))) {
          const body = car(init) === LAMBDA ? properPrefix(cdr(cdr(init))) : caseLambdaBodies(cdr(init));
          defs.push([name, body]);
          body.forEach(processExpr);
        }
        // Any other init may hold one, as cfa-rewrite-program wraps anonymous lambdas in letrec
        // wherever they sit.
        if (!isLambdaHead(init)) processExpr(init);
      }
      expr.slice(2).forEach(processExpr);
    } else {
      // Other compound expressions, operator included: ((letrec ((lp ...)) lp) 1).
      for (const sub of expr) if (isPair(sub)) processExpr(sub);
    }
  }

  exprs.forEach(processExpr);
  return defs;
}

/**
 * The names in targets that body calls, skipping quoted forms and collection HOFs. Only an
 * application's operator is a call; its arguments are searched for further applications. Each name
 * appears once, the last call found first, as the Scheme's consing leaves them.
 */
export function collectCallsInBody(body: readonly Datum[], targets: ReadonlySet<Sym>): Sym[] {
  const calls: Sym[] = [];
  function walk(expr: Datum): void {
    if (!isPair(expr)) return;
    const head = car(expr);
    if (head === QUOTE) return;
    if (isSym(head) && targets.has(head) && !isCollectionHof(head)) calls.push(head);
    if (isPair(head)) walk(head);
    properPrefix(cdr(expr)).forEach(walk);
  }
  body.forEach(walk);
  return [...new Set(calls.reverse())];
}

export function buildCallGraph(exprs: readonly Datum[]): CallGraph {
  const defs = extractDefinitions(exprs);
  const names = new Set(defs.map(([name]) => name));
  return defs.map(([name, body]) => [name, collectCallsInBody(body, names)] as const);
}

/** The names a definition calls, or none when the graph has no entry for it. */
export function callGraphEdges(graph: CallGraph, name: Sym): Sym[] {
  return graph.find(([n]) => n === name)?.[1] ?? [];
}

/**
 * Tarjan's strongly connected components. A component that is one node without a self-edge is
 * not recursive. The order is the Scheme's: the last component found comes first, and each
 * component lists its root first, then the nodes in the order they were pushed.
 */
export function tarjanScc<N>(graph: readonly (readonly [N, readonly N[]])[]): N[][] {
  let counter = 0;
  const stack: N[] = [];
  const index = new Map<N, number>();
  const lowlink = new Map<N, number>();
  const onStack = new Set<N>();
  const result: N[][] = [];

  function strongconnect(v: N): void {
    index.set(v, counter);
    lowlink.set(v, counter);
    counter += 1;
    stack.push(v);
    onStack.add(v);
    for (const w of graph.find(([n]) => n === v)?.[1] ?? []) {
      if (!index.has(w)) {
        strongconnect(w);
        lowlink.set(v, Math.min(lowlink.get(v)!, lowlink.get(w)!));
      } else if (onStack.has(w)) {
        lowlink.set(v, Math.min(lowlink.get(v)!, index.get(w)!));
      }
    }
    if (lowlink.get(v) === index.get(v)) {
      const component = stack.splice(stack.lastIndexOf(v));
      component.forEach((w) => onStack.delete(w));
      result.unshift(component);
    }
  }

  for (const [node] of graph) if (!index.has(node)) strongconnect(node);
  return result;
}
