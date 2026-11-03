// 0CFA control-flow analysis, ported from src/harness-checker/cfa.ss (HC-2).
//
// Answers one question per call site: which lambdas can arrive in operator position there? The
// analysis is flow-insensitive and context-insensitive: every variable has one set of abstract
// values for the whole program, and the sets grow until nothing changes. The termination analysis
// uses the call-site table to see recursion that reaches a function through a variable, an
// immediate lambda, a data structure or a built-in HOF.
//
// Abstract values:
//   number        a lambda label (see CfaLambda)
//   "prim:<sym>"  a free name used as a value: a built-in or a tool
//   "cell:<id>"   an allocation site; its contents are one merged set
//   "top"         a value the analysis cannot follow
//
// Literals and the results of data built-ins are opaque data and have no representation: they are
// never procedures. A value reaches top only by passing through an operator the analysis does not
// model (a tool, a record constructor or accessor). Calling top marks the site unresolved, which
// the termination analysis reports as `unresolved-call`, so the checker stays fail-closed.
//
// Two departures from the Scheme, neither of which changes the fixpoint:
// - Chez evaluates `map` and `let` inits in an unspecified order, so the Scheme's label numbers for
//   lambdas inside one form follow Chez's order. This port goes left to right. Labels are assigned
//   during the syntactic walk only, so the sets differ by a renaming of labels at most.
// - The store is keyed by Scheme's equal?, so keys holding source forms use their written text.
//   Structurally equal allocation sites share one cell here exactly as they do there.

import {
  cadr,
  caddr,
  car,
  cdadr,
  cddr,
  cdddr,
  cdr,
  Dotted,
  elements,
  isList,
  isNull,
  isPair,
  isSym,
  sym,
  write,
  type Datum,
  type Sym,
} from "../sexp.ts";

export type Value = number | string;

export type LambdaKind = "define" | "letrec" | "named-let" | "lambda";

/** One per lambda, case-lambda clause, procedure define, letrec binding and named let. */
export interface CfaLambda {
  readonly label: number;
  readonly kind: LambdaKind;
  /** The bound symbol for define, letrec and named-let, else null. */
  readonly name: Sym | null;
  /** The required formals. */
  readonly formals: readonly Datum[];
  /** The rest formal, or null. */
  readonly rest: Datum | null;
  readonly body: Datum;
  /** Label of the lexically enclosing lambda, or null at top level. */
  readonly parent: number | null;
  /** The source form the label was created for. */
  readonly expr: Datum;
}

/**
 * How a callee was reached. A HOF entry names the built-in invoked positionally, or holds null when
 * it was reached through a spread argument list. "opaque" means the callee's arguments are unrelated
 * to the site's own.
 */
export type Via =
  | "direct"
  | "apply"
  | "escape"
  | "named-let"
  | "cond-arrow"
  | "opaque"
  | { readonly hof: string | null };

export interface Callee {
  readonly label: number;
  readonly via: Via;
}

/** One per application, named-let entry, cond `=>` clause and parameterize form. */
export interface CfaSite {
  readonly expr: Datum;
  /** Label of the enclosing lambda, or null at top level. */
  readonly caller: number | null;
  /** Newest first, as the Scheme list is. */
  callees: Callee[];
  /** True when top can reach operator position here. */
  unresolved: boolean;
}

export interface CfaResult {
  /** Sorted by label. */
  readonly lambdas: readonly CfaLambda[];
  /** In creation order. */
  readonly sites: readonly CfaSite[];
  readonly table: ReadonlyMap<Datum, CfaSite>;
}

export function cfaLambdaRef(result: CfaResult, label: number): CfaLambda | undefined {
  return result.lambdas.find((l) => l.label === label);
}

/** The site created for this source object; lookup is by identity, as the Scheme eq-hashtable is. */
export function cfaSiteOf(result: CfaResult, expr: Datum): CfaSite | undefined {
  return result.table.get(expr);
}

export function cfaSiteCalleeLabels(site: CfaSite): number[] {
  return [...new Set(site.callees.map((c) => c.label))].sort((a, b) => a - b);
}

// ---------------------------------------------------------------
// Built-in classification
// ---------------------------------------------------------------

// Callback position of each collection HOF, mirroring termination.ss.
const HOF_CALLBACK_POSITIONS = new Map<string, number>(
  [
    "map",
    "for-each",
    "filter",
    "remove",
    "remp",
    "fold-left",
    "fold-right",
    "find",
    "exists",
    "for-all",
    "memp",
    "partition",
    "vector-map",
    "vector-for-each",
    "string-for-each",
  ].map((n) => [n, 0]),
);

export function cfaHofCallbackPosition(name: Datum): number | null {
  return isSym(name) ? (HOF_CALLBACK_POSITIONS.get(name.name) ?? null) : null;
}

const words = (s: string): Set<string> => new Set(s.split(/\s+/).filter(Boolean));

// Built-ins that allocate one structure holding every argument.
const ALLOCATOR_NAMES = words("cons list vector make-vector cons*");

// Built-ins that return part of a structure argument. The result is the argument's cells plus their
// contents; returning the cell covers `cdr` yielding the rest of a list.
const READER_NAMES = words(`
  car cdr caar cadr cdar cddr caaar caadr cadar caddr cdaar cdadr cddar cdddr list-ref list-tail
  vector-ref member memv memq assoc assv assq reverse list-copy vector->list list->vector vector-copy`);

// Built-ins whose result is opaque data whatever they are given, and which never call an argument.
const DATA_BUILTIN_NAMES = words(`
  + - * / = < > <= >= zero? positive? negative? odd? even? abs max min modulo remainder quotient
  expt sqrt floor ceiling round truncate number? integer? real? exact? inexact? exact->inexact
  inexact->exact number->string string->number not boolean? pair? null? list? length symbol?
  symbol->string string->symbol char? char=? char<? char>? char<=? char>=? char-alphabetic?
  char-numeric? char-whitespace? char-upcase char-downcase char->integer integer->char string?
  string-length string-ref string=? string<? string>? string<=? string>=? substring string-append
  string->list list->string string-copy string-contains string-upcase string-downcase vector?
  vector-length display newline write format eq? eqv? equal? procedure? port? eof-object? void
  error assert`);

const CONTROL_NAMES = words("apply values call-with-values dynamic-wind vector-set! vector-fill! append");

export function cfaModeledBuiltin(name: Datum): boolean {
  if (!isSym(name)) return false;
  const n = name.name;
  return (
    ALLOCATOR_NAMES.has(n) ||
    READER_NAMES.has(n) ||
    DATA_BUILTIN_NAMES.has(n) ||
    CONTROL_NAMES.has(n) ||
    HOF_CALLBACK_POSITIONS.has(n)
  );
}

const SPECIAL_FORMS = words(`
  quote quasiquote lambda case-lambda define set! if when unless begin and or cond case let let*
  letrec letrec* let-values let*-values do define-record-type parameterize guard`);

const S = {
  apply: sym("apply"),
  begin: sym("begin"),
  caseLambda: sym("case-lambda"),
  cond: sym("cond"),
  define: sym("define"),
  else: sym("else"),
  lambda: sym("lambda"),
  letStarValues: sym("let*-values"),
  quasiquote: sym("quasiquote"),
  r: sym("r"),
  unquote: sym("unquote"),
  unquoteSplicing: sym("unquote-splicing"),
  arrow: sym("=>"),
};

// ---------------------------------------------------------------
// Sets of abstract values: small arrays in Scheme's set-union order
// ---------------------------------------------------------------

// Scheme folds b into a, consing each new value onto the front.
function setUnion(a: readonly Value[], b: readonly Value[]): Value[] {
  const added: Value[] = [];
  for (const v of b) if (!a.includes(v) && !added.includes(v)) added.push(v);
  return [...added.reverse(), ...a];
}

function setUnionAll(sets: readonly (readonly Value[])[]): Value[] {
  return sets.reduce<Value[]>((acc, s) => setUnion(acc, s), []);
}

const isCell = (v: Value): v is `cell:${string}` => typeof v === "string" && v.startsWith("cell:");
const isPrim = (v: Value): v is `prim:${string}` => typeof v === "string" && v.startsWith("prim:");
const isLabel = (v: Value): v is number => typeof v === "number";

// Split formals into required and rest.
function parseFormals(f: Datum): { req: Datum[]; rest: Datum | null } {
  if (isList(f)) return { req: [...f], rest: null };
  if (f instanceof Dotted) return { req: [...f.items], rest: isSym(f.tail) ? f.tail : null };
  return { req: [], rest: isSym(f) ? f : null };
}

// Environments: an association list of symbol to store key, newest first.
interface Env {
  readonly name: Datum;
  readonly key: string;
  readonly next: Env | null;
}

function assq(env: Env | null, name: Datum): Env | null {
  for (let e = env; e; e = e.next) if (e.name === name) return e;
  return null;
}

const bind = (env: Env | null, name: Datum, key: string): Env => ({ name, key, next: env });

// ---------------------------------------------------------------
// The analysis
// ---------------------------------------------------------------

const SPREAD_DEPTH_LIMIT = 8;

/**
 * calls "js" models a JavaScript call: a formal the call does not reach is bound to undefined, which
 * is never a procedure, and an argument past the last formal is evaluated and ignored. "scheme", the
 * default, treats a call whose arity cannot match as impossible, since Chez raises on it (HC-37).
 */
export interface CfaOptions {
  readonly calls?: "scheme" | "js";
}

export function cfaAnalyze(exprs: readonly Datum[], options: CfaOptions = {}): CfaResult {
  const jsCalls = options.calls === "js";
  const store = new Map<string, Value[]>();
  const lambdaTable = new Map<Datum, CfaLambda>();
  const lambdas: CfaLambda[] = [];
  const bindingIds = new Map<Datum, string>();
  const siteTable = new Map<Datum, CfaSite>();
  const sites: CfaSite[] = [];
  const written = new WeakMap<object, string>();
  let changed = false;
  let spreadDepth = 0;

  // Written text of a source form, memoized: the stand-in for equal? on store keys.
  function text(d: Datum): string {
    if (typeof d !== "object") return write(d);
    let t = written.get(d);
    if (t === undefined) {
      t = write(d);
      written.set(d, t);
    }
    return t;
  }

  // --- store ---
  const storeRef = (key: string): Value[] => store.get(key) ?? [];
  function storeAdd(key: string, vals: readonly Value[]): void {
    const old = storeRef(key);
    const next = setUnion(old, vals);
    if (next.length !== old.length) {
      store.set(key, next);
      changed = true;
    }
  }

  const contentsKey = (cell: string): string => `contents:${cell.slice("cell:".length)}`;
  const retKey = (label: number): string => `ret:${label}`;
  const formalKey = (label: number, i: number): string => `f:${label}:${i}`;
  const restKey = (label: number): string => `r:${label}`;
  // The rest list's cell is named by the Scheme rest key, (r label).
  const restCell = (label: number): string => `cell:${write([S.r, label])}`;

  // Contents of every cell in a set; top reads as top.
  function contents(vals: readonly Value[]): Value[] {
    return setUnionAll(vals.map((v) => (isCell(v) ? storeRef(contentsKey(v)) : v === "top" ? ["top"] : [])));
  }

  // --- identities ---
  function bindingKey(obj: Datum): string {
    let k = bindingIds.get(obj);
    if (k === undefined) {
      k = `v:${bindingIds.size}`;
      bindingIds.set(obj, k);
    }
    return k;
  }

  function getLambda(source: Datum, kind: LambdaKind, name: Sym | null, formals: Datum, body: Datum, parent: number | null): CfaLambda {
    let l = lambdaTable.get(source);
    if (!l) {
      const { req, rest } = parseFormals(formals);
      l = { label: lambdas.length, kind, name, formals: req, rest, body, parent, expr: source };
      lambdaTable.set(source, l);
      lambdas.push(l);
    }
    return l;
  }

  function getSite(expr: Datum, caller: number | null): CfaSite {
    let s = siteTable.get(expr);
    if (!s) {
      s = { expr, caller, callees: [], unresolved: false };
      siteTable.set(expr, s);
      sites.push(s);
    }
    return s;
  }

  const sameVia = (a: Via, b: Via): boolean =>
    a === b || (typeof a === "object" && typeof b === "object" && a.hof === b.hof);

  function siteAddCallee(site: CfaSite, label: number, via: Via): void {
    if (!site.callees.some((c) => c.label === label && sameVia(c.via, via))) {
      site.callees.unshift({ label, via });
      changed = true;
    }
  }

  function siteMarkUnresolved(site: CfaSite): void {
    if (!site.unresolved) {
      site.unresolved = true;
      changed = true;
    }
  }

  const siteCell = (site: CfaSite): string => `cell:${text(site.expr)}`;

  function lookup(env: Env | null, name: Sym): Value[] {
    const e = assq(env, name);
    return e ? storeRef(e.key) : [`prim:${name.name}`];
  }

  // --- lambdas ---

  // Analyse a lambda's body and return its label. Called every pass; the label is stable because it
  // is keyed on the source form.
  function evalLambdaLike(
    source: Datum,
    kind: LambdaKind,
    name: Sym | null,
    formals: Datum,
    body: Datum,
    env: Env | null,
    parent: number | null,
  ): number {
    const l = getLambda(source, kind, name, formals, body, parent);
    storeAdd(retKey(l.label), evalBody(body, bindFormals(l, env), l.label));
    return l.label;
  }

  function bindFormals(l: CfaLambda, env: Env | null): Env | null {
    l.formals.forEach((f, i) => {
      env = bind(env, f, formalKey(l.label, i));
    });
    if (l.rest !== null) {
      storeAdd(restKey(l.label), [restCell(l.label)]);
      env = bind(env, l.rest, restKey(l.label));
    }
    return env;
  }

  // Flow arguments into a lambda. `spread` (or null) flows to every formal and into the rest list,
  // for apply and HOF callbacks. Returns null when the arity cannot match, else the lambda's result.
  // A JavaScript call always matches: a missing argument flows nothing and an extra one is dropped.
  function flowInto(label: number, args: readonly Value[][], spread: readonly Value[] | null): Value[] | null {
    const l = lambdas[label]!;
    const n = args.length;
    if (!jsCalls && spread === null && (n < l.formals.length || (l.rest === null && n > l.formals.length))) return null;
    for (let i = 0; i < l.formals.length; i++) {
      storeAdd(formalKey(label, i), setUnion(args[i] ?? [], spread ?? []));
    }
    if (l.rest !== null) {
      const cell = restCell(label);
      storeAdd(restKey(label), [cell]);
      storeAdd(contentsKey(cell), setUnion(setUnionAll(args.slice(l.formals.length)), spread ?? []));
    }
    return storeRef(retKey(label));
  }

  // Invoke every value in opSet. Returns the union of results.
  function invoke(opSet: readonly Value[], args: Value[][], spread: Value[] | null, site: CfaSite, via: Via): Value[] {
    return setUnionAll(
      opSet.map((v) => {
        if (isLabel(v)) {
          const r = flowInto(v, args, spread);
          if (!r) return [];
          siteAddCallee(site, v, via);
          return r;
        }
        if (isPrim(v)) return applyBuiltin(v.slice("prim:".length), args, spread, site);
        if (v === "top") {
          siteMarkUnresolved(site);
          escape(setUnion(setUnionAll(args), spread ?? []), site);
          return ["top"];
        }
        return [];
      }),
    );
  }

  // Values handed to an operator the analysis does not model. Every lambda reachable from them may
  // be called with unknown arguments, and every reachable cell may be overwritten with unknown
  // values.
  function escape(vals: readonly Value[], site: CfaSite): void {
    let todo = [...vals];
    const seen: Value[] = [];
    while (todo.length > 0) {
      const v = todo.shift()!;
      if (seen.includes(v)) continue;
      seen.push(v);
      if (isLabel(v)) {
        flowInto(v, [], ["top"]);
        siteAddCallee(site, v, "escape");
      } else if (isCell(v)) {
        storeAdd(contentsKey(v), ["top"]);
        todo = [...storeRef(contentsKey(v)), ...todo];
      }
    }
  }

  // --- built-ins ---

  // Positional slots a built-in reads, or 0 when it reads only the union of its arguments.
  function builtinArity(name: string): number {
    if (name === "vector-set!" || name === "dynamic-wind") return 3;
    if (name === "vector-fill!" || name === "apply" || name === "call-with-values") return 2;
    const pos = HOF_CALLBACK_POSITIONS.get(name);
    return pos === undefined ? 0 : pos + 2;
  }

  // A built-in reached through apply, a HOF callback or call-with-values gets its arguments as a
  // spread list, so any spread value may sit in any positional slot. Each slot therefore holds the
  // spread values as well. Spread built-ins can invoke one another without end, as in
  // (apply apply (list apply apply)), so past a fixed depth the site fails closed as unresolved.
  function applyBuiltin(name: string, args: Value[][], spread: Value[] | null, site: CfaSite): Value[] {
    const k = builtinArity(name);
    if (spread === null || spread.length === 0 || k === 0) return applyPositionalBuiltin(name, args, spread, site);
    if (spreadDepth >= SPREAD_DEPTH_LIMIT) {
      siteMarkUnresolved(site);
      escape(setUnion(setUnionAll(args), spread), site);
      return ["top"];
    }
    spreadDepth++;
    try {
      return applyPositionalBuiltin(name, widenArgs(args, spread, k), spread, site);
    } finally {
      spreadDepth--;
    }
  }

  function widenArgs(args: readonly Value[][], spread: readonly Value[], k: number): Value[][] {
    const out: Value[][] = [];
    for (let i = 0; i < Math.max(args.length, k); i++) out.push(setUnion(args[i] ?? [], spread));
    return out;
  }

  function applyPositionalBuiltin(name: string, args: Value[][], spread: Value[] | null, site: CfaSite): Value[] {
    const all = setUnion(setUnionAll(args), spread ?? []);
    if (ALLOCATOR_NAMES.has(name)) {
      const cell = siteCell(site);
      storeAdd(contentsKey(cell), all);
      return [cell];
    }
    if (READER_NAMES.has(name)) {
      return setUnion(
        all.filter((v) => isCell(v) || v === "top"),
        contents(all),
      );
    }
    // Any argument, spread ones included, can end up as the result's tail, which may be improper.
    // The result gets its own cell holding every argument and every element, so a reader on it
    // yields all of them.
    if (name === "append") {
      const cell = siteCell(site);
      storeAdd(contentsKey(cell), setUnion(all, contents(all)));
      return setUnion([cell], all);
    }
    if (DATA_BUILTIN_NAMES.has(name)) return [];
    if (name === "values") return all;
    if (name === "vector-set!" || name === "vector-fill!") {
      const valueSlot = name === "vector-set!" ? 2 : 1;
      if (args.length === valueSlot + 1) {
        for (const c of args[0]!) if (isCell(c)) storeAdd(contentsKey(c), args[valueSlot]!);
      }
      return [];
    }
    if (name === "apply") {
      if (args.length === 0) return [];
      const more = args.slice(1);
      const leading = more.slice(0, Math.max(more.length - 1, 0));
      const lst = more.length > 0 ? more[more.length - 1]! : [];
      const sp = setUnion(contents(lst), spread ?? []);
      // The site's own arguments are apply's only when the site is a positional call headed by
      // apply. An empty spread set is still a spread (HC-2 round 11, C1).
      const positional = spread === null && isPair(site.expr) && car(site.expr) === S.apply;
      return invoke(args[0]!, leading, sp, site, positional ? "apply" : "opaque");
    }
    if (name === "call-with-values") {
      if (args.length !== 2) return [];
      // The consumer receives the producer's values, never the site's own arguments.
      const r = invoke(args[0]!, [], null, site, "opaque");
      return invoke(args[1]!, [], r, site, "opaque");
    }
    if (name === "dynamic-wind") {
      if (args.length !== 3) return [];
      invoke(args[0]!, [], null, site, "opaque");
      invoke(args[2]!, [], null, site, "opaque");
      return invoke(args[1]!, [], null, site, "opaque");
    }
    const pos = HOF_CALLBACK_POSITIONS.get(name);
    if (pos !== undefined) {
      if (args.length <= pos) return [];
      const others = setUnionAll(args.filter((_, i) => i !== pos));
      const elems = setUnion(others, contents(others));
      const accKey = `hof-acc:${text(site.expr)}`;
      const sp = setUnionAll([elems, storeRef(accKey), spread ?? []]);
      // The callback's slots match the site's own arguments only when this HOF is invoked
      // positionally; under a spread it is null.
      const positional = spread === null || spread.length === 0;
      const r = invoke(args[pos]!, [], sp, site, { hof: positional ? name : null });
      storeAdd(accKey, r);
      if (name === "map" || name === "vector-map") {
        const cell = siteCell(site);
        storeAdd(contentsKey(cell), r);
        return [cell];
      }
      return setUnion(r, elems);
    }
    // Unmodeled operator: a tool, a record constructor or accessor. Anything handed to it escapes;
    // it returns top if it was handed anything that is not opaque data.
    if (all.length === 0) return [];
    escape(all, site);
    return ["top"];
  }

  // --- bodies and internal defines ---
  function flattenBegins(exprs: readonly Datum[]): Datum[] {
    return exprs.flatMap((e) => (isPair(e) && car(e) === S.begin ? flattenBegins(elements(cdr(e))) : [e]));
  }

  function defineName(e: Datum): Sym | null {
    if (!isPair(e) || car(e) !== S.define || !isPair(cdr(e))) return null;
    const head = cadr(e);
    if (isSym(head)) return head;
    if (isPair(head) && isSym(car(head))) return car(head) as Sym;
    return null;
  }

  function evalBody(body: Datum, env: Env | null, ctx: number | null): Value[] {
    const flat = flattenBegins(elements(body));
    let env2 = env;
    for (const e of flat) {
      const n = defineName(e);
      if (n) env2 = bind(env2, n, bindingKey(e));
    }
    let last: Value[] = [];
    for (const e of flat) last = evalExpr(e, env2, ctx);
    return last;
  }

  const lambdaForm = (e: Datum, kw: Sym): boolean => isPair(e) && car(e) === kw && isPair(cdr(e));

  // Evaluate a binding's right-hand side, naming it when it is a lambda or case-lambda.
  function evalNamedRhs(rhs: Datum, kind: LambdaKind, name: Sym | null, env: Env | null, ctx: number | null): Value[] {
    if (lambdaForm(rhs, S.lambda)) return [evalLambdaLike(rhs, kind, name, cadr(rhs), cddr(rhs), env, ctx)];
    if (lambdaForm(rhs, S.caseLambda)) return evalCaseLambda(rhs, kind, name, env, ctx);
    return evalExpr(rhs, env, ctx);
  }

  function evalCaseLambda(e: Datum, kind: LambdaKind, name: Sym | null, env: Env | null, ctx: number | null): Value[] {
    return elements(cdr(e))
      .filter(isPair)
      .map((clause) => evalLambdaLike(clause, kind, name, car(clause), cdr(clause), env, ctx));
  }

  // --- expressions ---
  function evalExpr(e: Datum, env: Env | null, ctx: number | null): Value[] {
    if (isSym(e)) return lookup(env, e);
    if (!isPair(e)) return [];
    const head = car(e);
    if (isSym(head) && SPECIAL_FORMS.has(head.name) && !assq(env, head)) return evalSpecial(e, head.name, env, ctx);
    return evalApplication(e, env, ctx);
  }

  const evalAll = (es: Datum, env: Env | null, ctx: number | null): Value[][] =>
    elements(es).map((x) => evalExpr(x, env, ctx));

  function evalApplication(e: Datum, env: Env | null, ctx: number | null): Value[] {
    const site = getSite(e, ctx);
    const op = evalExpr(car(e), env, ctx);
    const args = isList(cdr(e)) ? evalAll(cdr(e), env, ctx) : [];
    return invoke(op, args, null, site, "direct");
  }

  function evalQuasi(q: Datum, env: Env | null, ctx: number | null, depth: number, cell: string): void {
    if (!isPair(q)) return;
    const head = car(q);
    if ((head === S.unquote || head === S.unquoteSplicing) && isPair(cdr(q))) {
      if (depth > 0) return evalQuasi(cadr(q), env, ctx, depth - 1, cell);
      const v = evalExpr(cadr(q), env, ctx);
      storeAdd(contentsKey(cell), head === S.unquote ? v : setUnion(v, contents(v)));
    } else if (head === S.quasiquote) {
      evalQuasi(cdr(q), env, ctx, depth + 1, cell);
    } else {
      evalQuasi(head, env, ctx, depth, cell);
      evalQuasi(cdr(q), env, ctx, depth, cell);
    }
  }

  function evalSpecial(e: Datum, form: string, env: Env | null, ctx: number | null): Value[] {
    switch (form) {
      case "quote":
      case "define-record-type":
        return [];
      case "quasiquote": {
        const cell = `cell:${text(e)}`;
        if (isPair(cdr(e))) evalQuasi(cadr(e), env, ctx, 0, cell);
        return [cell];
      }
      case "lambda":
        return [evalLambdaLike(e, "lambda", null, cadr(e), cddr(e), env, ctx)];
      case "case-lambda":
        return evalCaseLambda(e, "lambda", null, env, ctx);
      case "define": {
        const n = defineName(e);
        if (n && isPair(cadr(e))) {
          const label = evalLambdaLike(e, "define", n, cdadr(e), cddr(e), env, ctx);
          storeAdd(bindingKey(e), [label]);
        } else if (n && isPair(cddr(e))) {
          storeAdd(bindingKey(e), evalNamedRhs(caddr(e), "define", n, env, ctx));
        }
        return [];
      }
      case "set!": {
        if (isPair(cdr(e)) && isPair(cddr(e))) {
          const v = evalExpr(caddr(e), env, ctx);
          const b = assq(env, cadr(e));
          if (b) storeAdd(b.key, v);
        }
        return [];
      }
      case "if":
      case "when":
      case "unless":
      case "begin":
      case "and":
      case "or": {
        const vs = evalAll(cdr(e), env, ctx);
        if (form === "if") return setUnionAll(vs.slice(1));
        if (form === "and" || form === "or") return setUnionAll(vs);
        return vs.length > 0 ? vs[vs.length - 1]! : [];
      }
      case "cond":
        return evalCond(e, env, ctx);
      case "case": {
        if (!isPair(cdr(e))) return [];
        evalExpr(cadr(e), env, ctx);
        return setUnionAll(
          elements(cddr(e)).map((clause) => (isPair(clause) && isPair(cdr(clause)) ? evalBody(cdr(clause), env, ctx) : [])),
        );
      }
      case "let":
        return evalLet(e, env, ctx);
      case "let*":
        return evalLetStar(e, env, ctx);
      case "letrec":
      case "letrec*":
        return evalLetrec(e, env, ctx);
      case "let-values":
      case "let*-values":
        return evalLetValues(e, env, ctx);
      case "do":
        return evalDo(e, env, ctx);
      case "parameterize":
        return evalParameterize(e, env, ctx);
      case "guard":
        return evalGuard(e, env, ctx);
      default:
        return [];
    }
  }

  // (guard (var clause ...) body ...): var holds whatever was raised, which can be any value, so it
  // starts as top and a call through it is unresolved (HC-2 round 14, I1).
  function evalGuard(e: Datum, env: Env | null, ctx: number | null): Value[] {
    if (!(isPair(cdr(e)) && isPair(cadr(e)) && isSym(car(cadr(e))) && isList(cdr(cadr(e))))) return [];
    const spec = cadr(e);
    const k = bindingKey(spec);
    const bodyV = evalBody(cddr(e), env, ctx);
    storeAdd(k, ["top"]);
    return setUnion(bodyV, evalCond([S.cond, ...elements(cdr(spec))], bind(env, car(spec), k), ctx));
  }

  // (parameterize ((p v) ...) body ...): Chez calls each p as (p) to read the old value and as
  // (p x) to install v, then the old value again on exit (HC-2 round 10, I2).
  function evalParameterize(e: Datum, env: Env | null, ctx: number | null): Value[] {
    if (!(isPair(cdr(e)) && isList(cadr(e)))) return [];
    const site = getSite(e, ctx);
    for (const b of elements(cadr(e))) {
      if (isList(b) && b.length === 2) {
        const p = evalExpr(b[0]!, env, ctx);
        const v = evalExpr(b[1]!, env, ctx);
        const old = invoke(p, [], null, site, "opaque");
        invoke(p, [setUnion(v, old)], null, site, "opaque");
      }
    }
    return evalBody(cddr(e), env, ctx);
  }

  function evalCond(e: Datum, env: Env | null, ctx: number | null): Value[] {
    return setUnionAll(
      elements(cdr(e)).map((clause) => {
        if (!isPair(clause)) return [];
        if (isPair(cdr(clause)) && cadr(clause) === S.arrow && isPair(cddr(clause))) {
          const t = evalExpr(car(clause), env, ctx);
          const f = evalExpr(caddr(clause), env, ctx);
          return invoke(f, [t], null, getSite(clause, ctx), "cond-arrow");
        }
        const t = car(clause) === S.else ? [] : evalExpr(car(clause), env, ctx);
        return isNull(cdr(clause)) ? t : evalBody(cdr(clause), env, ctx);
      }),
    );
  }

  const bindingPairs = (bs: Datum): Datum[] => elements(bs).filter((b) => isPair(b) && isSym(car(b)));

  function evalLet(e: Datum, env: Env | null, ctx: number | null): Value[] {
    if (isPair(cdr(e)) && isSym(cadr(e)) && isPair(cddr(e))) {
      // named let
      const name = cadr(e) as Sym;
      const bs = bindingPairs(caddr(e));
      const inits = bs.map((b) => evalExpr(isPair(cdr(b)) ? cadr(b) : false, env, ctx));
      const envLoop = bind(env, name, bindingKey(e));
      const label = evalLambdaLike(e, "named-let", name, bs.map(car), cdddr(e), envLoop, ctx);
      const site = getSite(e, ctx);
      storeAdd(bindingKey(e), [label]);
      return invoke([label], inits, null, site, "named-let");
    }
    if (!isPair(cdr(e))) return [];
    let env2 = env;
    for (const b of bindingPairs(cadr(e))) {
      if (isPair(cdr(b))) storeAdd(bindingKey(b), evalExpr(cadr(b), env, ctx));
      env2 = bind(env2, car(b), bindingKey(b));
    }
    return evalBody(cddr(e), env2, ctx);
  }

  function evalLetStar(e: Datum, env: Env | null, ctx: number | null): Value[] {
    if (!isPair(cdr(e))) return [];
    let env2 = env;
    for (const b of bindingPairs(cadr(e))) {
      if (isPair(cdr(b))) storeAdd(bindingKey(b), evalExpr(cadr(b), env2, ctx));
      env2 = bind(env2, car(b), bindingKey(b));
    }
    return evalBody(cddr(e), env2, ctx);
  }

  function evalLetrec(e: Datum, env: Env | null, ctx: number | null): Value[] {
    if (!isPair(cdr(e))) return [];
    const bs = bindingPairs(cadr(e));
    let env2 = env;
    for (const b of bs) env2 = bind(env2, car(b), bindingKey(b));
    for (const b of bs) {
      if (isPair(cdr(b))) storeAdd(bindingKey(b), evalNamedRhs(cadr(b), "letrec", car(b) as Sym, env2, ctx));
    }
    return evalBody(cddr(e), env2, ctx);
  }

  // Multiple values are merged: `values` returns the union of its arguments, so every variable a
  // binding introduces gets the whole init set.
  function evalLetValues(e: Datum, env: Env | null, ctx: number | null): Value[] {
    if (!isPair(cdr(e))) return [];
    const sequential = car(e) === S.letStarValues;
    let env2 = env;
    for (const b of elements(cadr(e))) {
      if (!(isPair(b) && isPair(cdr(b)))) continue;
      const v = evalExpr(cadr(b), sequential ? env2 : env, ctx);
      const { req, rest } = parseFormals(car(b));
      for (const name of rest !== null ? [rest, ...req] : req) {
        const k = `lv:${write([b, name])}`;
        storeAdd(k, v);
        env2 = bind(env2, name, k);
      }
    }
    return evalBody(cddr(e), env2, ctx);
  }

  function evalDo(e: Datum, env: Env | null, ctx: number | null): Value[] {
    if (!(isPair(cdr(e)) && isPair(cddr(e)))) return [];
    const specs = bindingPairs(cadr(e));
    let env2 = env;
    for (const s of specs) env2 = bind(env2, car(s), bindingKey(s));
    for (const s of specs) {
      if (isPair(cdr(s))) {
        storeAdd(bindingKey(s), evalExpr(cadr(s), env, ctx));
        if (isPair(cddr(s))) storeAdd(bindingKey(s), evalExpr(caddr(s), env2, ctx));
      }
    }
    const testClause = caddr(e);
    evalBody(cdddr(e), env2, ctx);
    if (!isPair(testClause)) return [];
    evalExpr(car(testClause), env2, ctx);
    return evalBody(cdr(testClause), env2, ctx);
  }

  // --- fixpoint ---
  do {
    changed = false;
    evalBody([...exprs], null, null);
  } while (changed);

  return { lambdas: [...lambdas], sites: [...sites], table: siteTable };
}
