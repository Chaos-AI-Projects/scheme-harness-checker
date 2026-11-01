// Binding identity of termination.ss (HC-17): alpha-rename-definitions, termination.ss:2925. The
// definition graph and the descent checks key on the bare symbol, so a local helper named like a
// top-level one would be judged by the top-level one's descent. This pass gives each such local
// definition its own name before any phase runs.
//
// A define, letrec or letrec* binder is renamed when more than one binder in the program uses its
// name, when it looks like a synthesized lambda@N node name, or when the analysis would misread it
// as a Chez builtin, keyword or 0CFA marker. Formals and let-style variables are renamed only in the
// last case. Top-level defines keep their names unless they look like lambda@N or are misread.
// Renaming is scope-correct: every reference moves with its binder, a rebinding stops it, and quoted
// data, case datums and quasiquoted templates outside unquote are left alone.
//
// The port is cons-cell faithful, because the differential test compares written output: an
// environment is an alist, newest first, so `bind` conses one entry per name in order, duplicates
// included, and the fresh-name counter advances exactly as Chez's does.

import { car, cdr, Dotted, isList, isPair, isSym, sym, Vec, type Datum, type Sym } from "../sexp.ts";
import { CFA_ELEMENT_MARKER, CFA_SPREAD_MARKER } from "./cfaprogram.ts";
import { isChezSchemeName } from "./chezenv.ts";
import { bindingNames, formalNames } from "./guards.ts";

/** An alist of (name . fresh), newest first, as alpha-rename-definitions returns it. */
export type RenameEnv = readonly (readonly [Sym, Sym])[];

const S = {
  quote: sym("quote"),
  quasiquote: sym("quasiquote"),
  unquote: sym("unquote"),
  unquoteSplicing: sym("unquote-splicing"),
  lambda: sym("lambda"),
  caseLambda: sym("case-lambda"),
  define: sym("define"),
  begin: sym("begin"),
  let: sym("let"),
  letStar: sym("let*"),
  letStarValues: sym("let*-values"),
  letValues: sym("let-values"),
  letrec: sym("letrec"),
  letrecStar: sym("letrec*"),
  do: sym("do"),
  case: sym("case"),
  guard: sym("guard"),
};

/** Scheme's cons over the array/Dotted representation. */
function cons(a: Datum, d: Datum): Datum {
  if (isList(d)) return [a, ...d];
  if (d instanceof Dotted) return new Dotted([a, ...d.items], d.tail);
  return new Dotted([a], d);
}

/** termination.ss:2955 node-name-like?: a synthesized lambda@N name. */
function nodeNameLike(name: Sym): boolean {
  return name.name.length >= 7 && name.name.startsWith("lambda@");
}

/** termination.ss:2963 misread-name?: a name the analysis reads by symbol as a builtin or marker. */
function misreadName(name: Datum): boolean {
  return isSym(name) && (name === CFA_ELEMENT_MARKER || name === CFA_SPREAD_MARKER || isChezSchemeName(name.name));
}

function assq(env: RenameEnv, name: Datum): readonly [Sym, Sym] | undefined {
  return env.find(([k]) => k === name);
}

/** termination.ss:3013 body-define-names. */
function bodyDefineNames(forms: readonly Datum[]): Sym[] {
  return forms.flatMap((f): Sym[] => {
    if (isPair(f) && car(f) === S.define && isPair(cdr(f))) {
      const t = car(cdr(f));
      if (isPair(t)) return isSym(car(t)) ? [car(t) as Sym] : [];
      return isSym(t) ? [t] : [];
    }
    if (isList(f) && f.length > 0 && f[0] === S.begin) return bodyDefineNames(f.slice(1));
    return [];
  });
}

/**
 * termination.ss:2925 alpha-rename-definitions. Returns the renamed program and the top-level
 * renames, an alist newest first that restore-top-level-names inverts.
 */
export function alphaRenameDefinitions(exprs: readonly Datum[]): { exprs: Datum[]; topEnv: RenameEnv } {
  const allSyms = new Set<Sym>();
  const binderCount = new Map<Sym, number>();
  let counter = 0;

  // The reader and the lowering build acyclic data, so unlike the Scheme no seen-table is needed.
  const noteSyms = (e: Datum): void => {
    if (isSym(e)) allSyms.add(e);
    else if (isList(e)) e.forEach(noteSyms);
    else if (e instanceof Dotted) {
      e.items.forEach(noteSyms);
      noteSyms(e.tail);
    } else if (e instanceof Vec) e.items.forEach(noteSyms);
  };

  const count = (name: Datum): void => {
    if (isSym(name)) binderCount.set(name, (binderCount.get(name) ?? 0) + 1);
  };

  // Over-counting only renames more, which is safe.
  const countBinders = (e: Datum): void => {
    if (!isList(e) || e.length === 0 || e[0] === S.quote) return;
    if (e[0] === S.define && e.length > 1) {
      const t = e[1]!;
      count(isPair(t) ? car(t) : t);
    } else if ((e[0] === S.letrec || e[0] === S.letrecStar) && e.length > 1 && isList(e[1]!)) {
      for (const b of e[1] as Datum[]) if (isPair(b)) count(car(b));
    }
    e.forEach(countBinders);
  };

  const rename = (name: Datum): boolean =>
    isSym(name) && ((binderCount.get(name) ?? 0) > 1 || nodeNameLike(name) || misreadName(name));

  const fresh = (name: Sym): Sym => {
    for (;;) {
      counter += 1;
      const cand = sym(`${name.name}~${counter}`);
      if (!allSyms.has(cand)) {
        allSyms.add(cand);
        return cand;
      }
    }
  };

  const unbind = (env: RenameEnv, names: readonly Datum[]): RenameEnv => env.filter(([k]) => !names.includes(k));

  // names are bound here; those that rename? accepts get fresh symbols.
  const bind = (env: RenameEnv, names: readonly Datum[]): RenameEnv =>
    names.reduce<RenameEnv>((acc, n) => (rename(n) ? [[n as Sym, fresh(n as Sym)], ...acc] : acc), unbind(env, names));

  // Formals, let, let-values, do and named-let variables: only a misread name gets a fresh symbol.
  const bindLocal = (env: RenameEnv, names: readonly Datum[]): RenameEnv =>
    names.reduce<RenameEnv>((acc, n) => (misreadName(n) ? [[n as Sym, fresh(n as Sym)], ...acc] : acc), unbind(env, names));

  const ref = (env: RenameEnv, e: Datum): Datum => assq(env, e)?.[1] ?? e;

  // Rewrite a binder: a symbol, a formals list or an improper one.
  const rnFormals = (fs: Datum, env: RenameEnv): Datum => {
    if (isSym(fs)) return ref(env, fs);
    if (isList(fs)) return fs.map((f) => rnFormals(f, env));
    if (fs instanceof Dotted) return new Dotted(fs.items.map((f) => rnFormals(f, env)), rnFormals(fs.tail, env));
    return fs;
  };

  // let-style bindings: each variable takes its name in inner.
  const rnBindingVars = (bs: Datum, inner: RenameEnv): Datum =>
    isList(bs) ? bs.map((b) => (isPair(b) ? cons(rnFormals(car(b), inner), cdr(b)) : b)) : bs;

  // A body: its defines bind across the whole body.
  const rnBody = (forms: Datum, env: RenameEnv): Datum[] | Datum => {
    if (!isList(forms)) return rn(forms, env);
    const inner = bind(env, bodyDefineNames(forms));
    return forms.map((f) => rnBodyForm(f, inner));
  };

  /** rn-body over the tail of a proper list, which is itself proper. */
  const rnBodyList = (forms: Datum[], env: RenameEnv): Datum[] => rnBody(forms, env) as Datum[];

  const rnBodyForm = (f: Datum, env: RenameEnv): Datum => {
    if (isList(f) && f.length > 1 && f[0] === S.define) {
      const t = f[1]!;
      if (isPair(t)) {
        const inner = bindLocal(env, formalNames(cdr(t)));
        return [S.define, cons(ref(env, car(t)), rnFormals(cdr(t), inner)), ...rnBodyList(f.slice(2), inner)];
      }
      return [S.define, ref(env, t), ...f.slice(2).map((x) => rn(x, env))];
    }
    if (isList(f) && f.length > 0 && f[0] === S.begin) return [S.begin, ...f.slice(1).map((x) => rnBodyForm(x, env))];
    return rn(f, env);
  };

  const rnBindings = (bs: Datum, env: RenameEnv): Datum =>
    isList(bs) ? bs.map((b) => (isList(b) && b.length > 0 ? [b[0]!, ...b.slice(1).map((x) => rn(x, env))] : b)) : bs;

  // termination.ss:3068 rn-qq recurses on the cdr, so a tail (unquote x), written (a . ,x), is an
  // unquote too. The suffix of x from index i is (head arg) exactly when x is proper and i is
  // second to last.
  const rnQq = (x: Datum, env: RenameEnv, depth: number): Datum => {
    if (!isPair(x)) return x;
    const items = isList(x) ? x : x.items;
    const tail: Datum = isList(x) ? [] : x.tail;
    const suffix = (i: number): Datum => {
      if (i === items.length) return rnQq(tail, env, depth);
      const head = items[i]!;
      if (isList(x) && items.length - i === 2) {
        const arg = items[i + 1]!;
        if (head === S.unquote || head === S.unquoteSplicing) {
          return [head, depth === 1 ? rn(arg, env) : rnQq(arg, env, depth - 1)];
        }
        if (head === S.quasiquote) return [S.quasiquote, rnQq(arg, env, depth + 1)];
      }
      return cons(rnQq(head, env, depth), suffix(i + 1));
    };
    return suffix(0);
  };

  const rnGeneric = (e: Datum, env: RenameEnv): Datum => {
    if (isList(e)) return e.map((x) => rn(x, env));
    if (e instanceof Dotted) return new Dotted(e.items.map((x) => rn(x, env)), rn(e.tail, env));
    return rn(e, env);
  };

  const rn = (e: Datum, env: RenameEnv): Datum => {
    if (isSym(e)) return ref(env, e);
    if (!isPair(e)) return e;
    if (!isList(e) || !isSym(e[0]!) || assq(env, e[0])) return rnGeneric(e, env);
    const head = e[0];
    const tail = e.slice(1);
    const t0 = tail[0];
    switch (head) {
      case S.quote:
        return e;
      case S.quasiquote:
        return tail.length === 1 ? [S.quasiquote, rnQq(t0!, env, 1)] : e;
      case S.lambda: {
        if (tail.length === 0) return e;
        const inner = bindLocal(env, formalNames(t0!));
        return [S.lambda, rnFormals(t0!, inner), ...rnBodyList(tail.slice(1), inner)];
      }
      case S.caseLambda:
        return [
          S.caseLambda,
          ...tail.map((c) => {
            if (!isPair(c)) return c;
            const inner = bindLocal(env, formalNames(car(c)));
            return cons(rnFormals(car(c), inner), rnBody(cdr(c), inner));
          }),
        ];
      case S.define:
        return rnBodyForm(e, env);
      case S.let: {
        if (tail.length >= 2 && isSym(t0!)) {
          const inner = bindLocal(env, [t0, ...bindingNames(tail[1]!)]);
          return [S.let, ref(inner, t0), rnBindingVars(rnBindings(tail[1]!, env), inner), ...rnBodyList(tail.slice(2), inner)];
        }
        if (tail.length === 0) return e;
        const inner = bindLocal(env, bindingNames(t0!));
        return [S.let, rnBindingVars(rnBindings(t0!, env), inner), ...rnBodyList(tail.slice(1), inner)];
      }
      case S.letStar:
      case S.letStarValues: {
        if (tail.length === 0 || !isList(t0!)) return e;
        let scope = env;
        const acc: Datum[] = [];
        for (const b of t0) {
          const inner = isPair(b) ? bindLocal(scope, formalNames(car(b))) : scope;
          acc.push((rnBindingVars(rnBindings([b], scope), inner) as Datum[])[0]!);
          scope = inner;
        }
        return [head, acc, ...rnBodyList(tail.slice(1), scope)];
      }
      case S.letValues: {
        if (tail.length === 0) return e;
        const inner = bindLocal(env, bindingNames(t0!));
        return [S.letValues, rnBindingVars(rnBindings(t0!, env), inner), ...rnBodyList(tail.slice(1), inner)];
      }
      case S.letrec:
      case S.letrecStar: {
        if (tail.length === 0) return e;
        const scope = bind(env, bindingNames(t0!));
        const bs = isList(t0!)
          ? t0.map((b) => (isList(b) && b.length > 0 ? [ref(scope, b[0]!), ...b.slice(1).map((x) => rn(x, scope))] : b))
          : t0!;
        return [head, bs, ...rnBodyList(tail.slice(1), scope)];
      }
      case S.do: {
        if (tail.length < 2 || !isList(t0!)) return e;
        const inner = bindLocal(env, bindingNames(t0));
        return [
          S.do,
          t0.map((b) =>
            isList(b) && b.length > 1 ? [ref(inner, b[0]!), rn(b[1]!, env), ...b.slice(2).map((x) => rn(x, inner))] : b,
          ),
          rn(tail[1]!, inner),
          ...tail.slice(2).map((x) => rn(x, inner)),
        ];
      }
      case S.case:
        if (tail.length === 0) return e;
        return [
          S.case,
          rn(t0!, env),
          ...tail.slice(1).map((c) => (isList(c) && c.length > 0 ? [c[0]!, ...c.slice(1).map((x) => rn(x, env))] : c)),
        ];
      case S.guard: {
        if (tail.length === 0 || !isList(t0!) || t0.length === 0) return e;
        const v = t0[0]!;
        const inner = bindLocal(env, [v]);
        return [S.guard, [ref(inner, v), ...t0.slice(1).map((c) => rn(c, inner))], ...rnBodyList(tail.slice(1), env)];
      }
      default:
        return rnGeneric(e, env);
    }
  };

  noteSyms([...exprs]);
  exprs.forEach(countBinders);
  // Top level: only names the analysis would misread are renamed.
  const topEnv = bodyDefineNames(exprs).reduce<RenameEnv>(
    (env, name) => ((nodeNameLike(name) || misreadName(name)) && !assq(env, name) ? [[name, fresh(name)], ...env] : env),
    [],
  );
  return { exprs: exprs.map((f) => rnBodyForm(f, topEnv)), topEnv };
}
