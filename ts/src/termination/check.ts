// The termination pass's entry point, termination.ss:3259 check-termination (HC-17). It rejects a
// cyclic datum outright, gives every binder its own name (alpharename.ts), runs Phases 2b to 7 on the
// renamed program, and reports each violation under the name the program wrote.
//
// The TypeScript checker has no type passes, so this is check-termination with an empty type-env, as
// test-termination.ss and the --no-types differential run it.

import { car, cdr, Dotted, isList, isPair, isSym, sym, Vec, type Datum, type Sym } from "../sexp.ts";
import { alphaRenameDefinitions, type RenameEnv } from "./alpharename.ts";
import { buildCallGraph, callGraphEdges, extractDefinitions, tarjanScc } from "./callgraph.ts";
import { cfaAnalyzeProgram } from "./cfaprogram.ts";
import { analyzeDirectRecursion } from "./directrec.ts";
import { analyzeDoForms } from "./do.ts";
import { flattenBegins } from "./guards.ts";
import { checkHofCallbacks, detectUserDefinedHofs } from "./hof.ts";
import { analyzeMutualRecursion } from "./mutualrec.ts";
import { analyzeNamedLetForms } from "./namedlet.ts";
import type { TerminationViolation } from "./violation.ts";

const DEFINE = sym("define");

/**
 * termination.ss:3259 check-termination. maxDefinitions, when set, blocks a program with more
 * definitions than that; null means no limit.
 */
export function checkTermination(exprs: readonly Datum[], maxDefinitions: number | null = null): TerminationViolation[] {
  if (cyclicDatum(exprs as Datum[])) {
    return [
      {
        kind: "cyclic-datum",
        function: null,
        expr: false,
        reason: "source contains a cyclic datum (#n= label); descent on car, cdr and vector-ref assumes acyclic data",
      },
    ];
  }
  const { exprs: renamed, topEnv } = alphaRenameDefinitions(exprs);
  return [
    ...duplicateTopLevelDefinitions(exprs),
    ...checkTerminationRenamed(renamed, maxDefinitions).map((v) => restoreTopLevelNames(v, topEnv)),
  ];
}

/**
 * termination.ss:3279 cyclic-datum?. Every descent rule assumes acyclic data, so a cycle built with
 * a #n= label is rejected before analysis. Shared but acyclic structure is accepted.
 */
export function cyclicDatum(x: Datum): boolean {
  const onPath = new Set<object>();
  const done = new Set<object>();
  const walk = (x: Datum): boolean => {
    if (!isList(x) && !(x instanceof Dotted) && !(x instanceof Vec)) return false;
    if (done.has(x)) return false;
    if (onPath.has(x)) return true;
    onPath.add(x);
    const children = isList(x) ? x : x instanceof Dotted ? [...x.items, x.tail] : x.items;
    const found = children.some(walk);
    onPath.delete(x);
    done.add(x);
    return found;
  };
  return walk(x);
}

/**
 * termination.ss:3305 duplicate-top-level-definitions: a second top-level define of a name rebinds
 * the same variable, while the definition graph judges only one of them. One violation per name.
 */
export function duplicateTopLevelDefinitions(exprs: readonly Datum[]): TerminationViolation[] {
  const names = flattenBegins(exprs)
    .filter((e) => isPair(e) && car(e) === DEFINE && isPair(cdr(e)))
    .map((e) => {
      const t = car(cdr(e));
      return isPair(t) ? car(t) : t;
    })
    .filter(isSym);
  const seen = new Set<Sym>();
  const acc: TerminationViolation[] = [];
  for (const name of names) {
    if (seen.has(name)) {
      if (!acc.some((v) => v.function === name)) {
        acc.push({
          kind: "duplicate-definition",
          function: name,
          expr: false,
          reason: `"${name.name}" is defined more than once at top level`,
        });
      }
    } else seen.add(name);
  }
  return acc;
}

/**
 * termination.ss:3212 restore-top-level-names: a renamed top-level definition is reported under its
 * own name. In the reason text a fresh name matches only when no digit follows, so car~1 leaves
 * car~12 alone.
 */
export function restoreTopLevelNames(v: TerminationViolation, topEnv: RenameEnv): TerminationViolation {
  if (topEnv.length === 0) return v;
  const oldName = (s: Sym): Sym => topEnv.find(([, fresh]) => fresh === s)?.[0] ?? s;
  const restoreExpr = (e: Datum): Datum => {
    if (isSym(e)) return oldName(e);
    if (isList(e)) return e.map(restoreExpr);
    if (e instanceof Dotted) return new Dotted(e.items.map(restoreExpr), restoreExpr(e.tail));
    return e;
  };
  const replaceName = (str: string, from: string, to: string): string => {
    let out = "";
    let i = 0;
    while (i + from.length <= str.length) {
      if (str.startsWith(from, i) && !/^\p{Nd}/u.test(str.slice(i + from.length))) {
        out += to;
        i += from.length;
      } else out += str[i++];
    }
    return out + str.slice(i);
  };
  return {
    kind: v.kind,
    function: v.function === null ? null : oldName(v.function),
    expr: restoreExpr(v.expr),
    reason: topEnv.reduce((r, [old, fresh]) => replaceName(r, fresh.name, old.name), v.reason),
  };
}

/** termination.ss:3332 check-termination-renamed: Phases 2b to 7 on the renamed program. */
function checkTerminationRenamed(exprs: readonly Datum[], maxDefinitions: number | null): TerminationViolation[] {
  const doViolations = analyzeDoForms(exprs);
  const namedLetViolations = analyzeNamedLetForms(exprs);
  const defs = extractDefinitions(exprs);
  if (maxDefinitions !== null && defs.length > maxDefinitions) {
    return [
      ...doViolations,
      ...namedLetViolations,
      {
        kind: "definition-limit-exceeded",
        function: null,
        expr: false,
        reason: `definition count ${defs.length} exceeds analysis limit ${maxDefinitions}`,
      },
    ];
  }
  const definedNames = defs.map(([name]) => name);
  // Phases 5 and 6 run on the program with 0CFA's higher-order call edges made explicit.
  const cfa = cfaAnalyzeProgram(exprs);
  const graph = buildCallGraph(cfa.rewritten);
  const baseViolations = [
    ...analyzeDirectRecursion(cfa.rewritten),
    ...analyzeMutualRecursion(cfa.rewritten),
    ...cfa.violations,
  ];
  const violatedNames = baseViolations.map((v) => v.function);
  // A function is proven terminating only when the checker positively confirms it: a single-node
  // SCC with no self-edge, or a recursive one the phases above passed. This fails closed.
  const triviallyNonRecursive = tarjanScc(graph)
    .filter((scc) => scc.length === 1 && !callGraphEdges(graph, scc[0]!).includes(scc[0]!))
    .map((scc) => scc[0]!);
  const provenTerminating = definedNames.filter((n) => triviallyNonRecursive.includes(n) || !violatedNames.includes(n));
  const hofViolations = checkHofCallbacks(defs, definedNames, provenTerminating, detectUserDefinedHofs(defs, exprs));
  return [...doViolations, ...namedLetViolations, ...baseViolations, ...hofViolations];
}
