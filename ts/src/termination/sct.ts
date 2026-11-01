// Size-change termination core, ported from src/harness-checker/sct.ss (HC-2).
//
// Lee, Jones and Ben-Amram (2001). Each call edge from caller f to callee g carries a size-change
// graph: an arc [x, y, strict] says the value passed for g's parameter y is no larger than f's
// parameter x, and strictly smaller when strict is true. Composing graphs along a path gives the
// path's graph. A set of edge graphs terminates when every idempotent graph in its composition
// closure, with G;G = G and src = dst, has a strict arc from some parameter to itself.
//
// Parameters compare with Scheme's equal?, so a caller may use symbols for formals and lists for
// derived measures such as "bound minus formal". Building edge graphs is the caller's job; this
// module only composes and judges them.

import { equal, write, type Datum } from "../sexp.ts";

export type Arc = readonly [from: Datum, to: Datum, strict: boolean];

export interface ScGraph {
  readonly src: Datum;
  readonly dst: Datum;
  /** In one canonical order, so equal graphs have equal arcs. */
  readonly arcs: readonly Arc[];
}

export type ScVerdict = "terminates" | "no-descent" | "limit";

// Merge arcs that share [from, to], keeping strict when any copy is.
function normalizeArcs(arcs: readonly Arc[]): Arc[] {
  const out: Arc[] = [];
  for (const [from, to, strict] of arcs) {
    const i = out.findIndex((b) => equal(b[0], from) && equal(b[1], to));
    if (i < 0) out.push([from, to, strict]);
    else if (strict && !out[i]![2]) out[i] = [from, to, true];
  }
  return out;
}

const arcToString = (a: Arc): string => write([a[0], a[1], a[2]]);

export function makeScGraph(src: Datum, dst: Datum, arcs: readonly Arc[]): ScGraph {
  const keyed = normalizeArcs(arcs).map((a) => [arcToString(a), a] as const);
  keyed.sort((x, y) => (x[0] < y[0] ? -1 : x[0] > y[0] ? 1 : 0));
  return { src, dst, arcs: keyed.map(([, a]) => a) };
}

/** g1 then g2; requires g1.dst to equal g2.src. */
export function scCompose(g1: ScGraph, g2: ScGraph): ScGraph {
  const arcs: Arc[] = [];
  for (const a of g1.arcs) {
    for (const b of g2.arcs) {
      if (equal(a[1], b[0])) arcs.push([a[0], b[1], a[2] || b[2]]);
    }
  }
  return makeScGraph(g1.src, g2.dst, arcs);
}

const graphKey = (g: ScGraph): string => write([g.src, g.dst, g.arcs.map((a) => [a[0], a[1], a[2]])]);

/** The closure of graphs under composition, or null when it would hold more than cap graphs. */
export function scClosure(graphs: readonly ScGraph[], cap: number): ScGraph[] | null {
  const seen = new Set<string>();
  // `out` is newest first, as the Scheme accumulator is.
  const out: ScGraph[] = [];
  let work: ScGraph[] = [...graphs];
  while (out.length <= cap) {
    const g = work.shift();
    if (!g) return out.reverse();
    const key = graphKey(g);
    if (seen.has(key)) continue;
    out.unshift(g);
    const after = out.filter((h) => equal(g.dst, h.src)).map((h) => scCompose(g, h));
    const before = out.filter((h) => equal(h.dst, g.src)).map((h) => scCompose(h, g));
    seen.add(key);
    work = [...after, ...before, ...work];
  }
  return null;
}

function idempotent(g: ScGraph): boolean {
  return equal(g.src, g.dst) && graphKey(scCompose(g, g)) === graphKey(g);
}

function strictSelfArc(g: ScGraph): boolean {
  return g.arcs.some((a) => a[2] && equal(a[0], a[1]));
}

export function scCheck(graphs: readonly ScGraph[], cap: number): ScVerdict {
  const closure = scClosure(graphs, cap);
  if (!closure) return "limit";
  return closure.every((g) => !idempotent(g) || strictSelfArc(g)) ? "terminates" : "no-descent";
}
