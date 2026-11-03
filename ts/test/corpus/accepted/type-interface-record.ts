// From check.test.ts: HC-30 a type alias and an interface are skipped by the lowering; Record<K, T> lowers as a record
type Point = { x: number; y: number };
interface Named { readonly name: string; tag?: string; pos: Point }
function norm(p: Point): number {
  type Sq = number;
  interface Box { v: Sq }
  const b: Box = { v: p.x * p.x + p.y * p.y };
  return b.v;
}
const n: Named = { name: "a", pos: { x: 1, y: 2 } };
const counts: Record<string, number> = { a: 1, b: 2 };
let total = 0;
for (const v of Object.values(counts)) { total += v; }
console.log(norm(n.pos) + total);
