// From check.test.ts: HC-38 a name destructured in a for...of head does not capture the bound a recursive call decreases
function f(n: number, ps: [number, string][]): number {
  if (!Number.isSafeInteger(n)) return 0;
  if (n <= 0) return 0;
  let t = 0;
  for (const [k, s] of ps) { t += k; console.log(s); }
  return t + f(n - 1, ps);
}
f(3, [[1, "a"]]);
