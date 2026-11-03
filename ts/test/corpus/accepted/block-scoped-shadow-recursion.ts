// From check.test.ts: HC-29 a branch binding does not capture the outer name that a recursive call decreases
function f(n: number): number {
  if (!Number.isSafeInteger(n)) return 0;
  if (n <= 0) return 0;
  if (n > 2) { const n = 5; console.log(n); }
  return f(n - 1);
}
f(3);
