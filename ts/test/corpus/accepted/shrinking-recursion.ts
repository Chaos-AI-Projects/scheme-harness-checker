// From check.test.ts: termination runs on the lowered program: a shrinking recursion is accepted
function count(n: number): number {
  if (!Number.isSafeInteger(n)) return 0;
  if (n <= 0) return 0;
  return 1 + count(n - 1);
}
console.log(count(3));
