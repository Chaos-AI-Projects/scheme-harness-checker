// From check.test.ts: a const naming the decreasing argument is seen through
function count(n: number): number {
  if (!Number.isSafeInteger(n)) return 0;
  if (n <= 0) return 0;
  const m = n - 1;
  return 1 + count(m);
}
function down(n: number): number {
  if (!Number.isSafeInteger(n)) return 0;
  if (n <= 0) return 0;
  const k = n - 1;
  const m = k;
  return down(m);
}
console.log(count(3), down(2));
