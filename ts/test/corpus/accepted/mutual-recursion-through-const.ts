// From check.test.ts: a const is seen through into a mutually recursive call (HC-22)
function even(n: number): boolean {
  if (!Number.isSafeInteger(n)) return false;
  if (n <= 0) return true;
  const m = n - 1;
  return odd(m);
}
function odd(n: number): boolean {
  if (!Number.isSafeInteger(n)) return false;
  if (n <= 0) return false;
  const m = n - 1;
  return even(m);
}
console.log(even(4));
