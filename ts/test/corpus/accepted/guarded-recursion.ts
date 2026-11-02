// From safeinteger.test.ts: HC-21 keeps a guarded recursion on a number parameter
// The last line is added here, so that the halting check runs the code.
function count(n: number): number {
  if (!Number.isSafeInteger(n)) return 0;
  if (n <= 0) return 0;
  return count(n - 1);
}

console.log(count(5));
