// From safeinteger.test.ts: HC-21 keeps a loop over a number parameter behind a Number.isSafeInteger return
// The last line is added here, so that the halting check runs the code.
function f(n: number): number {
  if (!Number.isSafeInteger(n)) return 0;
  let k = 0;
  for (let i = 0; i < n; i++) { k = k + 1; }
  return k;
}

console.log(f(5));
