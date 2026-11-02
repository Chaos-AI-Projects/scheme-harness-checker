// From safeinteger.test.ts: HC-21 keeps a loop over a number parameter inside a Number.isSafeInteger if
// The last line is added here, so that the halting check runs the code.
function f(n: number): number {
  let k = 0;
  if (Number.isSafeInteger(n)) { for (let i = n; i > 0; i--) { k = k + 1; } }
  return k;
}

console.log(f(5));
