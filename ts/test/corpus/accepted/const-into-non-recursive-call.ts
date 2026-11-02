// From check.test.ts: a const is seen through only into a call that can recurse back (HC-22 review 3)
function g(a: number): number { return a; }
function f(n: number): number {
  const m = n - 1;
  if (n === 0) { if (n > 100) return 0; }
  if (n === 1) { if (n > 100) return 1; }
  if (n === 2) { if (n > 100) return 2; }
  if (n === 3) { if (n > 100) return 3; }
  if (n === 4) { if (n > 100) return 4; }
  if (n === 5) { if (n > 100) return 5; }
  if (n === 6) { if (n > 100) return 6; }
  if (n === 7) { if (n > 100) return 7; }
  return g(m) + g(m) + g(m) + g(m) + g(m) + g(m) + g(m) + g(m) + g(m) + g(m) + g(m) + g(m) + g(m) + g(m) + g(m);
}
console.log(f(3));
