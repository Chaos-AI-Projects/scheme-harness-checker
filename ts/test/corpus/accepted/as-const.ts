// From check.test.ts: casts and non-null assertions are rejected, as const is allowed
const xs = [1, 2] as const; console.log(xs);
