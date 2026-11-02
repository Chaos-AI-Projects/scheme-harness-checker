// From check.test.ts: a dynamic member key must be a number at run time, not just in its type
const xs = [1, 2, 3];
let total = 0;
for (let i = 0; i < xs.length; i++) { total += xs[i]; }
for (let j = xs.length - 1; j >= 0; j -= 1) { total += xs[j]; }
const k = 2;
console.log(total, xs[xs.length - 1], xs[k], xs[+k], xs[k * 2 - 1]);
