// From safeinteger.test.ts: HC-21 keeps a nested loop bounded by an outer loop variable
const xs = [1, 2, 3];
let k = 0;
for (let i = 0; i < xs.length; i++) { for (let j = 0; j < i; j++) { k = k + 1; } }
