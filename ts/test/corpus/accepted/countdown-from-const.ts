// From safeinteger.test.ts: HC-21 keeps a countdown from a const literal
const n = 10; let k = 0; for (let i = n; i > 0; i--) { k = k + 1; }
