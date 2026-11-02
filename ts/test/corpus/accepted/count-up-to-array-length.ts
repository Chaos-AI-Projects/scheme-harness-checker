// From safeinteger.test.ts: HC-21 keeps a counter up to an array length
const xs = [1, 2, 3]; let t = 0; for (let i = 0; i < xs.length; i++) { t += xs[i]; }
