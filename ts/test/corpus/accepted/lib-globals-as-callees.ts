// From check.test.ts: a lib global is usable only as a receiver or a callee
const n = Number("1"); const k = Object.keys({ a: n }); console.log(Math.max(n, 2), k);
