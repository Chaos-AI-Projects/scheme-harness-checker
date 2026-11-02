// From check.test.ts: the whitelist covers the declared library surface
const xs = [3, 1, 2];
const s = "a,b,c";
const parts = s.split(",").map((p) => p.toUpperCase().trim());
const sorted = xs.slice().sort((a, b) => a - b);
const sum = xs.reduce((acc, x) => acc + x, 0);
const keys = Object.keys({ a: 1 });
const entries = Object.entries({ a: 1 });
const parsed: unknown = JSON.parse("{}");
const n = Number.isInteger(sum) ? Math.floor(sum / 2) : 0;
const isArr = Array.isArray(parsed);
const both = Promise.all([getWeather({ city: "x" })]);
console.log(parts, sorted, keys, entries, n, isArr, both, String(n), s.length);
