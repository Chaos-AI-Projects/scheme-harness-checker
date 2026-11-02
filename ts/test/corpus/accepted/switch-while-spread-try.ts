// From check.test.ts: try/catch, switch, while, destructuring and spread are in the subset
function classify(n: number): string {
  switch (n) {
    case 0: return "zero";
    default: return n < 0 ? "neg" : "pos";
  }
}
let k = 3;
while (k > 0) {
  k = k - 1;
}
const [head, ...rest] = [1, 2, 3];
const obj = { ...{ a: 1 }, b: head ?? 0 };
try {
  throw "boom";
} catch (e) {
  console.log(classify(rest.length), obj, e);
}
