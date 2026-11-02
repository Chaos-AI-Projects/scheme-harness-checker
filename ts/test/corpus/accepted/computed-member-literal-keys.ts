// From check.test.ts: computed member access needs a literal or a number key
const xs = [1, 2]; const i = 1; console.log(xs[i], xs[0], ({ a: 1 })["a"]);
