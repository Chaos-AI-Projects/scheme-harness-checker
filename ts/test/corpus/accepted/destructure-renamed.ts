// From check.test.ts: renamed and nested destructuring is accepted, the property name is not a value
const p = { name: "a" }; const { name: n } = p; console.log(n);
