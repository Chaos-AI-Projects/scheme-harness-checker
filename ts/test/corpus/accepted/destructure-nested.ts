// From check.test.ts: renamed and nested destructuring is accepted, the property name is not a value
const { a: { b } } = { a: { b: 1 } }; console.log(b);
