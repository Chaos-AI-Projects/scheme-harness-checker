// From check.test.ts: renamed and nested destructuring is accepted, the property name is not a value
const ps = [{ name: "a" }]; console.log(ps.map(({ name: n }) => n));
