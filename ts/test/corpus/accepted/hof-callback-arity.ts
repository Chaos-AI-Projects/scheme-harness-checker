// From check.test.ts: a HOF callback's arity is read from its definition, not its type
function inc(x: number): number { return x - 1; }
const pos = (x: number): boolean => x > 0;
const xs = [1, 2];
const ys = xs.map(inc).filter(pos).map((x: number) => x * 2);
