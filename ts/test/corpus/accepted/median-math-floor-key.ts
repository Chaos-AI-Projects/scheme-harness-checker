// From check.test.ts: a Math call is a numeric key
// The last line is added here, so that the halting check runs the code.
function median(xs: number[]): number { const s = xs.slice().sort((a, b) => a - b); return s[Math.floor(s.length / 2)]; }

console.log(median([3, 1, 2]));
