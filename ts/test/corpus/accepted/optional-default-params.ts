// From check.test.ts: HC-32 fills optional and literal-default parameters at each direct call
function sum(n: number, acc = 0, label?: string): number {
  if (!Number.isSafeInteger(n)) return acc;
  if (n <= 0) return acc;
  return sum(n - 1, acc + n, label);
}
const fmt = (n: number, unit = "C", round = true): string => `${round ? Math.round(n) : n}${unit}`;
async function main(): Promise<string> {
  const w = await getWeather({ city: "Sydney" });
  console.log(sum(4), sum(3, 10, "x"));
  return fmt(w.tempC) + fmt(w.tempC, "F", false);
}
main();
