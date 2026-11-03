// check.test.ts: field assignment on a local const object literal is accepted
function tally(words: string[]): { a: number; other: number } {
  const counts = { a: 0, other: 0 };
  for (const w of words) {
    if (w === "a") counts.a = counts.a + 1;
    else counts["other"] = counts.other + 1;
  }
  return counts;
}
async function main(): Promise<string> {
  const w = await getWeather({ city: "Sydney" });
  const o = { hot: false, n: 0 };
  o.hot = w.tempC > 25;
  o.n = w.tempC;
  for (const kv of Object.entries(tally(["a", "b", "a"]))) console.log(kv);
  return `${o.hot} ${o.n}`;
}
main();
