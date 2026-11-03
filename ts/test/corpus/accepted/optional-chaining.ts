// From check.test.ts: HC-31 reads optional fields through ?. on properties and elements
type Hit = { title: string; meta?: { score: number; tags: string[] } };
async function main(): Promise<number> {
  const hits: Hit[] = [{ title: "a", meta: { score: 2, tags: ["x"] } }, { title: "b" }];
  let total = 0;
  for (const h of hits) {
    total += h.meta?.score ?? 0;
    const first = h.meta?.tags[0] ?? "none";
    console.log(first, h.meta?.tags.length ?? 0, h.meta?.["score"]);
  }
  const w: { tempC: number } | undefined = await getWeather({ city: "Sydney" });
  return total + (w?.tempC ?? 0);
}
main();
