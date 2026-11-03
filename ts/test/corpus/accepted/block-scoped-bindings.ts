// From check.test.ts: HC-29 const and let inside if, try, catch, a block and a case are accepted
async function main(): Promise<number> {
  let total = 0;
  const raw: unknown = JSON.parse("[1, 2]");
  if (Array.isArray(raw)) { const n = raw.length; total += n; } else { let m = 1; m = m + 1; total += m; }
  try { const w = await getWeather({ city: "Sydney" }); total += w.tempC; } catch (e) { const msg = String(e); console.log(msg); }
  { const inner = total * 2; console.log(inner); }
  switch (total) { case 0: const z = 1; return z; default: const d = total; console.log(d); break; }
  return total;
}
main();
