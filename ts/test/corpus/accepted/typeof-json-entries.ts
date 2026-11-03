// From check.test.ts: HC-28 reads a JSON tool result by narrowing with typeof and iterating entries and values
async function main(): Promise<number> {
  const raw: unknown = JSON.parse('{"a": 1, "b": "x", "c": 2}');
  let total = 0;
  if (typeof raw === "object" && raw !== null) {
    for (const entry of Object.entries(raw)) {
      const [key, value] = entry;
      if (typeof value === "number" && key !== "skip") {
        total += value;
      }
    }
    for (const value of Object.values(raw)) {
      if (typeof value === "string") {
        console.log(value.toUpperCase());
      }
    }
  }
  return total;
}
main();
