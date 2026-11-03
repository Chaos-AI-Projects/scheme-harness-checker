// From check.test.ts: HC-38 a JSON tool result is read with the entry destructured in the for...of head
async function main(): Promise<number> {
  const raw: unknown = JSON.parse('{"a": 1, "b": "x", "c": 2}');
  let total = 0;
  if (typeof raw === "object" && raw !== null) {
    for (const [key, value] of Object.entries(raw)) {
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
