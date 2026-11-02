// From check.test.ts: a program in the subset that calls a tool is accepted
// The last line is added here, so that the halting check runs the code.
async function main(): Promise<string> {
  const cities = ["Sydney", "Hobart"];
  const temps: number[] = [];
  for (const city of cities) {
    const { tempC } = await getWeather({ city });
    temps.push(tempC);
  }
  const hot = temps.filter((t) => t > 25).map((t) => t * 2);
  let total = 0;
  for (let i = 0; i < hot.length; i++) {
    total += hot[i];
  }
  const label = total > 0 ? `hot: ${total}` : "none";
  console.log(JSON.stringify({ label, max: Math.max(...temps) }));
  return label;
}

main();
