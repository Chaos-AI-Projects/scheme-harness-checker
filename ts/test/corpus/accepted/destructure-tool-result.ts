// From check.test.ts: renamed and nested destructuring is accepted, the property name is not a value
// The last line is added here, so that the halting check runs the code.
async function main(): Promise<number> { const { tempC: t } = await getWeather({ city: "x" }); return t; }

main();
