// From check.test.ts: HC-34 String.prototype.replace with string arguments only
const raw = "temp: 21C, wind: 9kph";
const tidy = raw.replace("C", " degrees").replace("kph", " km/h").replaceAll(", ", "; ");
console.log(tidy);
