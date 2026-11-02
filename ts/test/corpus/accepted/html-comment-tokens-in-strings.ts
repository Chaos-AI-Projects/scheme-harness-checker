// From check.test.ts: HTML-like comment tokens are rejected, a script parser reads them as comments
const s = '<!-- -->'; const t = `<!--`; console.log(s, t); // <!-- -->
