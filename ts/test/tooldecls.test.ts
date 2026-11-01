import { test } from "node:test";
import assert from "node:assert/strict";
import { checkTypeScript } from "../src/check.ts";
import { schemaToType, toolDeclarations } from "../src/tool-decls.ts";

test("scalar JSON Schema types map to TypeScript types", () => {
  assert.equal(schemaToType({ type: "string" }), "string");
  assert.equal(schemaToType({ type: "number" }), "number");
  assert.equal(schemaToType({ type: "integer" }), "number");
  assert.equal(schemaToType({ type: "boolean" }), "boolean");
  assert.equal(schemaToType({ type: "null" }), "null");
});

test("a schema that says nothing is unknown, never any", () => {
  assert.equal(schemaToType({}), "unknown");
  assert.equal(schemaToType(true), "unknown");
  assert.equal(schemaToType(undefined), "unknown");
  assert.equal(schemaToType({ $ref: "#/definitions/x" }), "unknown");
  assert.equal(schemaToType({ type: "mystery" }), "unknown");
});

test("objects list their properties, optional unless required", () => {
  assert.equal(
    schemaToType({
      type: "object",
      properties: { city: { type: "string" }, days: { type: "integer" } },
      required: ["city"],
    }),
    "{ city: string; days?: number }",
  );
  assert.equal(schemaToType({ type: "object", properties: { "a-b": { type: "string" } }, required: ["a-b"] }),
               `{ "a-b": string }`);
  assert.equal(schemaToType({ type: "object" }), "{ [key: string]: unknown }");
  assert.equal(schemaToType({ type: "object", additionalProperties: { type: "number" } }),
               "{ [key: string]: number }");
});

test("arrays, unions, enums and consts", () => {
  assert.equal(schemaToType({ type: "array", items: { type: "string" } }), "string[]");
  assert.equal(schemaToType({ type: "array" }), "unknown[]");
  assert.equal(schemaToType({ type: "array", items: { anyOf: [{ type: "string" }, { type: "number" }] } }),
               "(string | number)[]");
  assert.equal(schemaToType({ type: ["string", "null"] }), "string | null");
  assert.equal(schemaToType({ oneOf: [{ type: "string" }, { type: "boolean" }] }), "string | boolean");
  assert.equal(schemaToType({ enum: ["a", "b\"c", 1, null] }), `"a" | "b\\"c" | 1 | null`);
  assert.equal(schemaToType({ const: "x" }), `"x"`);
  assert.equal(schemaToType({ allOf: [{ type: "object", properties: { a: { type: "string" } }, required: ["a"] },
                                      { type: "object", properties: { b: { type: "number" } }, required: ["b"] }] }),
               "({ a: string }) & ({ b: number })");
});

test("toolDeclarations writes one async declare function per tool, with its description", () => {
  const decls = toolDeclarations({
    getWeather: {
      description: "Current weather for a city.",
      inputSchema: { type: "object", properties: { city: { type: "string" } }, required: ["city"] },
      outputSchema: { type: "object", properties: { tempC: { type: "number" } }, required: ["tempC"] },
    },
    ping: { inputSchema: { type: "object", properties: {} } },
  });
  assert.equal(decls, [
    "/** Current weather for a city. */",
    "declare function getWeather(args: { city: string }): Promise<{ tempC: number }>;",
    "declare function ping(args: {}): Promise<unknown>;",
    "",
  ].join("\n"));
});

test("a description cannot close its comment early", () => {
  const decls = toolDeclarations({ t: { description: "ends */ declare var x: any; /*", inputSchema: {} } });
  assert.equal(decls.split("*/").length, 2, decls);
});

test("a tool name that is not a plain identifier is refused", () => {
  for (const name of ["get-weather", "1st", "a b", "delete", "constructor", "__proto__", ""]) {
    assert.throws(() => toolDeclarations({ [name]: { inputSchema: {} } }), /tool name/, name);
  }
});

test("declarations from schemas compile and gate a program", () => {
  const decls = toolDeclarations({
    getWeather: {
      inputSchema: { type: "object", properties: { city: { type: "string" } }, required: ["city"] },
      outputSchema: { type: "object", properties: { tempC: { type: "number" } }, required: ["tempC"] },
    },
  });
  const ok = checkTypeScript(
    `async function main() { const w = await getWeather({ city: "Sydney" }); return w.tempC; } main();`,
    { toolDeclarations: decls },
  );
  assert.deepEqual(ok.violations, []);
  const bad = checkTypeScript(`async function main() { return await getWeather({ town: "x" }); } main();`,
                              { toolDeclarations: decls });
  assert.equal(bad.ok, false);
  assert.equal(bad.violations[0].kind, "type-error");
});

test("a tool named main is refused, since programs define their own main", () => {
  assert.throws(() => toolDeclarations({ main: { inputSchema: {} } }), /tool name/);
});
