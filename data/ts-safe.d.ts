// The TypeScript whitelist: the only lib a checked program compiles against.
//
// A global or member is allowed exactly when this file declares it, and its declaration is its
// type, so this file plays the part of minimal-safe.txt and type-signatures.scm together. Leave
// out anything that reaches code or the host: constructor, __proto__, prototype, Function, eval,
// globalThis, process, require, fetch, timers. The interfaces the compiler insists on exist below
// with no members, so a function value or plain object exposes nothing.

interface Object {}
interface Function {}
interface CallableFunction {}
interface NewableFunction {}
interface IArguments {}
interface RegExp {}
interface Boolean {}

interface SymbolConstructor {
  readonly iterator: unique symbol;
}
// Needed only so the compiler can type for...of. The subset gate rejects any use of `Symbol`.
declare var Symbol: SymbolConstructor;

interface IteratorResult<T> {
  done?: boolean;
  value: T;
}
interface Iterator<T> {
  next(): IteratorResult<T>;
}
interface Iterable<T> {
  [Symbol.iterator](): Iterator<T>;
}
interface IterableIterator<T> extends Iterator<T> {
  [Symbol.iterator](): IterableIterator<T>;
}

interface Number {
  toFixed(fractionDigits?: number): string;
  toString(radix?: number): string;
}

interface NumberConstructor {
  readonly MAX_SAFE_INTEGER: number;
  readonly MIN_SAFE_INTEGER: number;
  isInteger(value: unknown): boolean;
  isFinite(value: unknown): boolean;
  isNaN(value: unknown): boolean;
  parseFloat(text: string): number;
  parseInt(text: string, radix?: number): number;
  (value: unknown): number;
}
declare var Number: NumberConstructor;
declare var NaN: number;
declare var Infinity: number;

interface String {
  readonly length: number;
  readonly [index: number]: string;
  at(index: number): string | undefined;
  charAt(pos: number): string;
  charCodeAt(index: number): number;
  concat(...strings: string[]): string;
  endsWith(searchString: string, endPosition?: number): boolean;
  includes(searchString: string, position?: number): boolean;
  indexOf(searchString: string, position?: number): number;
  lastIndexOf(searchString: string, position?: number): number;
  padEnd(maxLength: number, fillString?: string): string;
  padStart(maxLength: number, fillString?: string): string;
  repeat(count: number): string;
  replaceAll(searchValue: string, replaceValue: string): string;
  slice(start?: number, end?: number): string;
  split(separator: string, limit?: number): string[];
  startsWith(searchString: string, position?: number): boolean;
  substring(start: number, end?: number): string;
  toLowerCase(): string;
  toUpperCase(): string;
  trim(): string;
  trimEnd(): string;
  trimStart(): string;
  [Symbol.iterator](): IterableIterator<string>;
}

interface StringConstructor {
  (value?: unknown): string;
  fromCharCode(...codes: number[]): string;
}
declare var String: StringConstructor;

interface ReadonlyArray<T> {
  readonly length: number;
  readonly [n: number]: T;
  at(index: number): T | undefined;
  concat(...items: (T | ReadonlyArray<T>)[]): T[];
  every(predicate: (value: T, index: number) => boolean): boolean;
  filter(predicate: (value: T, index: number) => boolean): T[];
  find(predicate: (value: T, index: number) => boolean): T | undefined;
  findIndex(predicate: (value: T, index: number) => boolean): number;
  forEach(callback: (value: T, index: number) => void): void;
  includes(searchElement: T, fromIndex?: number): boolean;
  indexOf(searchElement: T, fromIndex?: number): number;
  join(separator?: string): string;
  map<U>(callback: (value: T, index: number) => U): U[];
  reduce<U>(callback: (accumulator: U, value: T, index: number) => U, initialValue: U): U;
  slice(start?: number, end?: number): T[];
  some(predicate: (value: T, index: number) => boolean): boolean;
  [Symbol.iterator](): IterableIterator<T>;
}

interface Array<T> {
  length: number;
  [n: number]: T;
  at(index: number): T | undefined;
  concat(...items: (T | ReadonlyArray<T>)[]): T[];
  every(predicate: (value: T, index: number) => boolean): boolean;
  filter(predicate: (value: T, index: number) => boolean): T[];
  find(predicate: (value: T, index: number) => boolean): T | undefined;
  findIndex(predicate: (value: T, index: number) => boolean): number;
  forEach(callback: (value: T, index: number) => void): void;
  includes(searchElement: T, fromIndex?: number): boolean;
  indexOf(searchElement: T, fromIndex?: number): number;
  join(separator?: string): string;
  map<U>(callback: (value: T, index: number) => U): U[];
  pop(): T | undefined;
  push(...items: T[]): number;
  reduce<U>(callback: (accumulator: U, value: T, index: number) => U, initialValue: U): U;
  reverse(): T[];
  shift(): T | undefined;
  slice(start?: number, end?: number): T[];
  some(predicate: (value: T, index: number) => boolean): boolean;
  sort(compare?: (a: T, b: T) => number): this;
  unshift(...items: T[]): number;
  [Symbol.iterator](): IterableIterator<T>;
}

interface ArrayConstructor {
  isArray(value: unknown): value is unknown[];
}
declare var Array: ArrayConstructor;

interface ObjectConstructor {
  keys(o: object): string[];
  entries<T>(o: { readonly [key: string]: T }): [string, T][];
}
declare var Object: ObjectConstructor;

interface Math {
  readonly E: number;
  readonly PI: number;
  abs(x: number): number;
  atan2(y: number, x: number): number;
  ceil(x: number): number;
  cos(x: number): number;
  exp(x: number): number;
  floor(x: number): number;
  log(x: number): number;
  log10(x: number): number;
  log2(x: number): number;
  max(...values: number[]): number;
  min(...values: number[]): number;
  pow(x: number, y: number): number;
  random(): number;
  round(x: number): number;
  sign(x: number): number;
  sin(x: number): number;
  sqrt(x: number): number;
  tan(x: number): number;
  trunc(x: number): number;
}
declare var Math: Math;

interface JSON {
  parse(text: string): unknown;
  stringify(value: unknown, replacer?: null, space?: number): string;
}
declare var JSON: JSON;

interface PromiseLike<T> {
  then<R1 = T, R2 = never>(
    onfulfilled?: ((value: T) => R1 | PromiseLike<R1>) | null,
    onrejected?: ((reason: unknown) => R2 | PromiseLike<R2>) | null,
  ): PromiseLike<R1 | R2>;
}
// Async functions return a Promise, and `await` needs `then` to find the awaited type.
interface Promise<T> {
  then<R1 = T, R2 = never>(
    onfulfilled?: ((value: T) => R1 | PromiseLike<R1>) | null,
    onrejected?: ((reason: unknown) => R2 | PromiseLike<R2>) | null,
  ): Promise<R1 | R2>;
}
type Awaited<T> = T extends null | undefined
  ? T
  : T extends object & { then(onfulfilled: infer F, ...args: infer _): any }
    ? F extends (value: infer V, ...args: infer _) => any
      ? Awaited<V>
      : never
    : T;
interface PromiseConstructor {
  all<T extends readonly unknown[] | []>(values: T): Promise<{ -readonly [P in keyof T]: Awaited<T[P]> }>;
}
declare var Promise: PromiseConstructor;

interface Console {
  log(...data: unknown[]): void;
}
declare var console: Console;
