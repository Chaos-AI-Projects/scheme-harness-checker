// The IR datum type: the s-expression form the Scheme checker reads, as plain JavaScript values.
// A proper list is an array, an improper list is a Dotted, and a symbol is an interned Sym, so
// symbols compare with ===. Every list read from source is a fresh object, so the termination port
// can key tables on source forms by identity, as the Scheme code does with eq-hashtables.
// The reader exists for test fixtures and the differential test; the lowering builds data directly.

export class Sym {
  readonly name: string;
  constructor(name: string) {
    this.name = name;
  }
}

/** An improper list: `items` followed by a non-list `tail`, as in `(a b . c)`. */
export class Dotted {
  readonly items: Datum[];
  readonly tail: Datum;
  constructor(items: Datum[], tail: Datum) {
    this.items = items;
    this.tail = tail;
  }
}

export class Vec {
  readonly items: Datum[];
  constructor(items: Datum[]) {
    this.items = items;
  }
}

export class Char {
  readonly value: string;
  constructor(value: string) {
    this.value = value;
  }
}

export type Datum = Sym | number | string | boolean | Char | Vec | Dotted | Datum[];

const SYMBOLS = new Map<string, Sym>();

export function sym(name: string): Sym {
  let s = SYMBOLS.get(name);
  if (!s) {
    s = new Sym(name);
    SYMBOLS.set(name, s);
  }
  return s;
}

export function isSym(d: Datum): d is Sym {
  return d instanceof Sym;
}

/** Scheme's pair?: a non-empty list, proper or not. */
export function isPair(d: Datum): d is Datum[] | Dotted {
  return (Array.isArray(d) && d.length > 0) || d instanceof Dotted;
}

export function isNull(d: Datum): boolean {
  return Array.isArray(d) && d.length === 0;
}

/** Scheme's list?: a proper list, the empty list included. */
export function isList(d: Datum): d is Datum[] {
  return Array.isArray(d);
}

export function car(d: Datum): Datum {
  if (Array.isArray(d) && d.length > 0) return d[0]!;
  if (d instanceof Dotted) return d.items[0]!;
  throw new TypeError(`car: not a pair: ${write(d)}`);
}

/** Scheme's cdr. A proper list's cdr is a fresh array, so never key a table on one. */
export function cdr(d: Datum): Datum {
  if (Array.isArray(d) && d.length > 0) return d.slice(1);
  if (d instanceof Dotted) return d.items.length > 1 ? new Dotted(d.items.slice(1), d.tail) : d.tail;
  throw new TypeError(`cdr: not a pair: ${write(d)}`);
}

export const cadr = (d: Datum): Datum => car(cdr(d));
export const cddr = (d: Datum): Datum => cdr(cdr(d));
export const caddr = (d: Datum): Datum => car(cddr(d));
export const cdddr = (d: Datum): Datum => cdr(cddr(d));
export const caadr = (d: Datum): Datum => car(cadr(d));
export const cdadr = (d: Datum): Datum => cdr(cadr(d));

/** A proper list's elements; anything else has none. */
export function elements(d: Datum): Datum[] {
  return Array.isArray(d) ? d : [];
}

/** Scheme's equal?. */
export function equal(a: Datum, b: Datum): boolean {
  if (a === b) return true;
  if (Array.isArray(a)) return Array.isArray(b) && a.length === b.length && a.every((x, i) => equal(x, b[i]!));
  if (a instanceof Dotted) {
    return b instanceof Dotted && equal(a.items, b.items) && equal(a.tail, b.tail);
  }
  if (a instanceof Vec) return b instanceof Vec && equal(a.items, b.items);
  if (a instanceof Char) return b instanceof Char && a.value === b.value;
  return false;
}

// ---------------------------------------------------------------
// Writer
// ---------------------------------------------------------------

const CHAR_NAMES: Record<string, string> = { " ": "space", "\n": "newline", "\t": "tab", "\0": "nul" };

/** Scheme's write. Equal data write the same text, so the port uses it for equal?-keyed tables. */
export function write(d: Datum): string {
  if (d instanceof Sym) return d.name;
  if (typeof d === "number") return String(d);
  if (typeof d === "boolean") return d ? "#t" : "#f";
  if (typeof d === "string") return JSON.stringify(d);
  if (d instanceof Char) return `#\\${CHAR_NAMES[d.value] ?? d.value}`;
  if (d instanceof Vec) return `#(${d.items.map(write).join(" ")})`;
  if (d instanceof Dotted) return `(${d.items.map(write).join(" ")} . ${write(d.tail)})`;
  return `(${d.map(write).join(" ")})`;
}

// ---------------------------------------------------------------
// Reader
// ---------------------------------------------------------------

const DELIMITERS = new Set([..."()[]\";'`,"]);
const NAMED_CHARS: Record<string, string> = { space: " ", newline: "\n", tab: "\t", nul: "\0", linefeed: "\n" };
const QUOTES: Record<string, string> = { "'": "quote", "`": "quasiquote", ",": "unquote", ",@": "unquote-splicing" };
const NUMBER = /^[+-]?(\d+\.?\d*|\.\d+)(e[+-]?\d+)?$/i;
const CLOSE = Symbol("close");
const DOT = Symbol("dot");

class Reader {
  private readonly src: string;
  private pos = 0;
  constructor(src: string) {
    this.src = src;
  }

  private fail(message: string): never {
    throw new SyntaxError(`${message} at offset ${this.pos}`);
  }

  private isDelimiter(c: string | undefined): boolean {
    return c === undefined || /\s/.test(c) || DELIMITERS.has(c);
  }

  /** Skip whitespace and comments; true when input remains. */
  skip(): boolean {
    for (;;) {
      const c = this.src[this.pos];
      if (c === undefined) return false;
      if (/\s/.test(c)) this.pos++;
      else if (c === ";") {
        while (this.pos < this.src.length && this.src[this.pos] !== "\n") this.pos++;
      } else if (this.src.startsWith("#|", this.pos)) {
        const end = this.src.indexOf("|#", this.pos + 2);
        if (end < 0) this.fail("unterminated block comment");
        this.pos = end + 2;
      } else if (this.src.startsWith("#;", this.pos)) {
        this.pos += 2;
        this.datum();
      } else return true;
    }
  }

  datum(): Datum {
    const d = this.token();
    if (d === CLOSE) this.fail("unexpected close paren");
    if (d === DOT) this.fail("unexpected dot");
    return d;
  }

  private token(): Datum | typeof CLOSE | typeof DOT {
    if (!this.skip()) this.fail("unexpected end of input");
    const c = this.src[this.pos]!;
    if (c === "(" || c === "[") {
      this.pos++;
      return this.list(c === "(" ? ")" : "]");
    }
    if (c === ")" || c === "]") {
      this.pos++;
      return CLOSE;
    }
    if (c === "'" || c === "`" || c === ",") {
      const mark = this.src.startsWith(",@", this.pos) ? ",@" : c;
      this.pos += mark.length;
      return [sym(QUOTES[mark]!), this.datum()];
    }
    if (c === '"') return this.string();
    if (c === "#") return this.hash();
    const start = this.pos;
    let escaped = "";
    let escapes = false;
    while (!this.isDelimiter(this.src[this.pos])) {
      // R6RS inline hex escape \xHH; inside a symbol. Chez writes -~1 as \x2D;~1.
      if (this.src.startsWith("\\x", this.pos)) {
        const end = this.src.indexOf(";", this.pos);
        const hex = end < 0 ? "" : this.src.slice(this.pos + 2, end);
        if (!/^[0-9a-f]+$/i.test(hex)) this.fail("bad inline hex escape");
        escaped += String.fromCodePoint(parseInt(hex, 16));
        escapes = true;
        this.pos = end + 1;
      } else escaped += this.src[this.pos++];
    }
    if (escapes) return sym(escaped);
    const text = this.src.slice(start, this.pos);
    if (text === ".") return DOT;
    if (NUMBER.test(text)) return Number(text);
    if (/^[+-]?\d+\/\d+$/.test(text)) {
      const [n, d] = text.split("/");
      return Number(n) / Number(d);
    }
    return sym(text);
  }

  private list(close: string): Datum {
    const items: Datum[] = [];
    for (;;) {
      if (!this.skip()) this.fail("unterminated list");
      if (this.src[this.pos] === close) {
        this.pos++;
        return items;
      }
      const t = this.token();
      if (t === CLOSE) this.fail("mismatched close paren");
      if (t === DOT) {
        if (items.length === 0) this.fail("dot at list start");
        const tail = this.datum();
        if (!this.skip() || this.src[this.pos] !== close) this.fail("expected close paren after dotted tail");
        this.pos++;
        if (Array.isArray(tail)) return [...items, ...tail];
        if (tail instanceof Dotted) return new Dotted([...items, ...tail.items], tail.tail);
        return new Dotted(items, tail);
      }
      items.push(t);
    }
  }

  private string(): string {
    let out = "";
    this.pos++;
    for (;;) {
      const c = this.src[this.pos++];
      if (c === undefined) this.fail("unterminated string");
      if (c === '"') return out;
      if (c === "\\") {
        const e = this.src[this.pos++];
        out += e === "n" ? "\n" : e === "t" ? "\t" : e === "r" ? "\r" : e === "0" ? "\0" : (e ?? "");
      } else out += c;
    }
  }

  private hash(): Datum {
    const next = this.src[this.pos + 1];
    if (next === "(") {
      this.pos += 2;
      return new Vec(this.list(")") as Datum[]);
    }
    if (next === "\\") {
      this.pos += 2;
      const start = this.pos;
      this.pos++;
      while (!this.isDelimiter(this.src[this.pos])) this.pos++;
      const text = this.src.slice(start, this.pos);
      if (text.length === 1) return new Char(text);
      const named = NAMED_CHARS[text];
      if (named !== undefined) return new Char(named);
      if (/^x[0-9a-f]+$/i.test(text)) return new Char(String.fromCodePoint(parseInt(text.slice(1), 16)));
      this.fail(`unknown character #\\${text}`);
    }
    const start = this.pos;
    this.pos++;
    while (!this.isDelimiter(this.src[this.pos])) this.pos++;
    const text = this.src.slice(start, this.pos);
    if (text === "#t" || text === "#true") return true;
    if (text === "#f" || text === "#false") return false;
    this.fail(`unsupported syntax ${text}`);
  }
}

/** Every top-level datum in `source`. */
export function readAll(source: string): Datum[] {
  const r = new Reader(source);
  const out: Datum[] = [];
  while (r.skip()) out.push(r.datum());
  return out;
}

/** The single datum in `source`. */
export function readOne(source: string): Datum {
  const all = readAll(source);
  if (all.length !== 1) throw new SyntaxError(`expected one datum, got ${all.length}`);
  return all[0]!;
}
