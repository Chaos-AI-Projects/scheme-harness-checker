// The bash command allowlist (HC-43, plans/hc-41-bash-checker.md in the vault). Every command the
// script runs must be named in the allowlist, and every flag it passes must be allowed for that
// command. The subset gate has already ruled out the constructs that hide which command runs, so
// this walk takes each command name as the literal word it is.

import { readFileSync } from "node:fs";
import { posix } from "node:path";
import { parseSync } from "sh-syntax";
import type { CallExpr, File, FuncDecl, Redirect, Word } from "sh-syntax";
import type { Violation } from "../violation.ts";
import { isInterpreter, literal, manyWords } from "./subset.ts";

export interface CommandRules {
  /** Option letters denied anywhere in a short cluster such as -nf. */
  denyShort?: string;
  /** Long options denied, and any abbreviation of them that getopt would accept. */
  denyLong?: readonly string[];
  /** Whole words denied, such as find's -exec. */
  denyWords?: readonly string[];
  /** A command whose arguments are a language of their own, checked by its own rule. */
  rules?: "find" | "sed";
  /** Option letters that take an argument. Left out, any option may take the next word. */
  argShort?: string;
  /** Long options that take an argument. Left out, any long option may take the next word. */
  argLong?: readonly string[];
  /** Words starting with + are option clusters too, as in tail's obsolete +1f. */
  plusOptions?: boolean;
  /** Every operand must start with this literal text; date reads any other operand as a time to set. */
  operandPrefix?: string;
}

export interface BashAllowlist {
  commands: Readonly<Record<string, CommandRules>>;
}

export const DEFAULT_ALLOWLIST: BashAllowlist = JSON.parse(
  readFileSync(new URL("../../../data/bash-safe.json", import.meta.url), "utf8"),
);

// Interpreters the subset gate does not know by their code flag, which read code from a file or
// stdin, or which run a shell command from their own input: awk's system(), ed's !, dc's !, m4's
// syscmd, make's recipes, and the database shells' escapes.
const MORE_INTERPRETERS = new Set([
  "awk", "gawk", "mawk", "nawk", "busybox", "tclsh", "wish", "expect", "pwsh", "Rscript", "R",
  "julia", "deno", "bun", "irb", "ipython", "guile", "racket", "scheme", "sbcl", "ghci", "runghc",
  "csi", "gdb", "vi", "vim", "nvim", "emacs", "ed", "ex", "make", "m4", "dc", "sqlite3", "mysql",
  "psql", "osascript", "java", "jshell", "fish", "tcsh", "csh", "yash", "toybox", "ts-node",
]);
// Every name in these families is an interpreter or a build of one: luajit, php-cgi, python3-dbg.
const INTERPRETER_FAMILY = /^(python|pypy|perl|ruby|lua|php)/;
const VERSION_SUFFIX = /[-.]?[0-9][0-9.-]*$/;

function interpreter(name: string): boolean {
  const base = posix.basename(name);
  return INTERPRETER_FAMILY.test(base)
    || [base, base.replace(VERSION_SUFFIX, "")].some((n) => isInterpreter(n) || MORE_INTERPRETERS.has(n));
}

// find's primaries, options and operators by how many operands follow them. A word in a primary's
// place must be one of these, so the walk never loses count of which words are operands.
const FIND_WORDS: ReadonlyMap<string, number> = new Map([
  ...[
    "-amin", "-anewer", "-atime", "-cmin", "-cnewer", "-context", "-ctime", "-D", "-files0-from",
    "-fls", "-fprint", "-fprint0", "-fstype", "-gid", "-group", "-ilname", "-iname", "-inum", "-ipath",
    "-iregex", "-iwholename", "-links", "-lname", "-maxdepth", "-mindepth", "-mmin", "-mtime", "-name",
    "-newer", "-path", "-perm", "-printf", "-regex", "-regextype", "-samefile", "-size", "-type", "-uid",
    "-used", "-user", "-wholename", "-xtype",
  ].map((w) => [w, 1] as const),
  ["-fprintf", 2],
  ...[
    "-H", "-L", "-P", "(", ")", "!", ",", "-a", "-and", "-o", "-or", "-not", "-d", "-daystart",
    "-depth", "-follow", "-ignore_readdir_race", "-noignore_readdir_race", "-mount", "-noleaf",
    "-xdev", "-warn", "-nowarn", "-empty", "-executable", "-false", "-true", "-nogroup", "-nouser",
    "-readable", "-writable", "-delete", "-ls", "-print", "-print0", "-prune", "-quit",
  ].map((w) => [w, 0] as const),
]);

// find's global options, which come before the starting paths rather than starting the expression.
const FIND_GLOBAL = new Set(["-H", "-L", "-P", "-D"]);

function findOperands(word: string): number | undefined {
  if (/^-newer[aBcmt][aBcmt]$/.test(word)) return 1;
  if (/^-O[0-9]*$/.test(word)) return 0;
  return FIND_WORDS.get(word);
}

// Redirection operators whose word is a path. Heredocs and here-strings take text instead.
const TEXT_REDIRECTS = new Set([71, 72, 73]);

export function checkBashCommands(code: string, allowlist: BashAllowlist = DEFAULT_ALLOWLIST): Violation[] {
  const bytes = new TextEncoder().encode(code);
  const at = (offset: number) => {
    const prefix = new TextDecoder().decode(bytes.subarray(0, offset));
    const lineStart = prefix.lastIndexOf("\n") + 1;
    return { line: prefix.split("\n").length, column: [...prefix.slice(lineStart)].length + 1 };
  };
  const out: Violation[] = [];
  const report = (offset: number, message: string) =>
    out.push({ kind: "not-whitelisted", message, ...at(offset) });

  let file: File;
  try {
    file = parseSync(code);
  } catch {
    // The subset gate reports the parse error.
    return out;
  }

  // A call skips the allowlist as a function only when it comes after a definition that always
  // runs in the script's own shell: a top-level statement, not in the background. A definition in a
  // subshell, a branch or another function's body may not exist when the call runs. bash refuses a
  // name such as ./ru\n and carries on, so only a plain identifier counts as defined.
  const defined = new Map<string, number>();
  for (const stmt of file.stmts) {
    if (stmt.cmd?.type === "FuncDecl" && !stmt.background) {
      const name = stmt.cmd.name?.value ?? "";
      if (/^[A-Za-z_][A-Za-z0-9_]*$/.test(name) && !defined.has(name)) defined.set(name, stmt.cmd.start);
    }
  }
  const functions = new Set<string>();
  const nodes: (CallExpr | Redirect)[] = [];
  const collect = (node: unknown): void => {
    if (node === null || typeof node !== "object") return;
    const type = (node as { type?: string }).type;
    if (type === "FuncDecl") functions.add((node as FuncDecl).name?.value ?? "");
    if (type === "CallExpr" || type === "Redirect") nodes.push(node as CallExpr | Redirect);
    for (const value of Object.values(node)) collect(value);
  };
  collect(file.stmts);

  const checkCall = (call: CallExpr) => {
    const [head, ...args] = call.args;
    if (!head) return;
    const name = literal(head);
    if (name === null) {
      report(head.start, "a command name that is not a literal word is not on the allowlist");
      return;
    }
    if (interpreter(name)) {
      report(head.start, `${name} is an interpreter, which runs code the checker never sees`);
      return;
    }
    if ((defined.get(name) ?? Infinity) < head.start) return;
    const rules = Object.hasOwn(allowlist.commands, name) ? allowlist.commands[name] : undefined;
    if (!rules) {
      report(head.start, `${name} is not on the allowlist`);
      return;
    }
    if (name === "unset") checkUnset(args);
    checkFlags(name, rules, args);
    if (rules.rules === "sed") checkSed(args);
    if (rules.rules === "find") checkFind(args);
  };

  const checkFlags = (name: string, rules: CommandRules, args: readonly Word[]) => {
    const hasRules = !!(rules.denyShort || rules.denyLong?.length || rules.denyWords?.length || rules.rules);
    // A -- right after an option that may take an argument is that argument, not the end of options.
    let argumentNext = false;
    let options = true;
    const operand = (word: Word) => {
      if (rules.operandPrefix === undefined) return;
      if (arrayWords(word)) {
        report(word.start, `${name} takes only operands starting with ${rules.operandPrefix}, and an expansion such as "$@" splits into several words`);
      } else if (!literalPrefix(word).startsWith(rules.operandPrefix)) {
        report(word.start, `${name} takes only operands starting with ${rules.operandPrefix}`);
      }
    };
    for (const word of args) {
      const value = literal(word);
      const isArgument = argumentNext;
      argumentNext = false;
      if (!options) {
        operand(word);
        continue;
      }
      if (value === "--" && rules.rules !== "find" && !isArgument) {
        options = false;
        continue;
      }
      if (value === null) {
        const plus = rules.plusOptions && literalPrefix(word).startsWith("+");
        if (hasRules && rules.rules !== "find" && (!cannotBeFlag(word) || plus || arrayWords(word))) {
          report(word.start, isArgument
            ? `an expansion as an option's argument to ${name} is not allowed; write the argument as a literal`
            : arrayWords(word)
            ? `an expansion such as "$@" passed to ${name} splits into several words, any of which may be a flag; put it after a literal --`
            : `an expansion passed to ${name} may hold a flag; put it after a literal --`);
        } else if (!isArgument) operand(word);
        continue;
      }
      if (rules.denyWords?.includes(value)) report(word.start, `${name} ${value} is not allowed`);
      if (value.startsWith("--")) {
        const option = value.split("=")[0]!;
        for (const long of rules.denyLong ?? []) {
          if (option.length > 2 && long.startsWith(option)) report(word.start, `${name} ${long} is not allowed`);
        }
        argumentNext = !value.includes("=") && option.length > 2
          && (rules.argLong?.some((long) => long.startsWith(option)) ?? true);
      } else if (value.startsWith("-") || rules.plusOptions && value.startsWith("+")) {
        const letters = value.slice(1);
        if (rules.denyShort) {
          for (const letter of letters) {
            if (rules.denyShort.includes(letter)) report(word.start, `${name} ${value[0]}${letter} is not allowed`);
          }
        }
        const taking = rules.argShort === undefined ? letters.length - 1
          : [...letters].findIndex((letter) => rules.argShort!.includes(letter));
        argumentNext = taking >= 0 && taking === letters.length - 1;
      } else if (!isArgument) operand(word);
    }
  };

  // bash's unset removes a function when given -f, or when no variable has the name. Either way a
  // later call to that name would run the program the function stood in for.
  const checkUnset = (args: readonly Word[]) => {
    let variablesOnly = false;
    for (const word of args) {
      const value = literal(word);
      if (value === "--") break;
      if (value === null || !value.startsWith("-") || value === "-") break;
      if (value.includes("f")) report(word.start, "unset -f is not allowed");
      if (value.includes("v")) variablesOnly = true;
    }
    if (variablesOnly) return;
    for (const word of args) {
      const value = literal(word);
      if (value === null ? functions.size > 0 : functions.has(value)) {
        report(word.start, "unset may remove a function here; use unset -v");
      }
    }
  };

  // GNU sed's e command and s///e run a shell, and w, r and their kin read or write files the
  // script names. A script is accepted only as a literal made of s///, d and p. With POSIXLY_CORRECT
  // set, getopt stops at the first operand, so an operand before the first -e is the script too.
  const checkSed = (args: readonly Word[]) => {
    const scripts: Word[] = [];
    let explicit = false;
    let operand: Word | undefined;
    let operandFirst = false;
    for (let i = 0; i < args.length; i++) {
      const word = args[i]!;
      const value = literal(word);
      if (value === "--") {
        operand ??= args[i + 1];
        break;
      }
      if (value?.startsWith("--")) {
        const [option, ...rest] = value.split("=");
        if (option!.length > 2 && "--expression".startsWith(option!)) {
          explicit = true;
          if (rest.length) checkSedScript(rest.join("="), word.start);
          else if (args[i + 1]) scripts.push(args[++i]!);
        } else if (option!.length > 2 && "--line-length".startsWith(option!) && !rest.length) i++;
      } else if (value?.startsWith("-") && value.length > 1) {
        for (let k = 1; k < value.length; k++) {
          const letter = value[k]!;
          if (letter === "i") break;
          if (letter === "e" || letter === "l") {
            const attached = value.slice(k + 1);
            if (letter === "e") explicit = true;
            if (letter === "e" && attached) checkSedScript(attached, word.start);
            else if (letter === "e" && args[i + 1]) scripts.push(args[++i]!);
            else if (!attached) i++;
            break;
          }
        }
      } else if (!operand) {
        operand = word;
        operandFirst = !explicit;
      }
    }
    if ((!explicit || operandFirst) && operand) scripts.push(operand);
    for (const word of scripts) {
      const value = literal(word);
      if (value === null) report(word.start, "a sed script must be a literal word");
      else checkSedScript(value, word.start);
    }
  };

  const checkSedScript = (script: string, offset: number) => {
    if (!sedScriptAllowed(script)) report(offset, "a sed script may hold only s///, d and p commands");
  };

  // find's arguments are walked as starting paths, then primaries and their operands. An expansion
  // among the paths may become a primary unless its literal start rules out an option, and once the
  // expression starts every word in a primary's place must be a literal the walk knows, so that it
  // counts the operands that follow. A glob or "$@" as an operand may expand to several words, and
  // find reads all but the first as primaries.
  const checkFind = (args: readonly Word[]) => {
    let operands = 0;
    let expression = false;
    for (const word of args) {
      const value = literal(word);
      if (operands > 0) {
        operands--;
        if (value === null && manyWords(word)) {
          report(word.start, "a glob or \"$@\" as a find primary's operand may expand to several words, which find reads as primaries");
        }
        continue;
      }
      if (value === null) {
        if (expression) {
          report(word.start, "an expansion in a find primary's place is not a primary; paths come before the expression");
        } else if (arrayWords(word)) {
          report(word.start, "an expansion such as \"$@\" given to find splits into several words, any of which may become a primary");
        } else if (!cannotBeFlag(word)) {
          report(word.start, "an expansion given to find may become a primary; start it with a literal path such as ./");
        }
      } else if (value.length > 1 && "-(),!".includes(value[0]!) || "(),!".includes(value)) {
        const count = findOperands(value);
        if (count === undefined) report(word.start, `find ${value} is not a primary the checker knows`);
        operands = count ?? 0;
        if (!FIND_GLOBAL.has(value) && !/^-O[0-9]*$/.test(value)) expression = true;
      } else if (expression) {
        report(word.start, `find ${value} is not a primary; paths come before the expression`);
      }
    }
  };

  // bash opens /dev/tcp/<host>/<port> and /dev/udp/<host>/<port> as sockets.
  const checkRedirect = (r: Redirect) => {
    if (TEXT_REDIRECTS.has(r.op) || !r.word) return;
    const value = literal(r.word);
    if (value !== null) {
      if (value !== "/dev/null" && (value.startsWith("/dev/") || posix.normalize(value).startsWith("/dev/"))) {
        report(r.word.start, `a redirection to ${value} is not allowed; only /dev/null is under /dev/`);
      }
      return;
    }
    const prefix = literalPrefix(r.word);
    const component = prefix.startsWith("/") ? prefix.slice(1).split("/") : null;
    const safe = prefix !== "" && (component === null
      || (component.length > 1 && !["", ".", "..", "dev"].includes(component[0]!)));
    if (!safe) report(r.word.start, "an expanded redirection target needs a literal directory prefix outside /dev/");
  };

  for (const node of nodes) {
    if (node.type === "CallExpr") checkCall(node);
    else checkRedirect(node);
  }
  return out;
}

// The literal text a word starts with, before its first expansion, glob or tilde.
function literalPrefix(word: Word): string {
  let prefix = "";
  for (const [i, part] of word.parts.entries()) {
    if (part.type === "Lit") {
      if (i === 0 && part.value.startsWith("~")) return "";
      const glob = part.value.search(/[*?[{\\]/);
      if (glob >= 0) return prefix + part.value.slice(0, glob);
      prefix += part.value;
    } else if (part.type === "SglQuoted" && !part.dollar) {
      prefix += part.value;
    } else if (part.type === "DblQuoted" && !part.dollar) {
      for (const inner of part.parts) {
        if (inner.type !== "Lit") return prefix;
        prefix += inner.value.replace(/\\([$`"\\\n])/g, "$1");
      }
    } else {
      return prefix;
    }
  }
  return prefix;
}

// Whether the word's literal start rules out a flag, as the ./ of "./$f" does.
function cannotBeFlag(word: Word): boolean {
  const prefix = literalPrefix(word);
  return prefix !== "" && !"-(!,".includes(prefix[0]!);
}

// Whether the word holds "$@", "${a[@]}", "${!a[@]}" or "${!pre@}" outside a command substitution.
// Each element after the first becomes a word of its own, without the literal start the first has.
function arrayWords(word: Word): boolean {
  const array = (node: unknown): boolean => {
    if (node === null || typeof node !== "object") return false;
    const p = node as { type?: string; param?: { value?: string } | null; index?: Word | null; names?: number };
    if (p.type === "CmdSubst") return false;
    if (p.type === "ParamExp" && (p.param?.value === "@" || literal(p.index ?? null) === "@" || p.names !== 0)) {
      return true;
    }
    return Object.values(node).some(array);
  };
  return word.parts.some(array);
}

// A sed script of commands separated by ; or newlines, each an optional address or range,
// optionally negated, then s/regex/replacement/flags with flags among g, p, i, I, m, M and digits,
// or d, or p. A regex address takes only /, and s takes one of SED_DELIMITERS.
const SED_DELIMITERS = new Set("/|#,:@%");

export function sedScriptAllowed(script: string): boolean {
  let i = 0;
  const blank = () => {
    while (i < script.length && " \t".includes(script[i]!)) i++;
  };
  // In a regex a bracket expression runs to its own ], so a delimiter inside it does not close the
  // regex. Its first ], or the one after ^, is literal, and so are a backslash and anything inside
  // [: :], [. .] and [= =].
  const bracket = (): boolean => {
    let j = i + 1;
    if (script[j] === "^") j++;
    if (script[j] === "]") j++;
    while (j < script.length && script[j] !== "]") {
      if (script[j] === "\n") return false;
      if (script[j] === "[" && ".:=".includes(script[j + 1] ?? "x")) {
        const end = script.indexOf(script[j + 1]! + "]", j + 2);
        if (end < 0 || script.slice(j, end).includes("\n")) return false;
        j = end + 1;
      }
      j++;
    }
    if (j >= script.length) return false;
    i = j;
    return true;
  };
  const delimited = (close: string, regex = true): boolean => {
    while (i < script.length && script[i] !== close) {
      if (script[i] === "\n") return false;
      if (script[i] === "\\") i++;
      else if (regex && script[i] === "[" && !bracket()) return false;
      i++;
    }
    if (i >= script.length) return false;
    i++;
    return true;
  };
  const address = (): boolean => {
    if (/[0-9]/.test(script[i] ?? "")) {
      while (/[0-9]/.test(script[i] ?? "")) i++;
    } else if (script[i] === "$") i++;
    else if (script[i] === "/") {
      i++;
      if (!delimited("/")) return false;
      while ("IM".includes(script[i] ?? "x")) i++;
    }
    return true;
  };
  while (i < script.length) {
    blank();
    if (i >= script.length) break;
    if (";\n".includes(script[i]!)) {
      i++;
      continue;
    }
    if (!address()) return false;
    blank();
    if (script[i] === ",") {
      i++;
      blank();
      const before = i;
      if (!address() || i === before) return false;
      blank();
    }
    if (script[i] === "!") {
      i++;
      blank();
    }
    const command = script[i++];
    if (command === "s") {
      const delimiter = script[i++] ?? "";
      if (!SED_DELIMITERS.has(delimiter)) return false;
      if (!delimited(delimiter) || !delimited(delimiter, false)) return false;
      while (i < script.length && /[gpiImM0-9]/.test(script[i]!)) i++;
    } else if (command !== "d" && command !== "p") {
      return false;
    }
    blank();
    if (i < script.length && !";\n".includes(script[i]!)) return false;
  }
  return true;
}
