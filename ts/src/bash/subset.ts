// The bash subset gate (HC-42, plans/hc-41-bash-checker.md in the vault). A construct is rejected
// when it hides which command runs, when it runs text the checker never parsed, or when it outlives
// the script. Command substitution stays allowed: the walk descends into it, so its commands meet
// the same rules. Which commands and flags are allowed at all is the allowlist's job, not this one.

import { parseSync, ParseError } from "sh-syntax";
import type {
  ArithmCmd, ArithmExp, ArithmExpr, ArrayElem, Assign, BinaryArithm, BinaryTest, CallExpr, CmdSubst, Comment, CStyleLoop,
  DblQuoted, DeclClause, ExtGlob, File, FuncDecl, LetClause, Lit, ParamExp, Redirect, SglQuoted, Stmt, TestExpr, UnaryArithm, UnaryTest, Word, WordIter, WordPart,
} from "sh-syntax";
import type { Violation } from "../violation.ts";

// Each runs text the checker never parsed.
const RUNS_TEXT = new Set(["eval", "source", "."]);

// Builtins that change which program a name runs, run a string later, or re-run history.
const BUILTINS = new Set([
  "exec", "trap", "alias", "enable", "builtin", "command", "hash", "fc", "bind", "complete",
  "compgen", "jobs",
]);

// Unquoted, these parse as a DeclClause or LetClause. Quoted or escaped they parse as a plain
// command, yet bash still runs the builtin, so its assignments would go unchecked.
const DECL_WORDS = new Set(["declare", "typeset", "local", "export", "readonly", "let"]);

// Commands whose arguments name another command to run. The plan's seven, plus the other common
// wrappers that do the same.
const WRAPPERS = new Set([
  "xargs", "env", "nohup", "timeout", "nice", "sudo", "su", "doas", "stdbuf", "setsid", "chroot",
  "watch", "parallel", "unshare", "nsenter", "runuser", "ionice", "taskset", "chrt", "flock",
  "script", "strace", "ltrace", "busybox",
  // `time` itself is a keyword, but /usr/bin/time and \time reach here as commands.
  "time",
]);

// Interpreters, and the option letters (in a short cluster such as -ec) or long options that make
// an argument the code to run.
interface CodeFlags { short: string; long: readonly string[] }
const SHELL: CodeFlags = { short: "c", long: [] };
const INTERPRETERS = new Map<string, CodeFlags>([
  ...["bash", "sh", "dash", "zsh", "ksh", "mksh", "ash", "rbash"].map(
    (n) => [n, SHELL] as const),
  ["perl", { short: "eE", long: [] }],
  ["ruby", { short: "e", long: [] }],
  ["node", { short: "ep", long: ["--eval", "--print"] }],
  ["nodejs", { short: "ep", long: ["--eval", "--print"] }],
  ["php", { short: "r", long: [] }],
  ["lua", { short: "e", long: [] }],
]);
const PYTHON = /^(python[0-9.]*|pypy[0-9.]*)$/;

// Whether the command is a shell or interpreter. One that reads its code from stdin or a file runs
// text the checker never parsed, so the allowlist may never hold one.
export function isInterpreter(name: string): boolean {
  return codeFlags(name) !== undefined;
}

function codeFlags(name: string): CodeFlags | undefined {
  return PYTHON.test(name) ? { short: "c", long: [] } : INTERPRETERS.get(name);
}

// Variables whose value changes which program a literal name runs, how words split, or what bash
// runs on its own: PS4 is expanded, command substitutions included, under `set -x`. BASH_COMPAT 42
// and below makes the quotes in "${x/a/'$(cmd)'}" literal, so the substitution inside them runs.
// Every name starting with BASH is bash's own, and BASHPID+= evaluates its value as arithmetic.
// POSIXLY_CORRECT makes getopt stop at the first operand, so sed 'e id' -e p reads 'e id' as its
// script, and it puts bash itself in posix mode.
const PROTECTED = new Set([
  "PATH", "IFS", "ENV", "PS4", "PROMPT_COMMAND", "SHELLOPTS", "EXECIGNORE", "POSIXLY_CORRECT",
]);
// Variables a child program reads as code, a library path, or options that can run a command:
// TAR_OPTIONS=--to-command=id makes tar run id, and GIT_SSH_COMMAND, LESSOPEN and PAGER name a
// program to run. A plain assignment counts too, since the variable may already be exported.
const CHILD_CODE = new Set([
  "GCONV_PATH", "LOCPATH", "GLIBC_TUNABLES", "PAGER", "MANPAGER", "EDITOR", "VISUAL", "SHELL",
  "LESS", "LESSOPEN", "LESSCLOSE", "LESSEDIT", "LESSKEY", "LESSKEYIN", "PHPRC", "TCLLIBPATH",
]);
const CHILD_CODE_PREFIX = /^(NODE_|PERL|PYTHON|RUBY|LUA_|GIT_)|_(OPTIONS|OPTS)$/;
const isProtected = (name: string) =>
  PROTECTED.has(name) || name.startsWith("LD_") || name.startsWith("BASH")
  || CHILD_CODE.has(name) || CHILD_CODE_PREFIX.test(name);

// bash gives these the integer attribute, so it evaluates any value assigned to them as arithmetic,
// and a subscript in that value runs its command substitutions. SECONDS gets the attribute when the
// script first reads it. BASHPID, the other default integer, is protected, and EUID, PPID and UID
// are read-only.
const INTEGER_VARS = new Set(["OPTIND", "RANDOM", "SRANDOM", "HISTCMD", "SECONDS"]);
const INTEGER = /^-?[0-9]+$/;

// A prefix assignment to IFS lasts only for these builtins, which use it to split what they read.
const SPLITS_INPUT = new Set(["read", "mapfile", "readarray"]);

// An unquoted heredoc body split into lines as bash reads them: a line ending in an odd number of
// backslashes joins the next, and the joined line can end in one again.
function joinContinuations(body: string): string[] {
  const lines: string[] = [];
  let pending = "";
  for (const line of body.split("\n")) {
    const joined = pending + line;
    const trailing = /\\*$/.exec(joined)![0].length;
    if (trailing % 2 === 1) pending = joined.slice(0, -1);
    else {
      lines.push(joined);
      pending = "";
    }
  }
  if (pending !== "") lines.push(pending);
  return lines;
}

const IDENTIFIER = /^[A-Za-z_][A-Za-z0-9_]*$/;

// Builtins that assign or unset the variables named in their arguments: the option letters that
// take an argument, those whose argument is a name, those whose argument is a callback, and which
// operands are names.
interface NameArgs { opts: string; names: string; callback: string; operands: "all" | 0 | 1 | null }
const MAPFILE: NameArgs = { opts: "dnOsuCc", names: "", callback: "C", operands: 0 };
const ASSIGNING = new Map<string, NameArgs>([
  ["read", { opts: "adinNptu", names: "a", callback: "", operands: "all" }],
  ["printf", { opts: "v", names: "v", callback: "", operands: null }],
  ["mapfile", MAPFILE],
  ["readarray", MAPFILE],
  ["getopts", { opts: "", names: "", callback: "", operands: 1 }],
  ["unset", { opts: "", names: "", callback: "", operands: "all" }],
  ["wait", { opts: "p", names: "p", callback: "", operands: null }],
]);

// set -k and the keyword option make every NAME=value argument an assignment, unchecked.
const KEYWORD_MODE = "keyword mode turns arguments into assignments";
// With history and histexpand on, bash rewrites every later line before it parses it.
const HISTORY = "history expansion rewrites lines after the checker read them";
const COMPAT = "a compat level makes the quotes in ${x/a/'...'} literal, so a substitution inside them runs";
const HISTORY_OPTIONS = new Set(["history", "histexpand"]);

// ${x@P} runs prompt expansion, which runs command substitutions held in the value.
const OTHER_PARAM_OPS = 100;
// ${x=w} and ${x:=w} assign x.
const ASSIGN_PARAM_OPS = new Set([87, 88]);
// ${x+w}, ${x-w}, ${x=w} and their : forms, whose word bash expands as a string. A pattern word, as
// in ${x#w}, and the message of ${x?w} take their quotes as quoting.
const WORD_PARAM_OPS = new Set([81, 82, 83, 84, 87, 88]);
const HEREDOC_OPS = new Set([71, 72]);
const DASH_HEREDOC = 72;
// = and the compound assignments += through >>=, the ones bash parses, and ++ / --.
const ASSIGN_ARITH_OPS = new Set([87, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58]);
const INC_DEC_OPS = new Set([41, 42]);
// [[ -v name ]]
const TEST_VAR_SET = 127;
// [[ -eq ]] through [[ -gt ]], which evaluate both operands as arithmetic.
const INT_TEST_OPS = new Set([133, 134, 135, 136, 137, 138]);
// Where test's -v is the unary operator rather than a string operand.
const OPERAND_START = new Set(["!", "(", "-a", "-o"]);
// The binary operators of test and [, after which a word before them is only a string.
const TEST_BINARY_OPS = new Set(["=", "==", "!=", "<", ">", "-eq", "-ne", "-lt", "-le", "-gt", "-ge", "-nt", "-ot", "-ef", "-a", "-o"]);
// A [[ -v ]] operand naming one array element.
const INDEXED = /^[A-Za-z_][A-Za-z0-9_]*\[[A-Za-z0-9_]+\]$/;

// Option B of the plan: past this point a form is accepted only when bash and sh-syntax are known
// to read it alike, and everything else is rejected even when it would be safe.
// ${x:-word}, the one expansion operator kept.
const DEFAULT_OP = 84;
// A subscript the parser and bash both read as one number or one name, or an array's @ and *.
const SUBSCRIPT = /^([0-9]+|[A-Za-z_][A-Za-z0-9_]*|@|\*)$/;
const SET_ONLY = "set accepts only -e, -u, -x, -o pipefail, -o errexit and -o nounset";
const SET_OPTIONS = new Set(["pipefail", "errexit", "nounset"]);

/** Checks a bash script against the subset gate. Every violation is reported, in source order. */
export function checkBashSubset(code: string): Violation[] {
  const bytes = new TextEncoder().encode(code);
  const at = (offset: number) => {
    const prefix = new TextDecoder().decode(bytes.subarray(0, offset));
    const lineStart = prefix.lastIndexOf("\n") + 1;
    return { line: prefix.split("\n").length, column: [...prefix.slice(lineStart)].length + 1 };
  };
  const out: Violation[] = [];
  const report = (offset: number, message: string) =>
    out.push({ kind: "unsupported-syntax", message, ...at(offset) });
  const byteOffset = (index: number) => new TextEncoder().encode(code.slice(0, index)).length;

  // bash drops a NUL, so a heredoc line \0E) ends the body for bash alone. sh-syntax joins a
  // backslash-CR-LF as a continuation and bash does not, so the next line would hide in arguments.
  if (code.includes("\0")) report(byteOffset(code.indexOf("\0")), "a NUL byte is read differently by bash and the parser");
  if (code.includes("\r")) report(byteOffset(code.indexOf("\r")), "a carriage return is read differently by bash and the parser");
  // bash removes every backslash-newline before it reads a token, and sh-syntax does not after a $,
  // so "$\<newline>(cmd)" is plain text to the parser and a substitution to bash. A continuation is
  // allowed only as one backslash after a blank, where no token is open. A longer odd run ends in a
  // literal backslash, which is a token.
  // The allowed ones must also lie outside quotes, heredocs and comments, checked after the parse.
  const continuations: number[] = [];
  for (const m of code.matchAll(/\\+\n/g)) {
    const run = m[0].length - 1;
    if (run % 2 === 1 && (run > 1 || !" \t".includes(code[m.index - 1] || "\n"))) {
      report(byteOffset(m.index), "a line continuation inside a word is read differently by bash and the parser");
    } else if (run % 2 === 1) continuations.push(byteOffset(m.index + run - 1));
  }
  const checkContinuations = (start: number, end: number) => {
    const inside = continuations.find((c) => c >= start && c < end);
    if (inside !== undefined) report(inside, "a line continuation inside quotes, a heredoc or a comment is not supported");
  };

  // A name the script assigns, unsets or tests must be a literal identifier: a subscript is
  // arithmetic, which runs command substitutions. An assigned name must also not be protected.
  const checkName = (value: string | null, offset: number, assigned: boolean) => {
    if (value === null) report(offset, "a variable name is not a literal word");
    else if (!IDENTIFIER.test(value)) report(offset, `'${value}' is not a variable name`);
    else if (assigned && isProtected(value)) report(offset, `assignment to ${value}`);
  };
  // A name whose value the builtin or loop sets to text the checker never sees.
  const checkTarget = (value: string | null, offset: number) => {
    checkName(value, offset, true);
    if (value !== null && INTEGER_VARS.has(value)) report(offset, `${value} evaluates its value as arithmetic`);
  };
  const checkNameExpr = (x: ArithmExpr | TestExpr | null, offset: number, assigned: boolean) =>
    checkName(x?.type === "Word" ? literal(x) : null, offset, assigned);
  // The parser takes only a name or a[i] here. a[i] parses as a ParamExp, whose subscript is checked
  // as arithmetic of its own.
  const checkArithTarget = (x: ArithmExpr | null, offset: number) => {
    const part = x?.type === "Word" ? x.parts[0] : undefined;
    if (part?.type === "ParamExp") checkName(part.param!.value, offset, true);
    else checkNameExpr(x, offset, true);
  };

  // Arithmetic evaluates a word's text as an expression, so text the parser saw only as a string
  // ("PATH=7", a command's output, a default value) could assign anything. A bare name or a plain
  // $x reads a value, which the arithmetic rules of HC-45 judge.
  const checkArith = (x: ArithmExpr | null): void => {
    if (!x) return;
    if (x.type === "Word") {
      for (const part of x.parts) {
        if (part.type !== "Lit" && !(part.type === "ParamExp" && plainParam(part))) {
          report(part.start, "arithmetic evaluates a quoted or substituted word as an expression");
        }
      }
    } else if (x.type === "BinaryArithm") {
      checkArith(x.x);
      checkArith(x.y);
    } else {
      checkArith(x.x);
    }
  };
  const checkIntOperand = (x: TestExpr | null) => {
    if (x?.type !== "Word") return;
    const value = literal(x);
    const [part, ...more] = x.parts;
    const inner = part?.type === "DblQuoted" && part.parts.length === 1 ? part.parts[0] : part;
    const ok = value !== null ? /^-?[0-9]+$/.test(value) || IDENTIFIER.test(value)
      : more.length === 0 && inner?.type === "ParamExp" && plainParam(inner);
    if (!ok) report(x.start, "an integer comparison evaluates its operand as arithmetic");
  };

  // Inside double quotes or an unquoted heredoc, bash keeps single quotes in a default or
  // alternative word as literal characters and still expands what they hold, so a $(...) the parser
  // saw as quoted text runs. Pattern words, as in ${x#'a'}, are not affected.
  const checkQuotedParams = (parts: readonly WordPart[]): void => {
    for (const part of parts) {
      if (part.type !== "ParamExp") continue;
      const exp = (part as ParamExp).exp;
      if (!exp || !WORD_PARAM_OPS.has(exp.op) || !exp.word) continue;
      for (const inner of exp.word.parts) {
        if (inner.type === "SglQuoted") {
          report(inner.start, "single quotes inside a quoted ${...} default are literal, so their text is expanded");
        }
      }
      checkQuotedParams(exp.word.parts);
    }
  };

  // bash and sh-syntax can disagree on where a heredoc body ends, and the lines between the two
  // ends run as commands the walk never saw. Inside $(...), bash ends the body at a line that starts
  // with the delimiter, such as E). In an unquoted heredoc bash also joins a line ending in a
  // backslash to the next before it compares, and sh-syntax does not. So every line of the body as
  // bash reads it must not start with the delimiter.
  const checkHeredoc = (r: Redirect, hdoc: Word | null) => {
    const delimiter = literal(r.word);
    if (!delimiter) {
      report(r.start, "a heredoc delimiter is not a literal word");
      return;
    }
    // sh-syntax gives an empty body no word.
    if (!hdoc) return;
    // An unquoted delimiter makes the body expand like a double-quoted string.
    const unquoted = r.word!.parts.every((p) => p.type === "Lit" && !p.value.includes("\\"));
    if (unquoted) checkQuotedParams(hdoc.parts);
    let body = new TextDecoder().decode(bytes.subarray(hdoc.start, hdoc.end));
    const strip = (l: string) => (r.op === DASH_HEREDOC ? l.replace(/^\t+/, "") : l);
    const lines = (unquoted ? joinContinuations(body) : body.split("\n")).map(strip);
    // sh-syntax's body span ends with the delimiter line it matched. If bash's joined reading no
    // longer ends with that line, a continuation absorbed it and bash reads past the parser's end.
    if (lines.at(-1) === delimiter) lines.pop();
    else if (strip(body.split("\n").at(-1)!) === delimiter) {
      report(hdoc.start, "a line continuation joins the heredoc delimiter into the body, so bash reads past it");
      return;
    }
    for (const line of lines) {
      if (line.startsWith(delimiter)) {
        report(hdoc.start, "a heredoc body line that bash may read as its delimiter hides the lines after it");
        return;
      }
    }
  };

  let file: File;
  try {
    file = parseSync(code, { keepComments: true });
  } catch (e) {
    if (e instanceof ParseError) {
      // sh-syntax sets pos on every parse error.
      report(e.pos!.offset, `parse error: ${e.text}`);
      return out;
    }
    // Other refusals, such as a zsh feature, are a plain error whose message starts "line:col: ".
    const message = e instanceof Error ? e.message : String(e);
    const [, line, column, text] = /^(\d+):(\d+): (.*)/s.exec(message) ?? [, "1", "1", message];
    const lineStart = new TextEncoder().encode(code.split("\n").slice(0, Number(line) - 1).join("\n")).length;
    report(Number(line) > 1 ? lineStart + Number(column) : Number(column) - 1, `parse error: ${text}`);
    return out;
  }

  // A function of the same name replaces the builtin, and in POSIX mode a prefix outlives a function.
  const functions = new Set<string>();
  const collectFunctions = (node: unknown): void => {
    if (node === null || typeof node !== "object") return;
    if ((node as { type?: string }).type === "FuncDecl") functions.add((node as FuncDecl).name?.value ?? "");
    for (const value of Object.values(node)) collectFunctions(value);
  };
  collectFunctions(file.stmts);
  // Words by end offset, to find the one written straight before a redirect operator.
  const wordsByEnd = new Map<number, Word>();
  const collectWords = (node: unknown): void => {
    if (node === null || typeof node !== "object") return;
    if ((node as { type?: string }).type === "Word") wordsByEnd.set((node as Word).end, node as Word);
    for (const value of Object.values(node)) collectWords(value);
  };
  collectWords(file.stmts);
  // IFS prefixes that last for one input-splitting builtin.
  const scopedIfs = new Set<Assign>();
  // Text straight inside double quotes or a heredoc body, where bash runs no process substitution.
  const plainText = new Set<WordPart>();
  // How many $(...) the walk is inside.
  let substDepth = 0;

  const visit = (node: unknown): void => {
    if (Array.isArray(node)) {
      node.forEach(visit);
      return;
    }
    if (node === null || typeof node !== "object") return;
    const n = node as { type?: string; start: number };
    switch (n.type) {
      case "Stmt": checkStmt(n as Stmt); break;
      case "CallExpr": checkCall(n as CallExpr); break;
      case "DeclClause": checkDecl(n as DeclClause); break;
      case "CoprocClause": report(n.start, "coproc is not supported"); break;
      case "TestDecl": report(n.start, "@test is not bash"); break;
      // sh-syntax joins a backslash-newline inside a comment, so the next line becomes part of it.
      // bash ends the comment at the newline and runs that line.
      case "Comment":
        if ((n as Comment).text.includes("\n")) report(n.start, "a comment ending in a backslash hides the next line from the checker");
        checkContinuations(n.start, (n as Comment).end);
        break;
      case "SglQuoted": checkContinuations(n.start, (n as SglQuoted).end); break;
      case "TimeClause": report(n.start, "time is not supported"); break;
      // In a pattern, a default word or a [[ =~ ]] regex, bash runs <(...) and >(...) where
      // sh-syntax keeps them as plain text.
      case "Lit":
        if (!plainText.has(n as Lit) && /[<>]\(/.test((n as Lit).value)) report(n.start, "process substitution inside a word runs a command the checker never parsed");
        if (!plainText.has(n as Lit) && /(^|[^\\])(\\\\)*\{/.test((n as Lit).value)) report(n.start, "brace expansion is not supported");
        break;
      case "ProcSubst": report(n.start, "process substitution runs a command the script cannot wait on"); break;
      // bash strips backslashes inside backticks before it parses the inside, so the heredoc and
      // quoting checks, which read the source, see different text from what runs.
      case "CmdSubst":
        if ((n as CmdSubst).backquotes) report(n.start, "backtick command substitution is not supported; use $(...)");
        // ${ cmd; } and ${| cmd; } (bash 5.3) run in the current shell, outside option B's forms.
        if ((n as CmdSubst).tempFile || (n as CmdSubst).replyVar) report(n.start, "function substitution ${ cmd; } is not supported; use $(...)");
        break;
      // sh-syntax keeps an extglob pattern as raw text, so the walk never sees a $(...) inside it.
      case "ExtGlob":
        report(n.start, "an extended glob is not supported");
        if (/[$`<>]/.test((n as ExtGlob).pattern?.value ?? "")) {
          report(n.start, "an extglob pattern holding an expansion hides code from the checker");
        }
        break;
      // Outside the C locale bash replaces $"..." with its translation, then expands that text.
      case "DblQuoted":
        if ((n as DblQuoted).dollar) report(n.start, "a translated $\"...\" string is expanded after translation");
        checkContinuations(n.start, (n as DblQuoted).end);
        checkQuotedParams((n as DblQuoted).parts);
        (n as DblQuoted).parts.forEach((p) => plainText.add(p));
        break;
      case "ParamExp": {
        const p = n as ParamExp;
        if (!acceptedParam(p)) report(n.start, "an operator in ${...} is not supported; use $x, ${x}, ${#x} or ${x:-word}");
        if (p.index && !SUBSCRIPT.test(litText(p.index))) report(n.start, "a subscript must be a literal number or a name");
        if (p.exp?.op === OTHER_PARAM_OPS && literal(p.exp.word)?.includes("P")) {
          report(n.start, "${...@P} runs prompt expansion on a value");
        }
        if (p.exp && ASSIGN_PARAM_OPS.has(p.exp.op) && p.param && isProtected(p.param.value)) {
          report(n.start, `assignment to ${p.param.value}`);
        }
        if (p.exp && ASSIGN_PARAM_OPS.has(p.exp.op) && p.param && INTEGER_VARS.has(p.param.value)
          && !INTEGER.test(literal(p.exp.word) ?? "")) {
          report(n.start, `${p.param.value} evaluates its value as arithmetic`);
        }
        // ${!a[@]} and ${!a[*]} list an array's keys; any other ${!...} reads a variable by name.
        if (p.excl && p.names === 0 && !["@", "*"].includes(litText(p.index))) {
          report(n.start, "indirect expansion hides which variable is read");
        }
        checkArith(p.index);
        checkArith(p.slice?.offset ?? null);
        checkArith(p.slice?.length ?? null);
        break;
      }
      case "ArithmExp":
      case "ArithmCmd": checkArith((n as ArithmExp | ArithmCmd).x); break;
      case "LetClause": (n as LetClause).exprs.forEach(checkArith); break;
      case "CStyleLoop": {
        const c = n as CStyleLoop;
        [c.init, c.cond, c.post].forEach(checkArith);
        break;
      }
      case "ArrayElem": checkArith((n as ArrayElem).index); break;
      case "Redirect": {
        const r = n as Redirect;
        // {NAME}>file stores the new descriptor's number in NAME.
        const fd = r.n?.value;
        if (fd?.startsWith("{")) report(n.start, "a named descriptor redirect is not supported");
        if (fd?.startsWith("{") && fd.endsWith("}")) checkName(fd.slice(1, -1), n.start, true);
        // bash reads the raw text of any word written straight before the operator, quotes and
        // all, so {a['b[$(cmd)]']}>file names a descriptor variable whose subscript runs cmd. The
        // parser saw an argument.
        const before = r.n ? undefined : wordsByEnd.get(r.start);
        if (before && bytes[before.start] === 0x7b && bytes[before.end - 1] === 0x7d) {
          report(before.start, "a {...} word straight before a redirect is a named descriptor to bash");
        }
        if (HEREDOC_OPS.has(r.op)) {
          const [d, ...more] = r.word?.parts ?? [];
          const quoted = r.op !== DASH_HEREDOC && more.length === 0 && d?.type === "SglQuoted" && !d.dollar && IDENTIFIER.test(d.value);
          if (!quoted) report(r.start, "only a quoted <<'WORD' heredoc whose WORD is a plain name is supported");
          if (substDepth > 0) report(r.start, "a heredoc inside $(...) is not supported");
          if (r.hdoc) checkContinuations(r.hdoc.start, r.hdoc.end);
          checkHeredoc(r, r.hdoc);
        }
        r.hdoc?.parts.forEach((p) => plainText.add(p));
        break;
      }
      case "BinaryArithm": {
        const b = n as BinaryArithm;
        if (ASSIGN_ARITH_OPS.has(b.op)) checkArithTarget(b.x, n.start);
        break;
      }
      case "UnaryArithm": {
        const u = n as UnaryArithm;
        if (INC_DEC_OPS.has(u.op)) checkArithTarget(u.x, n.start);
        break;
      }
      case "UnaryTest": {
        const u = n as UnaryTest;
        if (u.op === TEST_VAR_SET) report(n.start, "-v is not supported");
        if (u.op === TEST_VAR_SET && !INDEXED.test(litText(u.x))) checkNameExpr(u.x, n.start, false);
        if (u.x?.type === "Word") checkTestOperand(u.x);
        break;
      }
      case "BinaryTest": {
        const b = n as BinaryTest;
        if (INT_TEST_OPS.has(b.op)) [b.x, b.y].forEach(checkIntOperand);
        for (const x of [b.x, b.y]) if (x?.type === "Word") checkTestOperand(x);
        break;
      }
      case "WordIter":
      case "Assign": {
        const name = (node as WordIter | Assign).name;
        if (name && isProtected(name.value) && !scopedIfs.has(node as Assign)) report(n.start, `assignment to ${name.value}`);
        if (n.type === "Assign") checkArith((node as Assign).index);
        if (name && INTEGER_VARS.has(name.value)) {
          const a = n.type === "Assign" ? node as Assign : null;
          const value = a?.value ? literal(a.value) : "0";
          if (!a || a.append || a.array || !INTEGER.test(value ?? "")) {
            report(n.start, `${name.value} evaluates its value as arithmetic`);
          }
        }
        break;
      }
    }
    if (n.type === "CmdSubst") substDepth++;
    for (const value of Object.values(node)) visit(value);
    if (n.type === "CmdSubst") substDepth--;
  };

  const checkTestOperand = (word: Word) => {
    if (literal(word) === null && !quotedExpansion(word)) report(word.start, "a test operand must be a literal or one quoted expansion");
  };

  const checkStmt = (stmt: Stmt) => {
    // zsh's &| and &! do not parse as bash, so background is the only flag that can be set.
    if (stmt.background) {
      report(stmt.start, "a background job outlives the script");
    }
  };

  const checkCall = (call: CallExpr) => {
    const [head, ...rest] = call.args;
    if (!head) return;
    const raw = literal(head);
    if (raw === null) {
      report(head.start, "the command name is not a literal word");
      return;
    }
    const name = raw.includes("/") ? raw.slice(raw.lastIndexOf("/") + 1) : raw;
    // `time -- cmd` and `time -p -p cmd`: bash's time keyword takes these as its own options, and
    // sh-syntax leaves them as the command name, so the real command would escape every check here.
    if (raw.replace(/\\(.)/gs, "$1").startsWith("-")) {
      report(head.start, "a command name that starts with a dash is an option bash may skip");
    } else if (RUNS_TEXT.has(raw)) report(head.start, `'${raw}' runs text the checker never parsed`);
    else if (BUILTINS.has(name)) report(head.start, `${name} is not supported`);
    else if (WRAPPERS.has(name)) report(head.start, `${name} runs another command`);
    else if (DECL_WORDS.has(name)) {
      report(head.start, `a quoted or escaped declaration keyword hides what ${name} assigns`);
    }

    if (SPLITS_INPUT.has(name) && !functions.has(name)) {
      for (const a of call.assigns) if (a.name?.value === "IFS") scopedIfs.add(a);
    }

    const flags = codeFlags(name);
    if (flags) {
      for (const arg of rest) {
        const value = literal(arg);
        const isCode = value === null
          || (/^-[^-]/.test(value) && [...flags.short].some((c) => value.slice(1).includes(c)))
          || flags.long.some((l) => value === l || value.startsWith(`${l}=`));
        if (isCode) {
          report(arg.start, `${name} may be given code as an argument`);
          break;
        }
      }
    }
    const spec = ASSIGNING.get(name);
    if (spec) checkAssigning(name, spec, rest);
    if (name === "set") {
      checkSetOnly(rest);
      checkSet(rest);
    }
    if (name === "shopt") report(head.start, "shopt is not supported");
    if (name === "shopt") {
      for (const arg of rest) {
        const value = literal(arg);
        if (value === null) report(arg.start, "an option to shopt is not a literal word");
        else if (value === "keyword") report(arg.start, KEYWORD_MODE);
        else if (HISTORY_OPTIONS.has(value)) report(arg.start, HISTORY);
        else if (value.startsWith("compat")) report(arg.start, COMPAT);
      }
    }
    if (name === "test" || name === "[") {
      const operands = name === "[" && literal(rest.at(-1) ?? null) === "]" ? rest.slice(0, -1) : rest;
      for (const arg of operands) {
        if (literal(arg) === "-v") report(arg.start, "-v is not supported");
        checkTestOperand(arg);
        if (manyWords(arg)) report(arg.start, "a test operand that may expand to several words can carry -v and its name together");
      }
      for (const [i, arg] of operands.entries()) {
        const next = operands[i + 1];
        // A non-literal word before this one may be ! or -a at run time.
        const prev = i === 0 ? "!" : literal(operands[i - 1]!);
        const start = prev === null || OPERAND_START.has(prev);
        if (!start || !next) continue;
        const value = literal(arg);
        if (value === "-v") checkName(literal(next), next.start, false);
        // A non-literal word here may be -v at run time, so only a binary operator may follow it.
        else if (value === null && !TEST_BINARY_OPS.has(literal(next) ?? "")) {
          report(arg.start, "a non-literal word where a test operand starts may be an operator such as -v");
        }
      }
    }
    for (const arg of rest) {
      const part = arg.parts.find((p) => p.type === "ParamExp" || p.type === "CmdSubst");
      if (part) report(part.start, "an unquoted expansion splits into an unknown number of arguments");
    }
  };

  // Parses the builtin's options the way bash does, so a name attached to its option (-vNAME) or
  // behind a -- is still found.
  const checkAssigning = (name: string, spec: NameArgs, args: Word[]) => {
    const operands: Word[] = [];
    const seen = new Set<string>();
    let options = true;
    for (let i = 0; i < args.length; i++) {
      const arg = args[i]!;
      const value = literal(arg);
      if (!options) {
        operands.push(arg);
        continue;
      }
      if (value === null && !startsOperand(arg)) {
        report(arg.start, `an option to ${name} is not a literal word`);
        return;
      }
      if (value === null) {
        options = false;
        operands.push(arg);
        continue;
      }
      if (value === "--") {
        options = false;
        continue;
      }
      if (!/^-./.test(value)) {
        options = false;
        operands.push(arg);
        continue;
      }
      for (let j = 1; j < value.length; j++) {
        const c = value[j]!;
        seen.add(c);
        if (!spec.opts.includes(c)) continue;
        if (spec.callback.includes(c)) report(arg.start, `${name} -${c} runs a callback string`);
        if (spec.names.includes(c)) {
          const attached = value.slice(j + 1);
          const next = args[i + 1];
          if (attached) checkTarget(attached, arg.start);
          else checkTarget(next ? literal(next) : null, next?.start ?? arg.start);
        }
        if (j === value.length - 1) i++;
        break;
      }
    }
    // unset -f removes functions, whose names are not variables.
    if (name === "unset" && seen.has("f")) return;
    const names = spec.operands === "all" ? operands
      : spec.operands === null ? [] : operands.slice(spec.operands, spec.operands + 1);
    for (const word of names) {
      if (name === "unset") checkName(literal(word), word.start, true);
      else checkTarget(literal(word), word.start);
    }
  };

  // set reads every letter of a -cluster, and each o in it takes the next argument as an option
  // name. Options end at --, at a lone -, or at the first word not starting with - or +.
  const checkSet = (args: Word[]) => {
    for (let i = 0; i < args.length; i++) {
      const arg = args[i]!;
      const value = literal(arg);
      if (value === null) {
        report(arg.start, "an option to set is not a literal word");
        return;
      }
      if (value === "--" || !/^[-+]./.test(value)) return;
      for (const c of value.slice(1)) {
        if (c === "k" && value[0] === "-") report(arg.start, KEYWORD_MODE);
        if (c === "H" && value[0] === "-") report(arg.start, HISTORY);
        if (c !== "o") continue;
        const next = args[++i];
        if (!next) return;
        const option = literal(next);
        if (option === null) {
          report(next.start, "an option to set is not a literal word");
          return;
        }
        if (option === "keyword" && value[0] === "-") report(next.start, KEYWORD_MODE);
        if (HISTORY_OPTIONS.has(option) && value[0] === "-") report(next.start, HISTORY);
      }
    }
  };

  // set -e and friends, written as literal words and combined freely: -euo pipefail.
  const checkSetOnly = (args: Word[]) => {
    for (let i = 0; i < args.length; i++) {
      const arg = args[i]!;
      const value = literal(arg);
      if (value === null || !/^-[euxo]+$/.test(value)) {
        report(arg.start, SET_ONLY);
        return;
      }
      for (const c of value.slice(1)) {
        if (c !== "o") continue;
        const next = args[++i];
        if (!next || !SET_OPTIONS.has(literal(next) ?? "")) {
          report((next ?? arg).start, SET_ONLY);
          return;
        }
      }
    }
  };

  const checkDecl = (decl: DeclClause) => {
    // With -f or -F the names are functions (+f and +F do not do that), and export -n removes the
    // export attribute. A quoted NAME=value is rejected either way: bash parses it only at run time.
    let functions = false;
    for (const a of decl.args) {
      // A declaration re-parses a value that starts with ( as an array, running what it holds, and
      // declare, typeset and local do so for an expanded value too. export and readonly do not.
      if (a.name && a.value) {
        const value = literal(a.value);
        const exported = decl.variant?.value === "export" || decl.variant?.value === "readonly";
        if (value === null ? !(exported && quotedExpansion(a.value)) : value.startsWith("(")) {
          report(a.value.start, "a declaration re-parses a value that is not a literal, or starts with (, as an array; assign it on its own line");
        }
      }
      if (!a.naked || a.name) continue;
      const value = literal(a.value);
      if (value !== null && /^[-+]/.test(value) && !/^-[rx]+$/.test(value)) {
        report(a.start, "a declaration option other than -r and -x is not supported");
      }
      if (value === null) report(a.start, "a declaration argument is not a literal word");
      else if (/^-[A-Za-z]*i/.test(value)) {
        report(a.start, "an integer attribute evaluates every later assignment as arithmetic");
      } else if (decl.variant?.value !== "export" && /^[-+][A-Za-z]*n/.test(value)) {
        report(a.start, "a nameref hides which variable is assigned");
      } else if (/^[-+]/.test(value)) {
        if (/^-[A-Za-z]*[fF]/.test(value)) functions = true;
      } else if (/[=[]/.test(value)) {
        report(a.start, "a quoted assignment hides which variable is assigned");
      } else if (!functions) {
        checkName(value, a.start, true);
      }
    }
  };

  visit(file);
  return out;
}

// The text of a word made only of unquoted literal parts, or "" for anything else.
function litText(x: ArithmExpr | TestExpr | null): string {
  if (x?.type !== "Word" || x.parts.some((p) => p.type !== "Lit")) return "";
  return x.parts.map((p) => (p as { value: string }).value).join("");
}

// Whether the word's literal start, such as the "Hello " of "Hello $name", rules out an option.
function startsOperand(word: Word): boolean {
  const [part] = word.parts;
  const inner = part?.type === "DblQuoted" && !part.dollar ? part.parts[0] : part;
  const lead = inner?.type === "Lit" || (inner?.type === "SglQuoted" && !inner.dollar) ? inner.value : "";
  return lead !== "" && !hasGlob(lead, true) && !lead.replace(/\\(.)/gs, "$1").startsWith("-");
}

// Whether the word may expand to several words: an unquoted glob, brace or extglob, or "$@",
// "${a[@]}", "${!a[@]}" or "${!pre@}" anywhere in it, outside a command substitution.
export function manyWords(word: Word): boolean {
  const many = (node: unknown): boolean => {
    if (!node || typeof node !== "object") return false;
    const p = node as WordPart;
    if (p.type === "CmdSubst") return false;
    if (p.type === "ExtGlob") return true;
    if (p.type === "ParamExp" && (p.param?.value === "@" || litText(p.index) === "@" || p.names !== 0)) {
      return true;
    }
    return Object.values(node).some(many);
  };
  return word.parts.some((part, i) => part.type === "Lit" ? hasGlob(part.value, i < word.parts.length - 1) : many(part));
}

// $x, ${x}, ${#x}, ${a[i]} and ${x:-word} with a plain literal word: the expansions bash and the
// parser are known to read alike. The subscript is checked on its own.
function acceptedParam(p: ParamExp): boolean {
  const word = p.exp?.word?.parts ?? [];
  const plainDefault = p.exp?.op === DEFAULT_OP && !p.length
    && word.every((q) => q.type === "Lit" && !q.value.includes("\\"));
  return p.param !== null && !p.excl && p.names === 0 && !p.width && !p.isSet && !p.split
    && !p.globSubst && !p.rcExpand && !p.flags && !p.nestedParam && p.modifiers.length === 0
    && !p.slice && !p.repl && (!p.exp || plainDefault);
}

// One double-quoted parameter expansion or command substitution, such as "$x" or "$(id -u)".
function quotedExpansion(word: Word): boolean {
  const [part, ...more] = word.parts;
  if (more.length > 0 || part?.type !== "DblQuoted" || part.dollar || part.parts.length !== 1) return false;
  const inner = part.parts[0]!;
  return inner.type === "ParamExp" || (inner.type === "CmdSubst" && !inner.backquotes);
}

// A parameter read with no operator: no default or alternative word, no pattern replacement.
function plainParam(p: ParamExp): boolean {
  return !p.exp && !p.repl;
}

// The word's value after quote removal, or null when it holds an expansion, a glob, a brace
// expansion, a tilde, or $'...' / $"..." quoting, any of which bash resolves only at run time.
export function literal(word: Word | null): string | null {
  if (!word) return null;
  let value = "";
  for (const [i, part] of word.parts.entries()) {
    if (part.type === "Lit") {
      if (hasGlob(part.value, i < word.parts.length - 1) || (i === 0 && part.value.startsWith("~"))) {
        return null;
      }
      value += part.value.replace(/\\(.)/gs, "$1");
    } else if (part.type === "SglQuoted" && !part.dollar) {
      value += part.value;
    } else if (part.type === "DblQuoted" && !part.dollar
      && part.parts.every((p) => p.type === "Lit")) {
      value += part.parts.map((p) => (p as { value: string }).value.replace(/\\([$`"\\\n])/g, "$1"))
        .join("");
    } else {
      return null;
    }
  }
  return value;
}

// Whether an unescaped *, ?, { or [ makes the text a pattern. A [ opens a bracket expression only
// when a ] closes it, so a lone [ (the test command) is literal; when more of the word follows,
// the ] may be there. A ] straight after the [ is a member, not the close, so [] alone is literal.
function hasGlob(text: string, more: boolean): boolean {
  for (let k = 0; k < text.length; k++) {
    const c = text[k]!;
    if (c === "\\") k++;
    else if ("*?{".includes(c)) return true;
    else if (c === "[" && (more || text.includes("]", k + 2))) return true;
  }
  return false;
}
