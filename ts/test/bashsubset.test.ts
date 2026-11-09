import { test } from "node:test";
import assert from "node:assert/strict";
import { checkBashSubset } from "../src/bash/subset.ts";

function assertClean(code: string): void {
  assert.deepEqual(checkBashSubset(code), []);
}

function assertRejected(code: string, fragment: string): void {
  const violations = checkBashSubset(code);
  assert.ok(
    violations.some((v) => v.kind === "unsupported-syntax" && v.message.includes(fragment)),
    `expected "${fragment}" for: ${code}\ngot ${JSON.stringify(violations)}`,
  );
}

test("a script inside the subset is accepted", () => {
  assertClean(`set -euo pipefail
dir="./data"
for f in a b; do echo "$f" | grep -c x; done
out=$(ls -1 "$dir")
echo "$out" > ./out.txt
count=$((1 + 2))
echo $((count + 1))
cat <<'EOF'
plain text
EOF
`);
});

test("a parse error is rejected with its position", () => {
  const violations = checkBashSubset("echo ok\nif then fi\n");
  assert.equal(violations.length, 1);
  assert.equal(violations[0]!.kind, "unsupported-syntax");
  assert.equal(violations[0]!.line, 2);
  assert.equal(violations[0]!.column, 1);
});

test("eval, source and . are rejected", () => {
  assertRejected("eval 'ls'", "eval");
  assertRejected("source ./lib.sh", "source");
  assertRejected(". ./lib.sh", "'.'");
});

test("a command name that is not a literal word is rejected", () => {
  assertRejected("$cmd x", "not a literal");
  assertRejected("$(pick) x", "not a literal");
  assertRejected('"$c" x', "not a literal");
  assertRejected("$'\\x65'val x", "not a literal");
  assertRejected("{eval,} x", "not a literal");
  assertRejected("ev?l x", "not a literal");
  assertRejected("~/bin/tool x", "not a literal");
});

test("quoting and escapes are removed before the name is judged", () => {
  assertRejected("e\\val x", "eval");
  assertRejected('"ev"al x', "eval");
  assertRejected("'ev'al x", "eval");
  assertRejected("/usr/bin/env ls", "env");
});

test("builtins that change what runs are rejected", () => {
  for (const name of ["exec", "trap", "alias", "enable", "builtin", "command", "hash", "compgen"]) {
    assertRejected(`${name} x`, name);
  }
  assertRejected("coproc cat", "coproc");
});

test("a background job is rejected", () => {
  assertRejected("sleep 1 &", "background");
});

test("an interpreter given code as an argument is rejected", () => {
  assertRejected("bash -c 'ls'", "code as an argument");
  assertRejected("sh -ec 'ls'", "code as an argument");
  assertRejected("/bin/bash -c ls", "code as an argument");
  assertRejected("python3 -c 'print(1)'", "code as an argument");
  assertRejected("perl -ne 'print'", "code as an argument");
  assertRejected("node --eval=1", "code as an argument");
  assertRejected('bash "$opt" x', "code as an argument");
  assertRejected("python3.10 -c 'print(1)'", "code as an argument");
  assertRejected("pypy3.10 -c 'print(1)'", "code as an argument");
  assertClean("bash ./build.sh");
  assertClean("node ./app.js");
  assertClean("perl --version");
});

test("commands that run another command are rejected", () => {
  for (const name of ["xargs", "env", "nohup", "timeout", "nice", "sudo", "su"]) {
    assertRejected(`${name} ls`, name);
  }
});

test("assigning a variable that changes what runs is rejected", () => {
  assertRejected("PATH=/tmp ls", "PATH");
  assertRejected("IFS=,", "IFS");
  assertRejected("export LD_PRELOAD=./x.so", "LD_PRELOAD");
  assertRejected("declare BASH_ENV=./x", "BASH_ENV");
  assertRejected("ENV=./x", "ENV");
  assertRejected("for IFS in a; do echo ok; done", "IFS");
  assertRejected("read -r PATH < ./f", "PATH");
  assertRejected("printf -v IFS x", "IFS");
  assertClean('MYPATH=/tmp; echo "$MYPATH"');
  assertClean("read -r line < ./f");
});

test("assigning a variable a child program reads as code or options is rejected", () => {
  assertRejected("TAR_OPTIONS=--to-command=id tar -xf ./a.tar", "TAR_OPTIONS");
  assertRejected("export NODE_OPTIONS='--require ./x.js'", "NODE_OPTIONS");
  assertRejected("export JAVA_TOOL_OPTIONS=x", "JAVA_TOOL_OPTIONS");
  assertRejected("read -r MAVEN_OPTS < ./f", "MAVEN_OPTS");
  assertRejected("PERL5OPT=-Mx cat ./f", "PERL5OPT");
  assertRejected("declare -x PYTHONPATH=./lib", "PYTHONPATH");
  assertRejected("RUBYOPT=x cat ./f", "RUBYOPT");
  assertRejected("LUA_INIT=x cat ./f", "LUA_INIT");
  assertRejected("export LESSOPEN='|id %s'", "LESSOPEN");
  assertRejected("GIT_SSH_COMMAND=id cat ./f", "GIT_SSH_COMMAND");
  assertRejected("export GIT_CONFIG_COUNT=1", "GIT_CONFIG_COUNT");
  for (const name of ["GCONV_PATH", "LOCPATH", "GLIBC_TUNABLES", "PAGER", "MANPAGER", "EDITOR", "VISUAL", "SHELL"]) {
    assertRejected(`${name}=./x cat ./f`, name);
  }
  assertClean('LESSONS=3; NODES=2; OPTIONS_FILE=./o; echo "$LESSONS $NODES $OPTIONS_FILE"');
});

test("POSIXLY_CORRECT is protected, since it changes how getopt reads a command's arguments", () => {
  assertRejected("POSIXLY_CORRECT=1 sed -e p ./x", "POSIXLY_CORRECT");
  assertRejected("export POSIXLY_CORRECT=1", "POSIXLY_CORRECT");
});

test("a nameref is rejected because it hides which variable is assigned", () => {
  assertRejected("local -n r=PATH", "nameref");
  assertRejected("declare -n r=x", "nameref");
  assertClean("declare -r x=1");
});

test("prompt expansion and a mapfile callback are rejected", () => {
  assertRejected('echo "${x@P}"', "@P");
  assertRejected("mapfile -C cb arr < ./f", "callback");
  assertRejected('echo "${x@Q}"', "an operator in ${...}");
  assertRejected("readarray -C cb arr < ./f", "callback");
  assertClean("mapfile -t arr < ./f");
  assertClean("printf '%s' -Cx");
});

test("process substitution is rejected", () => {
  assertRejected("diff <(ls a) <(ls b)", "process substitution");
  assertRejected("ls > >(cat)", "process substitution");
});

test("an unquoted expansion used as an argument is rejected", () => {
  assertRejected("rm $f", "unquoted");
  assertRejected("echo $(ls)", "unquoted");
  assertRejected("cat ${f}", "unquoted");
  assertRejected("echo pre$f", "unquoted");
  assertClean('rm "$f"');
  assertClean('echo "pre$f" "$(ls)"');
});

test("command substitution is checked as a script of its own", () => {
  assertRejected("x=$(eval y)", "eval");
  assertRejected('echo "$(source ./a)"', "source");
  assertRejected("cat <<EOF\n$(eval x)\nEOF\n", "eval");
});

test("every violation is reported, with 1-based line and column", () => {
  const violations = checkBashSubset('x="é"; eval y\nsleep 1 &\n');
  assert.deepEqual(
    violations.map((v) => [v.line, v.column]),
    [[1, 8], [2, 1]],
  );
});

test("a declaration argument that is not a literal name is rejected", () => {
  assertRejected('export "PATH=x"', "hides which variable");
  assertRejected('local -- "IFS=,"', "hides which variable");
  assertRejected("declare 'a[0]=1'", "hides which variable");
  assertRejected('declare "$f" r=PATH', "not a literal word");
  assertRejected("local PATH", "PATH");
  assertRejected('f() { local -- "PATH"; }', "assignment to PATH");
  assertClean("local -r x=1; export y; arr=(1 2)");
});

test("each name a builtin assigns or unsets must be a literal, unprotected identifier", () => {
  assertRejected("read -r -- PATH < ./f", "PATH");
  assertRejected("read -a IFS < ./f", "IFS");
  assertRejected("read -raIFS < ./f", "IFS");
  assertRejected('read -r "$v" < ./f', "not a literal");
  assertRejected("read -r 'a[$(id)]' < ./f", "not a variable name");
  assertRejected("printf -vPATH x", "PATH");
  assertRejected('printf "$fmt" x', "not a literal");
  assertRejected("mapfile -t PATH < ./f", "PATH");
  assertRejected("readarray -s 1 IFS < ./f", "IFS");
  assertRejected("mapfile -Ccb arr < ./f", "callback");
  assertRejected("getopts ab PATH", "PATH");
  assertRejected("unset PATH", "PATH");
  assertRejected("unset -v IFS", "IFS");
  assertRejected("unset -- 'a[$(id)]'", "not a variable name");
  assertClean("read -r -p 'PATH? ' -d '' line < ./f");
  assertClean("read -n 1 -t 5 key < ./f");
  assertClean("mapfile -d '' -n 2 -O 1 arr < ./f");
  assertClean("getopts ab opt");
  assertClean("printf -v out '%s' PATH");
  assertClean("unset tmp other");
  assertRejected("read -r -- -x < ./f", "'-x' is not a variable name");
  assertRejected("unset tmp -x", "'-x' is not a variable name");
});

test("a default assignment to a protected variable is rejected", () => {
  assertRejected('echo "${PATH:=./bin}"', "assignment to PATH");
  assertRejected('echo "${IFS=,}"', "assignment to IFS");
  assertClean('echo "${PATH:-none}"');
  assertRejected('echo "${x:=1}"', "an operator in ${...}");
});

test("an arithmetic assignment to a protected or unnamed variable is rejected", () => {
  assertRejected("((PATH=1))", "assignment to PATH");
  assertRejected("echo $((IFS+=1))", "assignment to IFS");
  assertRejected("let PATH=1", "assignment to PATH");
  assertRejected("((PATH++))", "assignment to PATH");
  assertRejected("((--IFS))", "assignment to IFS");
  assertRejected("((a[$(id)]=1))", "arithmetic evaluates");
  assertClean("((n+=1)); ((i++)); let j=2; echo $((n * i))");
});

test("BASH_CMDS, BASH_ALIASES and EXECIGNORE are protected", () => {
  assertRejected("BASH_CMDS[ls]=./x", "BASH_CMDS");
  assertRejected("BASH_ALIASES=()", "BASH_ALIASES");
  assertRejected("EXECIGNORE=x", "EXECIGNORE");
});

test("indirect expansion and a non-literal -v operand are rejected", () => {
  assertRejected('echo "${!x}"', "indirect");
  assertRejected('[[ -v "$x" ]]', "not a literal");
  assertRejected("[[ -v a[$(id)] ]]", "variable name");
  assertRejected('[ -v "$x" ]', "not a literal");
  assertRejected("test -v 'a[$(id)]'", "not a variable name");
  assertRejected('echo "${!arr[@]}"', "an operator in ${...}");
  assertRejected('echo "${!pre@}"', "an operator in ${...}");
  assertRejected("[[ -v x ]]", "-v is not supported");
  assertRejected("[ -v y ]", "-v is not supported");
  assertRejected("test -v z", "-v is not supported");
});

test("a lone [ is not a glob", () => {
  assertClean('[ -f ./x ]');
  assertClean('if [ "$a" = b ]; then echo ok; fi');
  assertRejected("./[ab] x", "not a literal");
});

test("busybox runs another command, and so does a time binary", () => {
  assertRejected("busybox sh", "busybox runs another command");
  assertRejected("/usr/bin/time ls", "time runs another command");
});

test("columns count code points, not UTF-16 units", () => {
  const violations = checkBashSubset('x="😀"; eval y\n');
  assert.deepEqual(violations.map((v) => [v.line, v.column]), [[1, 8]]);
});

test("a quoted or escaped declaration keyword is rejected", () => {
  assertRejected("\\declare PATH=1", "declaration keyword");
  assertRejected("'let' PATH=1", "declaration keyword");
  assertRejected('"export" IFS=,', "declaration keyword");
  assertRejected("\\typeset x", "declaration keyword");
  assertRejected("\\readonly x", "declaration keyword");
  assertRejected("f() { \\local x; }", "declaration keyword");
  assertClean("declare x=1; let y=2; f() { local z; }");
});

test("arithmetic rejects a word that is quoted, substituted or expanded with an operator", () => {
  assertRejected('let "PATH=7"', "arithmetic evaluates");
  assertRejected('echo $(( "PATH=7" ))', "arithmetic evaluates");
  assertRejected("echo $(( 'PATH=7' ))", "arithmetic evaluates");
  assertRejected('a["PATH=7"]=1', "arithmetic evaluates");
  assertRejected('x=(["PATH=1"]=2)', "arithmetic evaluates");
  assertRejected('echo "${x:"PATH=1"}"', "arithmetic evaluates");
  assertRejected('echo "${a["$k"]}"', "arithmetic evaluates");
  assertRejected('for ((i="PATH=1"; i < 2; i++)); do echo ok; done', "arithmetic evaluates");
  assertRejected("echo $(( $(cat ./n) + 1 ))", "arithmetic evaluates");
  assertRejected("echo $(( ${x:-PATH=1} ))", "arithmetic evaluates");
  assertRejected("echo $(( ${x/a/PATH=1} ))", "arithmetic evaluates");
  assertRejected("((a[$(id)]))", "arithmetic evaluates");
  assertClean('echo $(( $n + ${#a[@]} )) "${a[0]}"');
  assertClean("((arr[i]++)); ((a[i]=1)); for ((i = 0; i < 3; i++)); do echo ok; done");
});

test("an indexed arithmetic assignment checks the array name", () => {
  assertRejected("((BASH_CMDS[ls]=1))", "assignment to BASH_CMDS");
  assertRejected("((BASH_ALIASES[x]++))", "assignment to BASH_ALIASES");
});

test("[[ ]] integer comparisons take an integer, a name or a plain expansion", () => {
  assertRejected('[[ $a -eq "PATH=1" ]]', "integer comparison");
  assertRejected("[[ $(cat ./n) -gt 1 ]]", "integer comparison");
  assertRejected("[[ ${x:-PATH=1} -le 1 ]]", "integer comparison");
  assertRejected("[[ 1 -ne a[$(id)] ]]", "integer comparison");
  assertClean('[[ "$a" -eq 1 ]]; [[ n -ge -2 ]]; [[ "$#" -gt 0 ]]; [[ "${#a[@]}" -lt 3 ]]');
  assertRejected("[[ $# -gt 0 ]]", "a test operand");
});

test("an integer attribute is rejected", () => {
  assertRejected("declare -i x=1", "integer attribute");
  assertRejected("f() { local -ai arr; }", "integer attribute");
  assertRejected("typeset -i n", "integer attribute");
});

test("wait -p names the variable it assigns", () => {
  assertRejected("wait -p PATH", "PATH");
  assertRejected("wait -n -pIFS", "IFS");
  assertClean("wait -n -p pid");
});

test("-v is rejected in a test even where it is not an operator", () => {
  assertRejected('[ "$1" = -v ]', "-v is not supported");
  assertRejected('test "$a" != -v', "-v is not supported");
  assertRejected("[ -v ]", "-v is not supported");
  assertRejected('[ ! -v "$x" ]', "not a literal");
  assertRejected('[ "$a" = b -a -v "$x" ]', "not a literal");
  assertRejected('[ \\( -v "$x" \\) ]', "not a literal");
});

test("unset -f takes a function name, while export -n, declare -f and indexed -v operands are rejected", () => {
  assertRejected("export -n x", "a declaration option other than -r and -x");
  assertClean("unset -f my-fn");
  assertRejected("declare -f my-fn", "a declaration option other than -r and -x");
  assertRejected("[[ -v arr[0] ]]", "-v is not supported");
  assertRejected("[[ -v a['x'] ]]", "not a literal");
});

test("every arithmetic assignment operator bash parses is checked", () => {
  for (const op of ["=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>="]) {
    assertRejected(`((PATH${op}1))`, "assignment to PATH");
  }
});

test("every [[ ]] integer comparison checks its operands", () => {
  for (const op of ["-eq", "-ne", "-le", "-ge", "-lt", "-gt"]) {
    assertRejected(`[[ 1 ${op} "PATH=1" ]]`, "integer comparison");
  }
  assertClean('[[ a == "PATH=1" ]]');
});

test("testing whether a protected variable is set is not an assignment", () => {
  const violations = checkBashSubset("[[ -v PATH ]]; [ -v IFS ]; test -v BASH_ENV");
  assert.deepEqual(violations.map((v) => v.message), Array(3).fill("-v is not supported"));
});

test("only [ drops a closing ], and getopts names one variable", () => {
  assertRejected("test -v ]", "not a variable name");
  assertClean("getopts ab opt -x");
});

test("a bracket expression needs a closing ] that is not its first member", () => {
  assertClean("./[] x");
  assertRejected("./[]] x", "not a literal");
  assertRejected('./x[a"]" x', "not a literal");
  assertClean('ec"ho" ok');
});

test("a named descriptor redirect assigns its variable", () => {
  assertRejected(": {PATH}>/dev/null", "assignment to PATH");
  assertRejected("echo x {LD_PRELOAD}>./f", "assignment to LD_PRELOAD");
  assertRejected(": {a[0]}>./f", "not a variable name");
  assertRejected(": {fd}>./log", "a named descriptor");
  assertClean("echo x 2>/dev/null");
});

test("only -f and -F make declaration names functions, and a quoted assignment is always rejected", () => {
  assertRejected('f() { local +f "IFS=x"; }', "hides which variable");
  assertRejected('typeset +F "PATH=/tmp/x"', "hides which variable");
  assertRejected('export +f "LD_PRELOAD=./x.so"', "hides which variable");
  assertRejected('declare -f "PATH=x"', "hides which variable");
  assertRejected("f() { local +f PATH; }", "assignment to PATH");
});

test("indirect expansion through an array element is rejected", () => {
  assertRejected('echo "${!a[0]}"', "indirect");
  assertRejected('echo "${!a[i]}"', "indirect");
  assertRejected('echo "${!a[0]:-x}"', "indirect");
  assertRejected('echo "${!a[@]}"', "an operator in ${...}");
  assertRejected('echo "${!a[*]}"', "an operator in ${...}");
});

test("history expansion is rejected because bash rewrites each line before parsing it", () => {
  assertRejected("set -H", "history expansion");
  assertRejected("set -eH", "history expansion");
  assertRejected("set -o histexpand", "history expansion");
  assertRejected("set -o history -o histexpand", "history expansion");
  assertRejected("set -o history", "history expansion");
  assertRejected("shopt -os history histexpand", "history expansion");
  assertRejected("shopt -s -o histexpand", "history expansion");
  assertRejected("set +H", "set accepts only");
  assertRejected("set +o histexpand", "set accepts only");
  assertRejected("shopt -s histappend", "shopt is not supported");
});

test("keyword mode is rejected because it turns arguments into assignments", () => {
  assertRejected("set -k", "keyword mode");
  assertRejected("set -ek", "keyword mode");
  assertRejected("set -o keyword", "keyword mode");
  assertRejected("set -eo keyword", "keyword mode");
  assertRejected("shopt -so keyword", "keyword mode");
  assertRejected("shopt -s -o keyword", "keyword mode");
  assertRejected('set -o "$opt"', "not a literal word");
  assertRejected('set "$opt"', "not a literal word");
  assertRejected('shopt -s "$opt"', "not a literal word");
  assertClean("set -euo pipefail");
  assertRejected('set -- a "$b"', "set accepts only");
  assertRejected("set - x", "set accepts only");
  assertRejected("set +e", "set accepts only");
});

test("an extglob pattern holding an expansion is rejected, because the walk cannot see into it", () => {
  assertRejected("[[ a == @(x|$(eval y)) ]]", "extglob");
  assertRejected("[[ a != !(`id`) ]]", "extglob");
  assertRejected('[[ a == +("$(PATH=/tmp; echo)") ]]', "extglob");
  assertRejected("shopt -s extglob; ls ?(x|$(id))", "extglob");
  assertRejected('case a in *(x|$y)) ;; esac', "extglob");
  assertRejected("[[ a == @(x|y) ]]", "a test operand");
  assertRejected("ls ./*(a|b).txt", "an extended glob");
});

test("a translated $\"...\" string is rejected anywhere, because bash expands its translation", () => {
  assertRejected('echo $"hello"', "translat");
  assertRejected('x=$"hi"', "translat");
  assertRejected('cat <<<$"hello"', "translat");
  assertClean("echo $'a\\tb' \"plain\"");
});

test("a format string that cannot start with - ends printf's options", () => {
  assertClean('printf "Hello $name\\n"');
  assertClean('printf "Done: %d files in $dir\\n" 3');
  assertRejected('printf "$fmt" x', "not a literal");
  assertRejected('printf "-$v" x', "not a literal");
});

test("only a plain literal start ends printf's options", () => {
  assertClean('printf "Hi $x" -vPATH');
  assertClean('printf Hello"$x"');
  assertRejected('printf "$(echo -v)PATH" x', "not a literal");
  assertRejected(`printf $'\\x2dv'"$x" y`, "not a literal");
  assertRejected("printf [$x y", "not a literal");
});

test("single quotes in a default or alternative word are literal inside double quotes, so they hide code", () => {
  assertRejected(`echo "\${x:-'$(id)'}"`, "single quotes");
  assertRejected(`echo "\${x:+'\`id\`'}"`, "single quotes");
  const quoteHits = (code: string) =>
    checkBashSubset(code).filter((v) => v.message.includes("single quotes")).length;
  assert.equal(quoteHits(`echo "\${x+'$(id)'}"`), 1, "+");
  assert.equal(quoteHits(`echo "\${x:+'$(id)'}"`), 1, ":+");
  assert.equal(quoteHits(`echo "\${x-'$(id)'}"`), 1, "-");
  assert.equal(quoteHits(`echo "\${x:-'$(id)'}"`), 1, ":-");
  assert.equal(quoteHits(`echo "\${x?'$(id)'}"`), 0, "?");
  assert.equal(quoteHits(`echo "\${x:?'$(id)'}"`), 0, ":?");
  assert.equal(quoteHits(`echo "\${x='$(id)'}"`), 1, "=");
  assert.equal(quoteHits(`echo "\${x:='$(id)'}"`), 1, ":=");
  assertRejected(`y="\${x:-'$(id)'}"`, "single quotes");
  assertRejected(`echo "\${x:-\${y:-'$(id)'}}"`, "single quotes");
  assertRejected(`echo "\${x:-$'$(id)'}"`, "single quotes");
  assertRejected(`cat <<EOF\n\${x:-'$(id)'}\nEOF\n`, "single quotes");
  // Option B rejects these for their operators, but the single-quote check must not fire on them.
  assert.equal(quoteHits(`y=\${x:-'$(id)'}; echo "\${x#'a'}" "\${x%'a'}" "\${x/a/'b'}"`), 0);
  assertClean(`cat <<'EOF'\n\${x:-'$(id)'}\nEOF\n`);
});

test("a backslash-newline in an unquoted heredoc is rejected, because bash may join it into the terminator", () => {
  assertRejected("cat <<EOF\nEO\\\nF\neval x\nEOF\n", "heredoc");
  assertRejected("cat <<-EOF\n\tEO\\\nF\nEOF\n", "heredoc");
  assertRejected("x=$(cat <<EOF\nEO\\\nF\nEOF\n)", "heredoc");
  assertRejected("cat <<EOF\na \\\\\nEOF\n", "only a quoted <<'WORD' heredoc");
  assertRejected("cat <<'EO F'\nEO \\\nF\nEO F\n", "only a quoted <<'WORD' heredoc");
  // The continuation pre-scan cannot see the quotes, so a backslash after a letter is rejected.
  assertRejected("cat <<'EOF'\nEO\\\nF\nEOF\n", "line continuation");
});

test("jobs is rejected, because jobs -x runs a command", () => {
  assertRejected("jobs -x eval x", "jobs");
});

test("a heredoc body line starting with the delimiter is rejected, because inside $(...) bash ends the body there", () => {
  assertRejected("x=$(cat <<'E'\nhi\nE)\neval echo HIT\nE\n)\n", "delimiter");
  assertRejected("x=$(cat <<E\nhi\nE)\neval echo HIT\nE\n)\n", "delimiter");
  assertRejected("x=$(cat <<-'E'\nhi\n\tE )\neval echo HIT\nE\n)\n", "delimiter");
  assertRejected('x="$(cat <<\'E\'\nhi\nE)\neval echo HIT\nE\n)"\n', "delimiter");
  assertRejected("x=$(cat <<'E'\nhi\nE\n)\n", "a heredoc inside $(...)");
  assertClean("cat <<'EOF'\nEO\nF EOF\nEOF\n");
});

test("only a backslash-newline that joins lines into the delimiter is rejected", () => {
  assertRejected("cat >run.sh <<EOF\ndocker run \\\n  -v ./x:/x \\\n  img\nEOF\n", "a line continuation inside quotes");
  assertRejected("cat <<EOF\nE\\\nOF)\nEOF\n", "delimiter");
});

test("an empty heredoc is still checked, because sh-syntax gives it no body word", () => {
  assertClean("cat <<'E'\nE\n");
  assertRejected("cat <<E*\nE*\n", "delimiter");
});

test("consecutive backslash-newlines in an unquoted heredoc all join, as bash joins them", () => {
  assertRejected("cat <<EF\nE\\\n\\\nF\neval echo HIT\nEF\n", "delimiter");
  assertRejected("cat <<EF\nE\\\n\\\n\\\nF\neval echo HIT\nEF\n", "delimiter");
  assertRejected("cat <<EF\nE\\\\\nF\nEF\n", "only a quoted <<'WORD' heredoc");
  // An even run of backslashes does not join, so the next line is still compared on its own.
  assertRejected("x=$(cat <<EOF\na\\\\\\\\\nEOF)\neval echo HIT\nEOF\n)\n", "delimiter");
});

test("a continuation that joins the parser's delimiter line into the body is rejected, because bash then reads on", () => {
  // Round-14 review, bash 5.3.9: sh-syntax strips the tab and ends the body at \tE; bash joins
  // "\tx \\" with "\tE" first, keeps reading, and runs the command substitution on the next line.
  assertRejected("cat <<-E\n\tx \\\n\tE\necho '$(touch S)'\nE\n", "delimiter");
  // Without <<- sh-syntax joins as bash does, so the body runs to the last E and the walk sees touch.
  // Under option B no heredoc body may hold a continuation, and <<- is rejected outright.
  assertRejected("cat <<'E'\nx \\\nE\n", "a line continuation inside quotes");
  assertRejected("cat <<-E\n\tx\n\tE\n", "only a quoted <<'WORD' heredoc");
});

test("backtick command substitution is rejected, because bash strips its backslashes before parsing the inside", () => {
  assertRejected("x=`echo hi`", "backtick");
  assertRejected("x=`echo \"$(cat <<'$E'\nhello\n\\$E)\"; echo \"\n$E\n)\"`", "backtick");
  assertClean("x=$(echo hi)");
});

test("BASH_COMPAT and shopt compat levels are rejected, because they make quotes in ${x/a/'...'} literal", () => {
  assertRejected("BASH_COMPAT=42", "assignment to BASH_COMPAT");
  assertRejected("export BASH_COMPAT=42", "BASH_COMPAT");
  assertRejected("shopt -s compat31", "compat");
  assertRejected("shopt -s compat44", "compat");
  assertRejected("shopt -s nullglob", "shopt is not supported");
});

test("a NUL byte or a carriage return is rejected, because bash and sh-syntax read them differently", () => {
  // bash drops NULs, so a body line \0E) ends the heredoc for bash only.
  assertRejected("x=$(cat <<'E'\nhi\n\0E)\neval echo HIT\nE\n)\n", "NUL");
  // sh-syntax joins a backslash-CR-LF as a continuation; bash does not.
  assertRejected("echo ok \\\r\neval echo HIT\n", "carriage return");
  assertRejected("echo ok\r\n", "carriage return");
  const [cr] = checkBashSubset("echo ok\r\n");
  assert.deepEqual([cr!.line, cr!.column], [1, 8]);
});

test("OPTIND, RANDOM, SRANDOM and HISTCMD take only an integer literal, because bash evaluates their values as arithmetic", () => {
  for (const v of ["OPTIND", "RANDOM", "SRANDOM", "HISTCMD"]) {
    assertRejected(`${v}='a[$(echo HIT >&2)]'`, `${v} evaluates`);
    assertRejected(`${v}="$x"`, `${v} evaluates`);
    assertRejected(`local ${v}=a`, `${v} evaluates`);
    assertRejected(`${v}+=1`, `${v} evaluates`);
    assertRejected(`for ${v} in 'a[$(echo HIT >&2)]'; do :; done`, `${v} evaluates`);
    assertRejected(`read -r ${v} <<<x`, `${v} evaluates`);
    assertRejected(`printf -v ${v} '%s' x`, `${v} evaluates`);
    assertRejected(`mapfile ${v} <x`, `${v} evaluates`);
    assertRejected(`getopts ab ${v}`, `${v} evaluates`);
    assertRejected(`echo "\${${v}:=$x}"`, `${v} evaluates`);
  }
  assertClean("OPTIND=1");
  assertClean("RANDOM=20");
  // bash gives SECONDS the integer attribute when the script first reads it.
  assertRejected(`echo "$SECONDS"\nSECONDS='a[$(echo HIT >&2)]'`, "SECONDS evaluates");
  assertRejected(`start=$SECONDS\nread -r SECONDS <<<x`, "SECONDS evaluates");
  assertClean(`start=$SECONDS\nSECONDS=0`);
  assertClean("local OPTIND=1");
  assertClean("unset RANDOM");
  assertRejected('echo "${OPTIND:=1}"', "an operator in ${...}");
  assertClean("getopts ab opt");
});

test("a declaration value must be a literal not starting with (, because bash re-parses it as an array", () => {
  for (const kw of ["declare", "typeset", "local", "export", "readonly"]) {
    assertRejected(`${kw} -a b='($(echo HIT >&2))'`, "re-parses");
    assertRejected(`${kw} x=$v`, "re-parses");
    assertRejected(`${kw} x=\\(a`, "re-parses");
  }
  // declare, typeset and local re-parse an expanded value when the name is already an array.
  for (const kw of ["declare", "typeset", "local"]) {
    assertRejected(`${kw} x="$v"`, "re-parses");
    assertRejected(`${kw} x+="$v"`, "re-parses");
  }
  // export and readonly never re-parse an expanded value (bash 5.3.9, with the name an indexed or
  // associative array, inside a function, with = and +=), so one quoted expansion is accepted.
  assertClean('export FOO="$HOME"\nreadonly DIR="$(pwd)"\nexport A="${x}" B+="$y"\n');
  assertRejected(`d=(x); declare d='($(echo HIT >&2))'`, "re-parses");
  assertRejected(`declare -A e='([k]=$(echo HIT >&2))'`, "re-parses");
  // The split form assigns a plain string, which bash does not re-parse.
  assertClean(`f() { local x; x="$1"; }`);
  assertClean("local x=1 y='a(b' z=");
  assertClean("arr=(1 2)");
});

test("every BASH name is protected, because BASHPID+= evaluates its value as arithmetic", () => {
  assertRejected(`BASHPID+='a[$(echo HIT >&2)]'`, "assignment to BASHPID");
  assertRejected(`declare BASHPID+=1`, "assignment to BASHPID");
  assertRejected(`BASHPID+=1 true`, "assignment to BASHPID");
  assertRejected(`read -r BASH_XTRACEFD <<<x`, "assignment to BASH_XTRACEFD");
  assertClean(`echo "$BASHPID $BASH_VERSION"`);
});

test("a parser exception other than ParseError is a parse error with a position", () => {
  const violations = checkBashSubset("echo ok\nx=${(echo HIT >&2)}\n");
  assert.equal(violations.length, 1);
  assert.equal(violations[0]!.kind, "unsupported-syntax");
  assert.match(violations[0]!.message, /^parse error/);
  assert.deepEqual([violations[0]!.line, violations[0]!.column], [2, 3]);
  assert.equal(checkBashSubset("${(echo HIT >&2)}")[0]!.column, 1);
});

test("a comment ending in a backslash is rejected, because the parser joins the next line into it and bash runs that line", () => {
  assertRejected('echo a # c \\\neval "echo HIT >&2"', "comment");
  assertRejected('x=1 # c \\\neval "echo HIT >&2"', "comment");
  assertRejected('x=$(echo a # c \\\neval "echo HIT >&2"\n)', "comment");
  assertRejected('  echo a  # c \\\neval "echo HIT >&2"', "comment");
  // An even run of backslashes ends the comment for both.
  assertClean("echo a # c \\\\\necho b");
  assertClean("# just a comment \\");
  assertClean("echo a # see https://example.com/a?b=1\necho b");
});

test("process substitution written inside a pattern, default word or regex is rejected, because bash runs it there", () => {
  for (const op of ["#", "##", "%", "%%", ",", ",,", "^", "^^", "/", "//", "/#", "/%", "+", ":+", "-", ":-", "=", ":=", "?", ":?"]) {
    assertRejected(`y=\${zz${op}<(echo HIT >&2)}`, "process substitution");
    assertRejected(`echo "\${zz${op}>(echo HIT >&2)}"`, "process substitution");
  }
  assertRejected('y=${x/a/<(echo HIT >&2)}', "process substitution");
  assertRejected('[[ a =~ (x|<(echo HIT >&2)) ]]', "process substitution");
  assertRejected('[[ a =~ (>(echo HIT >&2)) ]]', "process substitution");
  assertRejected('x=a\ncat <<EOF\n${x#<(echo HIT >&2)}\nEOF\n', "process substitution");
  assertClean("[[ a =~ (x|y) ]]");
  // Only < and > open one; an = before a group does not.
  assertClean("[[ a =~ x=(y) ]]");
  // Plain text in double quotes or a heredoc body is not expanded for process substitution.
  assertClean('echo "use <(cmd) for diff"');
  assertClean('echo "a$x>(b)"');
  assertRejected("cat <<EOF\nplain <(cmd)\nEOF\n", "only a quoted <<'WORD' heredoc");
  assertClean("cat <<'EOF'\nplain >(cmd)\nEOF\n");
});

test("an extglob pattern holding a process substitution is rejected", () => {
  assertRejected('shopt -s extglob\necho @(x|<(echo HIT >&2))', "extglob");
  assertRejected('shopt -s extglob\necho !(<(echo HIT >&2))', "extglob");
  assertRejected('shopt -s extglob\nls ./@(x|>(echo HIT >&2))', "extglob");
  assertRejected('shopt -s extglob\ncase a in +(>(echo HIT >&2)) ) ;; esac', "extglob");
  assertRejected('shopt -s extglob\n[[ a == @(x|<(echo HIT >&2)) ]]', "extglob");
  assertRejected("echo @(a|b)", "an extended glob");
});

test("an IFS prefix is accepted on read, mapfile and readarray, where it lasts for that one builtin", () => {
  assertClean("IFS= read -r line < ./f");
  assertClean("IFS=, read -r a b < ./f");
  assertClean("IFS=$'\\n' read -r -d '' -a parts < ./f");
  assertClean("while IFS= read -r line; do echo \"$line\"; done < ./f");
  assertClean("IFS= mapfile -t lines < ./f");
  assertClean("IFS= readarray -t lines < ./f");
  assertRejected("IFS= echo x", "assignment to IFS");
  assertRejected("IFS=, cat ./f", "assignment to IFS");
  assertRejected("PATH=./bin read -r x < ./f", "assignment to PATH");
  // A function named read takes the place of the builtin, and in POSIX mode the prefix outlives it.
  assertRejected("read() { echo x; }\nIFS=/ read", "assignment to IFS");
  assertRejected("IFS=/ read\nfunction read { echo x; }", "assignment to IFS");
});

test("a line continuation not preceded by a blank is rejected, because the parser may not join it where bash does", () => {
  const sub = "$\\\n(echo HIT >&2)";
  assertRejected(`echo "${sub}"`, "line continuation");
  assertRejected(`x="${sub}"`, "line continuation");
  assertRejected(`cat <<E\n${sub}\nE\n`, "line continuation");
  assertRejected(`x=$(cat <<E\n${sub}\nE\n)`, "line continuation");
  assertRejected(`cat <<<"${sub}"`, "line continuation");
  assertRejected(`echo x > "./o${sub}"`, "line continuation");
  assertRejected(`echo "\${x:-${sub}}"`, "line continuation");
  assertRejected(`y=\${x#${sub}}`, "line continuation");
  assertRejected(`[[ a =~ ${sub} ]]`, "line continuation");
  assertRejected('echo "$\\\n\\\n(echo HIT >&2)"', "line continuation");
  assertRejected('echo "$\\\n{ echo HIT >&2; }"', "line continuation");
  assertRejected("cat='a[$(echo HIT >&2)]'\n(\\\n(cat))", "line continuation");
  assertRejected('echo "$\\\n[x]"', "line continuation");
  assertRejected("\\\necho x", "line continuation");
  // Only a single backslash after a blank is allowed; a longer odd run ends in a literal one.
  assertRejected('echo a \\\\\\\n(x)', "line continuation");
  assertClean("ls -l \\\n  ./data\n");
  assertClean("echo a \\\n\t./b");
  assertClean("echo a\\\\\necho b");
});

test("a command name starting with a dash is rejected, because bash's time keyword reads -- and -p as its own options and runs the next word", () => {
  assertRejected("time -- eval touch\\ x", "starts with a dash");
  assertRejected('c=touch; time -- "$c" x', "starts with a dash");
  assertRejected('time -p -- bash -c "touch x"', "starts with a dash");
  assertRejected("true && time -- eval x", "starts with a dash");
  assertRejected("if time -- eval x; then :; fi", "starts with a dash");
  assertRejected("x=$(time -- eval x)", "starts with a dash");
  assertRejected("time -p -p eval x", "starts with a dash");
  assertRejected("time ls -l", "time is not supported");
  assertRejected("time -p ls -l", "time is not supported");
});

test("a quoted {...} word straight before a redirect is rejected, because bash takes it as a named descriptor and expands its subscript", () => {
  assertRejected("echo hi {a['b[$(id)]']}>/dev/null", "named descriptor");
  assertRejected("echo hi {a[$'b[$(id)]']}</dev/null", "named descriptor");
  assertRejected("cat {a['b[$(id)]']}<<<x", "named descriptor");
  assertRejected("echo {\"a\"}>./f", "named descriptor");
  assertClean("echo '{a}' >./f");
  assertClean("echo x>./f; echo \"$(ls)\">./g");
});

test("a non-literal word where a test operand starts must be followed by a literal binary operator, because it may be -v", () => {
  assertRejected("op=-v\n[ \"$op\" 'b[$(id)]' ]", "may be an operator");
  assertRejected("[ $'-v' 'b[$(id)]' ]", "may be an operator");
  assertRejected("test $'\\x2dv' 'b[$(id)]'", "may be an operator");
  assertRejected("[ -[v] 'b[$(id)]' ]", "may be an operator");
  assertRejected("[ x -a \"$op\" 'b[$(id)]' ]", "may be an operator");
  // With a non-literal before it, a literal -v may still be where an operand starts.
  assertRejected("[ x \"$a\" -v 'b[$(id)]' ]", "variable name");
  assertClean('[ "$x" ]; [ "$x" = y ]; [ "$a" -eq 1 ]; [ ! "$x" ]');
  // After a literal word that is not ! ( -a or -o, neither -v nor a non-literal word starts an operand.
  assertClean('[ x "$y" z ]');
  assertRejected('[ "$a" = -v -a x ]', "-v is not supported");
});

test("a test operand that may expand to several words is rejected, because the words can carry -v and a subscript together", () => {
  assertRejected("test {-v,'a[$(id)]'}", "several words");
  assertRejected("[ {-v,'a[$(id)]'} ]", "several words");
  assertRejected('set -- -v x\ntest "$@"', "several words");
  assertRejected('b=(-v x)\ntest "${b[@]}"', "several words");
  assertRejected("test x = {y,-o,-v,'a[$(id)]'}", "several words");
  assertRejected("test *", "several words");
  assertRejected('[ "${!b[@]}" ]', "several words");
  assertRejected('[ "${!pre@}" ]', "several words");
  assertRejected('[ "${x:-"$@"}" ]', "several words");
  assertRejected("[ a[$y = x ]", "several words");
  assertRejected("shopt -s extglob\n[ @(-v|a\\[*) ]", "several words");
  assertRejected("shopt -s extglob\ntest !(x) = y", "several words");
  assertRejected("shopt -s extglob\n[ +(-v|a\\[*) ]", "several words");
  assertClean('[ "$x" = y ]; [ "${a[*]}" ]; [ "${a[0]}" = x ]; [ "$#" -eq 0 ]; test "$*"');
  // "$@" inside a command substitution is that command's arguments, and a [ with no ] after it is
  // a plain character.
  assertClean('[ "$(printf %s "$@")" = x ]');
  assertRejected('[ x = a"$y"[ ]', "a test operand");
});

// Option B (plans/hc-41-bash-checker.md, "Narrowed to forms both parsers read alike"): the gate
// accepts a construct only when bash and sh-syntax are known to read it alike.
test("only a quoted <<'WORD' heredoc at the top level of a statement is accepted", () => {
  assertClean("cat <<'EOF'\nplain $x text\nEOF\n");
  assertClean("if true; then\n  cat <<'END_1'\nbody\nEND_1\nfi\n");
  assertRejected("cat <<EOF\ntext\nEOF\n", "only a quoted <<'WORD' heredoc");
  assertRejected("cat <<\"EOF\"\ntext\nEOF\n", "only a quoted <<'WORD' heredoc");
  assertRejected("cat <<\\EOF\ntext\nEOF\n", "only a quoted <<'WORD' heredoc");
  assertRejected("cat <<-'EOF'\n\ttext\n\tEOF\n", "only a quoted <<'WORD' heredoc");
  assertRejected("cat <<'E-F'\ntext\nE-F\n", "only a quoted <<'WORD' heredoc");
  assertRejected("cat <<'E'F\ntext\nEF\n", "only a quoted <<'WORD' heredoc");
  assertRejected("x=$(cat <<'EOF'\ntext\nEOF\n)\n", "a heredoc inside $(...)");
});

test("a line continuation inside quotes, a heredoc or a comment is rejected", () => {
  assertClean("echo a \\\n  b\n");
  assertRejected("echo \"a \\\nb\"\n", "a line continuation inside quotes");
  assertRejected("echo 'a \\\nb'\n", "a line continuation inside quotes");
  assertRejected("cat <<'E'\na \\\nE\n", "a line continuation inside quotes");
});

test("time, extended globs, brace expansion and named descriptors are rejected", () => {
  assertRejected("time ls\n", "time is not supported");
  assertRejected("ls @(a|b)\n", "an extended glob");
  assertRejected("ls !(a)\n", "an extended glob");
  assertRejected("echo {a,b}\n", "brace expansion");
  assertRejected("echo x{1..3}\n", "brace expansion");
  assertRejected("exec {fd}>out\n", "a named descriptor");
  assertRejected("echo hi {fd}>out\n", "a named descriptor");
});

test("shopt is rejected in any form, and set takes only -e, -u, -x and three -o names", () => {
  assertRejected("shopt -s nullglob\n", "shopt is not supported");
  assertRejected("shopt\n", "shopt is not supported");
  assertClean("set -euo pipefail\nset -e\nset -x -u\nset -o errexit -o nounset\nset -eo pipefail -u\n");
  assertRejected("set -f\n", "set accepts only");
  assertRejected("set +e\n", "set accepts only");
  assertRejected("set -o noglob\n", "set accepts only");
  assertRejected("set -- a b\n", "set accepts only");
  assertRejected("set -e x\n", "set accepts only");
  assertRejected("set -o\n", "set accepts only");
});

test("a parameter expansion with an operator is rejected, except ${#x} and a plain ${x:-word}", () => {
  assertClean('echo "$x" "${x}" "$@" "${#x}" "${x:-def}" "${arr[0]}" "${arr[i]}" "${#arr[@]}" "$1"\n');
  assertRejected('echo "${x-def}"\n', "an operator in ${...}");
  assertRejected('echo "${x:+alt}"\n', "an operator in ${...}");
  assertRejected('echo "${x:=v}"\n', "an operator in ${...}");
  assertRejected('echo "${x:?msg}"\n', "an operator in ${...}");
  assertRejected('echo "${x:-"q"}"\n', "an operator in ${...}");
  assertRejected('echo "${x:-$y}"\n', "an operator in ${...}");
  assertRejected('echo "${x:-a\\b}"\n', "an operator in ${...}");
  assertRejected('echo "${x#p}"\n', "an operator in ${...}");
  assertRejected('echo "${x%p}"\n', "an operator in ${...}");
  assertRejected('echo "${x/a/b}"\n', "an operator in ${...}");
  assertRejected('echo "${x:1:2}"\n', "an operator in ${...}");
  assertRejected('echo "${x@Q}"\n', "an operator in ${...}");
  assertRejected('echo "${x^^}"\n', "an operator in ${...}");
  assertRejected('echo "${!x}"\n', "an operator in ${...}");
  assertRejected('echo "${!a[@]}"\n', "an operator in ${...}");
  assertRejected('echo "${!pre@}"\n', "an operator in ${...}");
  assertRejected('echo "${a[i+1]}"\n', "a subscript");
  assertRejected('echo "${a[$i]}"\n', "a subscript");
});

test("test, [ and [[ take literal operators, and operands that are literals or one quoted expansion", () => {
  assertClean('[ -f ./x ]\ntest "$a" = b\n[[ "$a" == b ]]\n[[ -n "$(id -u)" ]]\n[ "$(id -u)" = 0 ]\n');
  assertRejected("[ -v x ]\n", "-v is not supported");
  assertRejected("test -v x\n", "-v is not supported");
  assertRejected("[[ -v x ]]\n", "-v is not supported");
  assertRejected("[[ $a == b ]]\n", "a test operand");
  assertRejected("[[ \"$a\" == b* ]]\n", "a test operand");
  assertRejected("[[ \"$a\" =~ ^a.*$ ]]\n", "a test operand");
  assertRejected("[[ x\"$a\" == b ]]\n", "a test operand");
  assertRejected("[[ \"$a\"x == b ]]\n", "a test operand");
  assertRejected("[ \"x$a\" = b ]\n", "a test operand");
  assertRejected("[ \"$a$b\" = b ]\n", "a test operand");
});

test("a declaration option other than -r and -x is rejected", () => {
  assertClean("local -r a=1\nexport -x b=2\nreadonly c=3\ndeclare -rx d=4\nlocal e\n");
  assertRejected("declare -a a\n", "a declaration option other than -r and -x");
  assertRejected("export -n a\n", "a declaration option other than -r and -x");
  assertRejected("declare +x a\n", "a declaration option other than -r and -x");
  assertRejected("declare -g a=1\n", "a declaration option other than -r and -x");
  assertRejected("declare -f f\n", "a declaration option other than -r and -x");
});

test("each option-B rejection reports only its own finding, at its position, and leaves accepted neighbours clean", () => {
  const found = (code: string) => checkBashSubset(code).map((v) => [v.message, v.line, v.column]);
  // A heredoc body with no continuation is not taken for a joined delimiter.
  assert.deepEqual(found("cat <<E\nx\nE\n"), [["only a quoted <<'WORD' heredoc whose WORD is a plain name is supported", 1, 5]]);
  // The continuation is reported at its backslash.
  assert.deepEqual(found('echo "a \\\nb"\n'), [["a line continuation inside quotes, a heredoc or a comment is not supported", 1, 9]]);
  // An even run of backslashes inside quotes is two literal backslashes, not a continuation.
  assertClean('echo "a\\\\\\\\\nb"\n');
  // A continuation after a quoted word lies outside it.
  assertClean("echo 'a' \\\n  b\n");
  assertClean('echo "${arr[7]}"\n');
  assert.deepEqual(found("[[ -n $a ]]\n"), [["a test operand must be a literal or one quoted expansion", 1, 7]]);
  // set's options end at --, so a later -k is an argument, not keyword mode.
  assert.deepEqual(found("set -- -k\n"), [["set accepts only -e, -u, -x, -o pipefail, -o errexit and -o nounset", 1, 5]]);
  // Under -f the names are functions, which may hold a dash.
  assert.deepEqual(found("declare -f my-fn\n"), [["a declaration option other than -r and -x is not supported", 1, 9]]);
  // A [ at the end of an operand closes no bracket expression, so it is one word.
  assert.deepEqual(found('[ x = a"$y"[ ]\n'), [["a test operand must be a literal or one quoted expansion", 1, 7]]);
  assertRejected('[ "`id -u`" = 0 ]\n', "a test operand");
});

test("bash 5.3 function substitution ${ cmd; } and ${| cmd; } is rejected", () => {
  assertRejected("x=${ echo a; }\n", "function substitution");
  assertRejected('echo "${ echo a; }"\n', "function substitution");
  assertRejected("y=${| REPLY=a; }\n", "function substitution");
  assertClean("x=$(echo a)\n");
});
