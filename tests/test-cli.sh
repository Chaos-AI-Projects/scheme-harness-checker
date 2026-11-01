#!/usr/bin/env bash
# test-cli.sh
# Tests for flags handled by src/main.ss.
#
# Run from harness-checker/:
#   PACKRAT=<packrat-extended-path> tests/test-cli.sh
set -u

packrat="$(realpath "${PACKRAT:-$(dirname "$0")/../../../packrat-extended}")"
cd "$(dirname "$0")/.."
libdirs="src:$packrat:$packrat/examples"
pass=0
fail=0

run() {
  out=$(scheme --libdirs "$libdirs" --program src/main.ss "$@" data/minimal-safe.txt data/type-signatures.scm 2>&1)
  rc=$?
}

check() {
  if [ "$2" = 0 ]; then
    pass=$((pass + 1)); echo "  PASS: $1"
  else
    fail=$((fail + 1)); echo "  FAIL: $1"; echo "$out" | sed 's/^/    | /'
  fi
}

has() { echo "$out" | grep -qF -- "$1"; echo $?; }

echo "=== --no-types ==="

run tests/cli/type-error-only.ss
check "type error reported by default" "$(has 'TYPE ERRORS:')"
check "type error alone exits 1 by default" "$([ $rc = 1 ]; echo $?)"

run --no-types tests/cli/type-error-only.ss
check "--no-types suppresses type errors" "$([ "$(has 'TYPE ERRORS:')" = 1 ]; echo $?)"
check "--no-types on a type error alone exits 0" "$([ $rc = 0 ]; echo $?)"

run tests/cli/constraint-error-only.ss
check "constraint error reported by default" "$(has 'CONSTRAINT ERRORS:')"

run --no-types tests/cli/constraint-error-only.ss
check "--no-types suppresses constraint errors" "$([ "$(has 'CONSTRAINT ERRORS:')" = 1 ]; echo $?)"
check "--no-types on a constraint error alone exits 0" "$([ $rc = 0 ]; echo $?)"

run --no-types tests/cli/type-and-termination.ss
check "--no-types still reports termination" "$(has 'no-decreasing-arg')"
check "--no-types counts only termination" "$(echo "$out" | grep -qx '1 violation(s) total.'; echo $?)"
check "--no-types on a termination violation exits 1" "$([ $rc = 1 ]; echo $?)"

run --no-types --no-termination tests/cli/type-and-termination.ss
check "--no-types --no-termination passes" "$([ $rc = 0 ]; echo $?)"

echo
echo "Results: $pass passed, $fail failed"
[ "$fail" = 0 ]
