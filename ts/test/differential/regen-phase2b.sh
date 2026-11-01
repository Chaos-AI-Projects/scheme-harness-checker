#!/usr/bin/env bash
# Regenerates phase2b.corpus.txt, phase2b.oracle.txt, rename.oracle.txt and check.oracle.txt from
# test-termination.ss with Chez.
# Each program runs in its own process under a memory cap and a timeout: on 2026-11-01 one
# unbounded pass over the corpus hit a cyclic datum, grew to ~14.6GB and stalled the host for hours.
#   PACKRAT=<packrat-extended-path> ts/test/differential/regen-phase2b.sh
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
tests="$here/../../../tests"
packrat="$(realpath "${PACKRAT:-$here/../../../../../packrat-extended}")"
libdirs="../src:$packrat:$packrat/examples"
cd "$tests"
( ulimit -v 3000000; timeout 120 scheme --libdirs "$libdirs" --program "$here/corpus.ss" test-termination.ss ) > "$here/phase2b.corpus.txt"
one="$(mktemp)"
trap 'rm -f "$one"' EXIT
oracle() { # driver output
  : > "$2"
  while IFS= read -r line; do
    printf '%s\n' "$line" > "$one"
    rc=0
    out="$( ulimit -v 3000000; timeout 15 scheme --libdirs "$libdirs" --program "$here/$1" "$one" 2>/dev/null )" || rc=$?
    if [ "$rc" -ne 0 ] || [ -z "$out" ]; then echo "(skipped $rc)"; else printf '%s\n' "$out"; fi >> "$2"
  done < "$here/phase2b.corpus.txt"
}
oracle phase2b.ss "$here/phase2b.oracle.txt"
oracle rename.ss "$here/rename.oracle.txt"
oracle check.ss "$here/check.oracle.txt"
