#!/usr/bin/env bash
# Regenerates ts/src/termination/chezenv.ts from Chez, capped like regen-phase2b.sh.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
( ulimit -v 3000000; timeout 60 scheme --program "$here/chezenv.ss" ) > "$here/../../src/termination/chezenv.ts"
