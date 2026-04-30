#!/usr/bin/env bash
#
# check-unbounded-cps.sh — fail if production Lean files still expose or use
# the unbounded CPS spec API after the step-bound migration.
#
# Usage:
#   scripts/check-unbounded-cps.sh
#
# Historical prose may mention the old names only when the line is explicitly
# marked with:
#   historical-step-bound-migration

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PATTERN='(^|[^A-Za-z0-9_])(cpsTriple|cpsBranch|cpsNBranch|cpsHaltTriple|to_cpsTriple|to_cpsBranch|to_cpsNBranch|to_cpsHaltTriple)([^A-Za-z0-9_]|$)'
ALLOW_MARKER='historical-step-bound-migration'

mapfile -t matches < <(
  cd "$ROOT"
  rg -n "$PATTERN" EvmAsm/Rv64 EvmAsm/Evm64 \
    | rg -v "$ALLOW_MARKER" || true
)

if (( ${#matches[@]} > 0 )); then
  cat >&2 <<'EOF'
Unbounded CPS guard failed.

Production specs must use the step-upper-bound aware APIs:
  cpsTripleWithin, cpsBranchWithin, cpsNBranchWithin, cpsHaltTripleWithin

Remove unbounded compatibility wrappers/projections and update callers. If a
line is historical prose, mark that exact line with:
  historical-step-bound-migration

Remaining matches:
EOF
  printf '%s\n' "${matches[@]}" >&2
  exit 1
fi

printf 'unbounded CPS guard: no production matches found.\n'
