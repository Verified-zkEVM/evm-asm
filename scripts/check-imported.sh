#!/usr/bin/env bash
#
# check-imported.sh — fail if any EvmAsm/**/*.lean file was not built
# (i.e. is not transitively reachable from EvmAsm.lean root via `import`).
#
# Tracks issue #1209: orphaned files compile only by accident (e.g.
# direct `lake build EvmAsm.X.Y`) and silently rot when the default
# `lake build` doesn't touch them.
#
# Approach: count `.lean` source files under `EvmAsm/` and compare to
# the number of `.olean` artifacts under `.lake/build/lib/lean/EvmAsm/`.
# If a `.lean` has no matching `.olean`, it is orphaned. Runs AFTER
# `lake build`, so it uses Lean's own import resolution (no in-house
# regex parser) and requires no changes to the existing `lake build`
# output.
#
# Usage:
#   scripts/check-imported.sh           # exit 1 on any orphan
#   scripts/check-imported.sh --report  # always exit 0; print summary
#
# POSIX bash, no external deps. Must run after `lake build` so that the
# olean artifacts are present.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

mode="enforce"
if [[ ${1:-} == "--report" ]]; then
  mode="report"
fi

LEAN_ROOT="EvmAsm"
OLEAN_ROOT=".lake/build/lib/lean/EvmAsm"

if [[ ! -d "$OLEAN_ROOT" ]]; then
  echo "check-imported.sh: $OLEAN_ROOT not found — run \`lake build\` first" >&2
  exit 2
fi

# Build sorted lists of relative module paths (without extension).
mapfile -t lean_files < <(find "$LEAN_ROOT" -name '*.lean' -type f \
  | sed -E "s|^$LEAN_ROOT/||; s|\.lean\$||" | LC_ALL=C sort)
mapfile -t olean_files < <(find "$OLEAN_ROOT" -name '*.olean' -type f \
  | sed -E "s|^$OLEAN_ROOT/||; s|\.olean\$||" | LC_ALL=C sort)

# Orphans = .lean source files with no corresponding .olean.
mapfile -t orphans < <(comm -23 \
  <(printf '%s\n' "${lean_files[@]}") \
  <(printf '%s\n' "${olean_files[@]}"))

lean_count=${#lean_files[@]}
olean_count=${#olean_files[@]}
orphan_count=${#orphans[@]}

if [[ "$mode" == "report" ]]; then
  printf 'lean source files: %d\n' "$lean_count"
  printf 'olean artifacts:   %d\n' "$olean_count"
  printf 'orphaned sources:  %d\n' "$orphan_count"
  if (( orphan_count > 0 )); then
    printf '\nOrphans:\n'
    for o in "${orphans[@]}"; do
      printf '  %s/%s.lean\n' "$LEAN_ROOT" "$o"
    done
  fi
  exit 0
fi

if (( orphan_count > 0 )); then
  cat >&2 <<EOF

==================================================================
Import-coverage guardrail failed: $orphan_count orphaned source file(s).

These .lean files exist under $LEAN_ROOT/ but have no corresponding
.olean artifact under $OLEAN_ROOT/, meaning they are NOT reachable
from the $LEAN_ROOT.lean root via \`import\`.

Orphans:
EOF
  for o in "${orphans[@]}"; do
    printf '  %s/%s.lean\n' "$LEAN_ROOT" "$o" >&2
  done
  cat >&2 <<EOF

To fix, either:
  - add the file's module to the import chain reachable from $LEAN_ROOT.lean
    (e.g. via a sub-umbrella like $LEAN_ROOT/Rv64.lean), or
  - delete the file if it is truly dead.
==================================================================
EOF
  exit 1
fi

exit 0
