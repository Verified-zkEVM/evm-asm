#!/usr/bin/env bash
#
# check-correspondence-deps.sh — keep the spec-correspondence harness cheap.
#
# The correspondence checker runs as a per-PR CI gate only because its import
# closure is tiny and Mathlib-free (`EvmAsm.EL.RLP.FullDecode` pulls in exactly
# `Decode` and `Basic`). One casual `import Mathlib.…` — or one `Subject` rooted
# in a heavy tower like `EvmAsm.Evm64` (closure ~1471 modules) — silently turns
# a seconds-long gate into an hour-long one, and the symptom shows up as "CI got
# slow", far from the cause.
#
# This is a pure source scan: it walks `import` lines transitively from the
# executable root and fails if any reached module is Mathlib (or another heavy
# root). No build required, so it stays on the cheap source-checks path.
#
# CALIBRATION — why blocking: the property is invisible in review (an import
# three modules away does it), cheap to check, and expensive to rediscover. The
# registry `EvmAsm/Progress/Correspondence.lean` is deliberately EXEMPT — it
# must import proof modules to witness their theorems, and lives in the heavy
# tier by design. See docs/agents/spec-correspondence.md §9.
#
# Usage:
#   scripts/check-correspondence-deps.sh              # scan
#   scripts/check-correspondence-deps.sh --self-test  # planted-violation check
set -euo pipefail
cd "$(dirname "$0")/.."

ROOT_MODULE="${ROOT_MODULE:-EvmAsm.Tests.Correspondence.Registry}"
FORBIDDEN_PREFIXES=("Mathlib" "EvmAsm.Evm64" "EvmAsm.Codegen" "EvmAsm.Rv64")

# Resolve a module name to its file path.
mod_path() { echo "${1//./\/}.lean"; }

# Transitive closure of imports from a root module, restricted to files that
# exist in-tree (external packages are reported by name and checked by prefix).
closure() {
  local root="$1"
  local -a queue=("$root")
  local -a seen=()
  while [ ${#queue[@]} -gt 0 ]; do
    local m="${queue[0]}"
    queue=("${queue[@]:1}")
    case " ${seen[*]:-} " in *" $m "*) continue ;; esac
    seen+=("$m")
    echo "$m"
    local f
    f="$(mod_path "$m")"
    [ -f "$f" ] || continue
    while IFS= read -r imp; do
      [ -n "$imp" ] && queue+=("$imp")
    done < <(grep -E '^import ' "$f" 2>/dev/null | sed 's/^import  *//' | tr -d '\r')
  done
}

scan() {
  local root="$1" violations=0 total=0
  while IFS= read -r m; do
    total=$((total + 1))
    for p in "${FORBIDDEN_PREFIXES[@]}"; do
      case "$m" in
        "$p"|"$p".*)
          echo "  FORBIDDEN  $m  (reached from $root)"
          violations=$((violations + 1))
          ;;
      esac
    done
  done < <(closure "$root")
  echo "correspondence-deps: $total module(s) in the closure of $root, $violations forbidden."
  return $((violations > 0))
}

if [ "${1:-}" = "--self-test" ]; then
  # Negative control. `EvmAsm.Progress.Correspondence` is the registry — it is
  # SUPPOSED to be heavy (it imports proof modules to witness their theorems),
  # so scanning it must report violations. If it does not, the scanner is not
  # actually reaching into the closure and its green result on the harness
  # means nothing.
  echo "self-test: scanning the registry (expected to be heavy)..."
  if scan "EvmAsm.Progress.Correspondence" >/dev/null 2>&1; then
    echo "self-test: FAILED — the known-heavy registry closure reported clean;"
    echo "  the scanner is not traversing imports, so its green results are vacuous."
    exit 1
  fi
  echo "self-test: OK — the scanner flags a known-heavy closure, so a clean"
  echo "  result on the harness is meaningful."
  exit 0
fi

echo "Scanning the correspondence harness import closure..."
scan "${ROOT_MODULE}"
