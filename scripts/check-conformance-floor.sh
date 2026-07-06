#!/usr/bin/env bash
#
# check-conformance-floor.sh — monotonic ratchet on the kernel-checked
# conformance-vector count.
#
# Why: `EvmAsm/EL/Conformance/All.lean` proves `allConformanceVectorCount
# = N` (kernel-checked, N=66 at time of writing). That theorem guarantees
# the vectors *exist and pass*, but nothing stops a PR from silently
# DELETING vectors (lowering N) while keeping a green build. This gate
# pins a floor in scripts/conformance-baseline.txt and fails if the
# current count drops below it — a one-way ratchet. Raise the floor as
# coverage grows (the script tells you when, or use --write).
#
# This is the cheap, always-available half of the conformance
# non-regression story (R-C3). The heavier EEST `--min-full` gate
# (codegen-eest-stateless-check.sh) needs ziskemu + fixtures and belongs
# in a dedicated workflow; see scripts/eest-fixture-tag.txt.
#
# Usage:
#   scripts/check-conformance-floor.sh          # exit 1 if count < floor
#   scripts/check-conformance-floor.sh --write   # set floor = current count
#
# POSIX/bash; deps: grep.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

ALL_LEAN="EvmAsm/EL/Conformance/All.lean"
BASELINE_FILE="scripts/conformance-baseline.txt"

# Pull the kernel-checked literal from the theorem statement.
CURRENT="$(grep -oE 'allConformanceVectorCount = [0-9]+' "$ALL_LEAN" \
  | head -1 | grep -oE '[0-9]+' || true)"

if [[ -z "${CURRENT:-}" ]]; then
  echo "check-conformance-floor: could not read allConformanceVectorCount from $ALL_LEAN" >&2
  exit 1
fi

if [[ "${1:-}" == "--write" ]]; then
  printf '%s\n' "$CURRENT" > "$BASELINE_FILE"
  echo "check-conformance-floor: set floor = $CURRENT in $BASELINE_FILE"
  exit 0
fi

if [[ ! -f "$BASELINE_FILE" ]]; then
  echo "check-conformance-floor: missing $BASELINE_FILE (run with --write to seed it)" >&2
  exit 1
fi
FLOOR="$(tr -dc '0-9' < "$BASELINE_FILE")"

if (( CURRENT < FLOOR )); then
  cat >&2 <<EOF
==================================================================
check-conformance-floor FAILED: conformance vectors regressed.
  current allConformanceVectorCount = $CURRENT
  baseline floor ($BASELINE_FILE)     = $FLOOR

Conformance vectors must not decrease. If you removed a vector
deliberately, justify it in review and lower the floor with
  scripts/check-conformance-floor.sh --write
==================================================================
EOF
  exit 1
fi

if (( CURRENT > FLOOR )); then
  echo "check-conformance-floor: OK — count $CURRENT > floor $FLOOR. Consider raising the floor:"
  echo "  scripts/check-conformance-floor.sh --write"
  exit 0
fi

echo "check-conformance-floor: OK — count $CURRENT == floor $FLOOR."
