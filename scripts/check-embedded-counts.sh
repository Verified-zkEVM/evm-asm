#!/usr/bin/env bash
#
# check-embedded-counts.sh — architecture fitness function (#12129).
#
# Forbids hand-written registry tallies in the obligation matrix's prose.
#
# Why this exists
# ---------------
# `EvmAsm/Progress/Obligations.lean` is the dashboard the end-to-end effort
# steers by. Its `note` fields are free prose, and #11803 / #12103 / #12129
# each found the same decay: a figure written into that prose is correct on
# the day it is written and wrong within days, because the thing it describes
# is edited several times a day.
#
# Obligation 3's note carried a decoder-registry tally that had drifted to
# being wrong on every figure in it. The numbers it restated already exist in
# `EvmAsm/Progress/Routines.lean` as `decide`-checked theorems:
#
#     routineCount_eq, routineProvenCount_eq,
#     routineConditionalCount_eq, routinePartlyCount_eq
#
# Those CANNOT go stale — a wrong number there fails the build. So the fix is
# not "keep the prose in sync" (nobody will) but "do not restate it": point at
# the theorem and let the kernel hold the number.
#
# This is the `infra`-prose half of the staleness problem. Its siblings:
#   * `no_proven_opcode_blockers` (Obligations.lean) — KERNEL-gated, catches a
#     blocker naming an already-proven opcode;
#   * `check-obligation-blockers.sh` — catches a blocker citing a CLOSED issue
#     (advisory: needs network + `gh`).
# This one needs neither network nor the kernel, so it is strict by default.
#
# Scope note: deliberately limited to the count vocabulary the registry owns.
# It does NOT try to validate arbitrary prose — an unfalsifiable goal. It
# forbids exactly the restatements that have actually rotted.
#
# Usage:
#   scripts/check-embedded-counts.sh           # strict (exit 1 on a hit)
#   scripts/check-embedded-counts.sh --warn    # advisory (always exit 0)
#
set -uo pipefail
cd "$(dirname "$0")/.."

WARN=0
[[ "${1:-}" == "--warn" ]] && WARN=1

TARGET="EvmAsm/Progress/Obligations.lean"

if [[ ! -f "$TARGET" ]]; then
  echo "check-embedded-counts: $TARGET not found — skipping." >&2
  exit 0
fi

# The registry count vocabulary. A digit immediately preceding one of these
# words is a restatement of a `decide`-checked theorem.
PATTERN='[0-9]+ (rows|proven|conditional|partly)\b'

hits="$(grep -nE "$PATTERN" "$TARGET" || true)"

if [[ -z "$hits" ]]; then
  echo "check-embedded-counts: OK — no hand-written registry tallies in $TARGET."
  exit 0
fi

count="$(printf '%s\n' "$hits" | wc -l | tr -d ' ')"
echo "check-embedded-counts: $count embedded registry count(s) in $TARGET:" >&2
printf '%s\n' "$hits" | sed 's/^/  ✗  /' >&2

cat >&2 <<'EOF'

A registry tally written into obligation prose is correct on the day it is
written and wrong within days. The numbers already exist as `decide`-checked
theorems in `EvmAsm/Progress/Routines.lean`:

    routineCount_eq  routineProvenCount_eq
    routineConditionalCount_eq  routinePartlyCount_eq

Cite those by name instead of restating their values. A wrong number there
fails the build; a wrong number in prose fails nothing and misleads a reader.
EOF

[[ $WARN -eq 1 ]] && exit 0
exit 1
