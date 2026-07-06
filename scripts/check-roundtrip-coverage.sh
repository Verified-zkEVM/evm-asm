#!/usr/bin/env bash
#
# check-roundtrip-coverage.sh — regression fence (Phase 3, R-E4) asserting
# that every `Instr` constructor declared in EvmAsm/Rv64/Basic.lean has at
# least one `#guard emitInstr (.<Ctor> …)` example in
# EvmAsm/Codegen/RoundTripTests.lean.
#
# RoundTripTests already covers every shape today (~61 guards vs the current
# constructor set). This is NOT an expansion task: it is a one-way ratchet
# that FAILS THE BUILD when a NEW `Instr` shape lands without a round-trip
# guard (e.g. a future `emitDispatcher*` variant). Cheap drift detection so
# the emitter and its syntax tests cannot silently diverge.
#
# Usage:
#   scripts/check-roundtrip-coverage.sh           # exit 1 on any uncovered ctor
#   scripts/check-roundtrip-coverage.sh --report  # always exit 0; print summary
#
# Pure bash + grep/sed, no external deps — runs in CI and as a pre-commit hook
# without setup. Source-only (no `lake build` needed).

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BASIC="$ROOT/EvmAsm/Rv64/Basic.lean"
TESTS="$ROOT/EvmAsm/Codegen/RoundTripTests.lean"

mode="enforce"
if [[ ${1:-} == "--report" ]]; then
  mode="report"
fi

for f in "$BASIC" "$TESTS"; do
  if [[ ! -f "$f" ]]; then
    echo "check-roundtrip-coverage: missing expected file: $f" >&2
    exit 2
  fi
done

# --- Extract Instr constructor names ---------------------------------------
# The constructors live between `inductive Instr where` and the trailing
# `deriving …` line. Each constructor is a line of the form `  | NAME …`.
# We pull NAME (uppercase RISC-V mnemonics), preserving declaration order.
mapfile -t ctors < <(
  awk '
    /^inductive Instr where/ { ininst=1; next }
    ininst && /^[[:space:]]*deriving/ { exit }
    ininst && /^[[:space:]]*\|/ {
      # strip leading "  | " then take the first whitespace-delimited token
      line=$0
      sub(/^[[:space:]]*\|[[:space:]]*/, "", line)
      split(line, parts, /[[:space:](]/)
      if (parts[1] != "") print parts[1]
    }
  ' "$BASIC"
)

if (( ${#ctors[@]} == 0 )); then
  echo "check-roundtrip-coverage: parsed 0 Instr constructors from $BASIC" >&2
  echo "  (did the inductive layout change? expected 'inductive Instr where' … 'deriving')" >&2
  exit 2
fi

# --- Check each constructor has a guard ------------------------------------
# Match `.<Ctor>` followed by a non-identifier char so that, e.g., `.SLT`
# does not match `.SLTU`/`.SLTI`/`.SLTIU`, `.LB` does not match `.LBU`,
# `.DIV` does not match `.DIVU`, `.MUL` does not match `.MULH*`, etc.
# Lean identifier continuation chars are [A-Za-z0-9_']; anything else
# (space, ')', newline, '.') terminates the constructor token. The opening
# paren is optional so nullary forms (`emitInstr .NOP`) match as well as the
# applied form (`emitInstr (.ADD …)`).
missing=0
covered=0
for ctor in "${ctors[@]}"; do
  if grep -Eq "emitInstr[[:space:]]*\(?\.${ctor}([^A-Za-z0-9_']|\$)" "$TESTS"; then
    covered=$((covered + 1))
  else
    missing=$((missing + 1))
    printf '  FAIL    no round-trip #guard for Instr constructor  .%s\n' "$ctor"
  fi
done

total=${#ctors[@]}

if [[ "$mode" == "report" ]]; then
  printf '\nround-trip coverage: %d/%d constructors guarded, %d missing\n' \
    "$covered" "$total" "$missing"
  exit 0
fi

if (( missing > 0 )); then
  cat >&2 <<EOF

==================================================================
Round-trip coverage fence failed: $missing of $total Instr
constructor(s) have no \`#guard emitInstr (.<Ctor> …)\` example in
EvmAsm/Codegen/RoundTripTests.lean.

Every \`Instr\` shape must have at least one round-trip guard so the
GNU-as emitter cannot silently drift from the syntax we feed
riscv64-elf-as. Add a guard for each constructor listed above, e.g.

    #guard emitInstr (.NEWOP .x5 .x6 .x7) = "newop x5, x6, x7"

(This is a one-way ratchet — see scripts/check-roundtrip-coverage.sh
and report R-E4.)
==================================================================
EOF
  exit 1
fi

printf 'round-trip coverage: all %d Instr constructors guarded.\n' "$total"
