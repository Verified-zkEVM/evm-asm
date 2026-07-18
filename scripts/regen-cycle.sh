#!/usr/bin/env bash
# regen-cycle.sh — rebuild + guest layout regen + offset-aware SAsm literal
# remap + rebuild, converging in up to 3 remap passes (later waves of drifted
# files only surface once their import prerequisites build).
# Session helper for the v0.6.0 migration (evm-asm-0w05f).
set -uo pipefail
cd "$(dirname "$0")/.."
S="${REGEN_SCRATCH:-/tmp/claude-1000/-home-zksecurity-evm-asm2/e32e8676-b919-44c3-8483-c15720533cbd/scratchpad}"
git show HEAD:scripts/asm-fixtures/symbol-addresses.tsv > "$S/old-symbols.tsv"
lake build 2>&1 | tail -1
python3 scripts/gen-symbol-addresses.py --build stateless_guest 2>&1 | tail -1
python3 scripts/asm_to_program.py guest-addrs 2>&1 | tail -1
python3 scripts/guest_image_coverage.py --emit-lean 2>&1 | tail -1
: > "$S/remap-done.txt"
for pass in 1 2 3; do
  lake build 2>&1 | grep '^error: EvmAsm/' | grep -oE 'EvmAsm/Codegen/Programs/[A-Za-z0-9]+\.lean' | sort -u > "$S/failpass.txt" || true
  if [ ! -s "$S/failpass.txt" ]; then echo "REGEN_CLEAN pass=$pass"; exit 0; fi
  # never remap the same file twice within a cycle (double-remap corrupts)
  comm -23 "$S/failpass.txt" <(sort "$S/remap-done.txt") > "$S/todo.txt"
  echo "pass $pass: $(wc -l < "$S/failpass.txt") failing, $(wc -l < "$S/todo.txt") to remap"
  [ -s "$S/todo.txt" ] || break
  python3 "$S/remap_sasm.py" "$S/old-symbols.tsv" scripts/asm-fixtures/symbol-addresses.tsv $(cat "$S/todo.txt") | tail -2
  cat "$S/todo.txt" >> "$S/remap-done.txt"
done
lake build 2>&1 | grep -cE '^✖'
