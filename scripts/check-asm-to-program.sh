#!/usr/bin/env bash
# CI drift guard for bead evm-asm-4ch8f.9 asm-string -> Program conversions.
#
# For every function recorded in scripts/asm-fixtures/MANIFEST.tsv, regenerate
# the Program + def + rfl theorem + #guards from the saved original asm fixture
# and confirm (a) the fixture still assembles .text-identically under
# `emitProgram`, and (b) the generated Lean block is present verbatim in its
# checked-in file. Any divergence means a hand-edit drifted the emitted string
# away from the mechanically-derived, byte-identity-checked form.
#
# Requires riscv64-unknown-elf-as / -objcopy on PATH (same as the guest build).
set -euo pipefail
cd "$(dirname "$0")/.."
if ! command -v riscv64-unknown-elf-as >/dev/null 2>&1; then
  echo "check-asm-to-program: riscv64-unknown-elf-as not found; skipping (install to enable)"
  exit 0
fi
exec python3 scripts/asm_to_program.py check-all
