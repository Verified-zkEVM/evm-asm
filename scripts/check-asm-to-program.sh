#!/usr/bin/env bash
# CI drift guard for bead evm-asm-4ch8f.9 asm-string -> Program conversions.
#
# For every function recorded in scripts/asm-fixtures/MANIFEST.tsv, confirm:
#   (a) the ACTUAL Lean-rendered string (emitProgram <prog>, obtained from the
#       real elaborator via `lake env lean --run`) assembles .text-identically
#       to the saved original-asm fixture -- the authoritative binary-identity
#       check, exercising Lean's emitInstr (not the Python mirror);
#   (b) the generated Lean block is present verbatim in its checked-in file
#       (source drift guard);
#   (c) the offline py_emit render still agrees (fast mirror cross-check).
#   (d) each MANIFEST path declares its Function, unless it is the explicit
#       GH #10753 bridge/leaf shape.  This catches a file-size split that moves
#       a Function to an arbitrary sibling while leaving the manifest stale.
# Any divergence means a hand-edit or an emitInstr/py_emit split drifted the
# emitted guest text away from the byte-identity-checked form.
#
# Refactor-inertness recipe: when comparing two complete guest ELFs, give both
# emits the same output basename.  The ELF records that basename, so distinct
# names can make otherwise byte-identical assembly and objects appear to differ.
#
# Requires a RISC-V `as`/`objcopy` on PATH AND a built project (`lake build`),
# since the authoritative check runs the Lean elaborator.  Both triple
# spellings are accepted: CI installs `binutils-riscv64-unknown-elf`, Homebrew
# ships the identical GNU binutils as `riscv64-elf-*`.  Probing only the former
# made this gate skip on every macOS checkout — green, having checked nothing.
set -euo pipefail
cd "$(dirname "$0")/.."
# GH #12204 step 2. Pure-Python, no toolchain needed — so it runs ABOVE the
# assembler probe below. A check that can only skip is not a check, and the
# skip path here is exactly what hid the pre-#11043 breakage on macOS.
python3 scripts/asm_to_program.py numlabel-self-test
if ! command -v riscv64-unknown-elf-as >/dev/null 2>&1 \
   && ! command -v riscv64-elf-as >/dev/null 2>&1; then
  echo "check-asm-to-program: no riscv64-{unknown-,}elf-as found; skipping (install to enable)"
  exit 0
fi
exec python3 scripts/asm_to_program.py check-all
