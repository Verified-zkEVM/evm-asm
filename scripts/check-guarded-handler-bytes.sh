#!/usr/bin/env bash
# CI byte-tie drift guard for bead evm-asm-vgyg9 (= 4ch8f.49.a): the verified
# guarded-handler Program (Codegen/Proofs/GuardedHandlerSpecs.lean) must be
# byte-identical to the EMITTED h_ADD subroutine at the address the dispatch
# table uses (symbol-addresses.tsv, itself ELF-drift-guarded by
# check-region-map.sh). See scripts/check_guarded_handler_bytes.py for the
# mechanism. Requires riscv64-unknown-elf-{as,objcopy,readelf} and a built
# project (the render runs the real Lean elaborator).
set -euo pipefail
cd "$(dirname "$0")/.."

if [[ "${EVMASM_BUILD_LOCK_HELD:-0}" != 1 ]]; then
  exec scripts/lib/worktree-build-lock.sh "$0" "$@"
fi

if ! command -v riscv64-unknown-elf-as >/dev/null 2>&1 \
   && ! command -v riscv64-elf-as >/dev/null 2>&1; then
  echo "check-guarded-handler-bytes: no riscv64-{unknown-,}elf-as found; skipping (install to enable)"
  exit 0
fi
if [[ ! -f gen-out/regionmap/stateless_guest.elf ]]; then
  echo "==> gen-out/regionmap/stateless_guest.elf missing; emitting"
  lake exe codegen --program stateless_guest --halt linux93 -o gen-out/regionmap/stateless_guest
fi
exec python3 scripts/check_guarded_handler_bytes.py
