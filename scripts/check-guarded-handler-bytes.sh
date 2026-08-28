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
# ⛔ Re-emit when the ELF is MISSING *or* OLDER THAN THE EMITTER.
#
# This used to read `if [[ ! -f … ]]`, which is a silent-staleness trap: an ELF
# left over from an earlier tree is happily reused, and the gate then compares
# today's verified Program against yesterday's emitted bytes.  Measured on a
# four-day-old file, this gate reported a wholesale byte shift from `+124`
# onward on `h_ADD` — indistinguishable from a real layout regression, and it
# cost real time to attribute.  A stale ELF can also make the comparison PASS
# when it should fail, which is the worse direction.
#
# The freshness test is the emitter's own mtime rather than an unconditional
# re-emit: `lake exe codegen` relinks whenever the library changes, so a binary
# newer than the ELF means the ELF predates the current tree.  That keeps this
# free in CI — `check-region-map.sh` emits the same file two steps earlier in
# the `codegen` group, so the ELF is already newer than the binary there — while
# fixing the local case, which is the one that was exposed.
GHB_ELF=gen-out/regionmap/stateless_guest.elf
GHB_EXE=.lake/build/bin/codegen
if [[ ! -f "$GHB_ELF" ]]; then
  echo "==> $GHB_ELF missing; emitting"
  scripts/lib/lake-cache-diagnostic.sh lake exe codegen --program stateless_guest \
    --halt linux93 -o gen-out/regionmap/stateless_guest
elif [[ -f "$GHB_EXE" && "$GHB_EXE" -nt "$GHB_ELF" ]]; then
  echo "==> $GHB_ELF is older than $GHB_EXE; re-emitting (stale image would"
  echo "    compare today's Program against an earlier tree's bytes)"
  scripts/lib/lake-cache-diagnostic.sh lake exe codegen --program stateless_guest \
    --halt linux93 -o gen-out/regionmap/stateless_guest
fi
exec python3 scripts/check_guarded_handler_bytes.py
