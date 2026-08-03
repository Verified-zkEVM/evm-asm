#!/usr/bin/env bash
# CI gate for GH #11280: GuestAddrs declared starts must match the linker-facts
# TSV for every converted, linked guest entry.
#
# Why a separate check from guest_image_coverage.py --gaps:
#   --gaps walks TSV actual addresses only. On #11277, 222 GuestAddrs entries
#   were stale by +0x2c4 while the TSV was current — CodeReq.extentsOkFrom
#   failed and --gaps stayed green. Ordering/gap coverage is not a declared-
#   versus-actual extent check.
#
# Contract:
#   * declared = def <entry> : Nat := 0x… in EvmAsm/Codegen/GuestAddrs.lean
#   * actual   = scripts/asm-fixtures/symbol-addresses.tsv (stateless_guest .text)
#   * population = converted + linked only (unlinked aliases do not fail)
#   * FAIL tags: DECLARED_START_MISMATCH | DECLARED_MISSING | DECLARED_EXTENT_OVERRUN
#
# No ELF build required (source-only). Wired hard into source-checks — a gate
# nobody has seen fail is indistinguishable from one that cannot; perturb
# evidence lives in the PR body (#11280).
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/guest_image_coverage.py --check-declared-starts
