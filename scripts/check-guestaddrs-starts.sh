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
# GH #12623 second pass: --check-declared-data extends the same
# declared-vs-actual contract to every NON-.text (data-cell) symbol with a
# GuestAddrs declaration (.bss/.data/.state_gas_diag/.sszscratch; FAIL tags
# DECLARED_DATA_MISMATCH | DECLARED_DATA_MISSING). #11280 covered .text only;
# 1823 .bss rows — two thirds of the linker facts — had no tie.
#
# No ELF build required (source-only). Wired hard into source-checks — a gate
# nobody has seen fail is indistinguishable from one that cannot; perturb
# evidence lives in the PR body (#11280, #12623).
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/guest_image_coverage.py --check-declared-starts
exec python3 scripts/guest_image_coverage.py --check-declared-data
