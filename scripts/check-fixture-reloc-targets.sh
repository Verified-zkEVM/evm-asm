#!/usr/bin/env bash
# check-fixture-reloc-targets.sh — CI entry point.
#
# Probe-only-fixture callee-name gate (#12145): compares each registered
# fixture's R_RISCV relocation table against the lean RelocTable at the same
# instruction indices. Exits nonzero when a fixture's UND-class relocation
# names a different symbol than the lean entry at that index.
#
# Cost note: assembles all reloc-bearing fixtures serially (~10 minutes on
# this runner); runs in the codegen lane of check-build-parallel.sh.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/check-fixture-reloc-targets.py
