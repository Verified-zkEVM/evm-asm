#!/usr/bin/env bash
# check-fixture-reloc-targets.sh — CI entry point.
#
# Probe-only-fixture callee-name gate (#12145): compares each registered
# fixture's R_RISCV relocation table against the lean RelocTable at the same
# instruction indices. Exits nonzero for a target mismatch, assembly failure,
# missing fixture, or any shortfall from the expected reloc-bearing population.
#
# Cost note: assembles all reloc-bearing fixtures serially (~10 minutes on
# this runner); runs in the codegen lane of check-build-parallel.sh.
#
# Toolchain: requires as + objdump. Accepts riscv64-unknown-elf-* (CI) and
# riscv64-elf-* (Homebrew macOS); see scripts/lib/riscv-tools.sh / #12503.
# Missing toolchain → loud skip (exit 0), never FileNotFoundError mid-lane.
set -euo pipefail
cd "$(dirname "$0")/.."
# shellcheck source=lib/riscv-tools.sh
source "$(dirname "$0")/lib/riscv-tools.sh"
if ! require_riscv_tools_or_skip check-fixture-reloc-targets as objdump; then
  exit 0
fi
exec python3 scripts/check-fixture-reloc-targets.py
