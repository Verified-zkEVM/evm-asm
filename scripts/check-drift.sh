#!/usr/bin/env bash
#
# check-drift.sh — CI entry point.
#
# Asserts that DRIFT.md (the TCB / "what is NOT proven" ledger) matches
# what `scripts/drift-report.sh --write` would emit. Fails the build on
# drift. Same shape as scripts/check-progress.sh.
#
# Why: DRIFT.md is generated from the kernel-checked registry +
# obligation tracker. If an opcode tier or an obligation status changes
# but DRIFT.md is not regenerated, this catches it.

set -euo pipefail
cd "$(dirname "$0")/.."
exec scripts/drift-report.sh --check
