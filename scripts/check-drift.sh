#!/usr/bin/env bash
#
# check-drift.sh — CI entry point.
#
# Asserts that DRIFT.md (the TCB / "what is NOT proven" ledger) matches
# what `scripts/drift-report.sh --write` would emit. Fails the build on
# drift.
#
# Since #12683 this is the project's ONLY generated-doc drift gate of this
# shape — its sibling check-progress.sh was retired together with the
# committed PROGRESS.md. Two consequences: DRIFT.md must stay committed for
# this gate to exist at all, and it is now also the input the two obligation
# gates parse the rendered `Blocked by` column out of.
#
# Why: DRIFT.md is generated from the kernel-checked registry +
# obligation tracker. If an opcode tier or an obligation status changes
# but DRIFT.md is not regenerated, this catches it.

set -euo pipefail
cd "$(dirname "$0")/.."
exec scripts/drift-report.sh --check
