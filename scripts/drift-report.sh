#!/usr/bin/env bash
#
# drift-report.sh — regenerate DRIFT.md, the TCB / "what is NOT proven"
# ledger, from the kernel-checked registry (EvmAsm/Progress.lean) and the
# obligation tracker (EvmAsm/Progress/Obligations.lean).
#
# Modes:
#   scripts/drift-report.sh --write   # regenerate DRIFT.md
#   scripts/drift-report.sh --check   # exit non-zero if DRIFT.md differs
#                                     # from the regenerated output (CI gate)
#
# Design: the whole body is emitted by `lake exe progress-report drift`
# (Lean-side, kernel-checked, deterministic — no date/SHA), so the drift
# comparison is a plain diff. Mirrors scripts/progress-report.sh.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

MODE="${1:-}"
case "$MODE" in
  --write|--check) ;;
  *) echo "usage: $0 --write | --check" >&2; exit 2 ;;
esac

TMP="$(mktemp)"
trap 'rm -f "$TMP"' EXIT

# GH #12652: force-build the report module and UNSUPPRESS stderr via the
# shared helper (scripts/lib/report-fresh-lean.sh, the check-axioms GH
# #10601 pattern).  Previously a cache-stale `lake exe progress-report`
# could emit last week's figures, exit zero, and land them in DRIFT.md
# with `--write` — the follow-up `--check` then diffed two copies of the
# same stale text and passed.  The helper exits non-zero on a failed
# build, a failed run, or a suspiciously empty report, and writes stdout
# to $TMP byte-exactly (plain redirect — command substitution strips
# trailing newlines and would silently change the --check diff).
source "$ROOT/scripts/lib/report-fresh-lean.sh"
report_fresh_lean "$TMP" progress-report drift

case "$MODE" in
  --write)
    mv "$TMP" DRIFT.md
    trap - EXIT
    echo "Wrote DRIFT.md"
    ;;
  --check)
    if [[ ! -f DRIFT.md ]]; then
      echo "DRIFT.md missing; run scripts/drift-report.sh --write" >&2
      exit 1
    fi
    if ! diff -u DRIFT.md "$TMP"; then
      cat >&2 <<'EOF2'

DRIFT.md is out of date relative to the kernel-checked registry +
obligation tracker. To regenerate:

    scripts/drift-report.sh --write

then commit the result.
EOF2
      exit 1
    fi
    ;;
esac
