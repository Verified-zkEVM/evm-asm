#!/usr/bin/env bash
#
# check-duplication.sh — ADVISORY copy-paste/duplication watch (report R-C6;
# GitClear AI-duplication data). Thin wrapper around `jscpd`.
#
# WHY ADVISORY: duplication is a *leading indicator*, not a defect. The Rule of
# Three (and the steering review's explicit non-goal) says deliberate
# per-opcode / per-fixture boilerplate is cheaper duplicated than behind a
# brittle macro — so the ~516 codegen-*.sh and concrete Program(s).lean trees
# are EXCLUDED in scripts/jscpd.json. The remaining signal is convergent
# proof-tactic/lemma duplication worth a human glance. This gate therefore
# defaults to exit 0 (report only) and "fails only on NEW sprawl": with --gate,
# it fails if the duplicated-line percentage exceeds the calibrated budget in
# scripts/duplication-baseline.txt.
#
# Usage:
#   scripts/check-duplication.sh [paths...]      # advisory; default scripts/ EvmAsm/
#   scripts/check-duplication.sh --gate [paths]  # exit 1 if % > baseline budget
#   scripts/check-duplication.sh --update        # rewrite baseline to current %
#
# Deps: node/npx (jscpd fetched via npx), jq. Skips gracefully (exit 0) if
# jscpd cannot be obtained — never block CI on a missing optional tool.

set -uo pipefail
export LC_ALL=C   # keep the --gate awk float compare locale-stable (dot decimal)

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

CONFIG="scripts/jscpd.json"
BASELINE_FILE="scripts/duplication-baseline.txt"
OUT=".jscpd-report"
MODE="advisory"
PATHS=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --gate) MODE="gate"; shift ;;
    --update) MODE="update"; shift ;;
    *) PATHS+=("$1"); shift ;;
  esac
done
# Default scope is scripts/ ONLY: a full jscpd sweep of the ~2000 .lean files
# exceeds 300s (infeasible per-PR — see R-C6 "keep checks cheap, heavy suites
# nightly"). The shell suite is also where AI copy-paste sprawl is most likely.
# CI runs `scripts/check-duplication.sh scripts/ EvmAsm/` on the nightly/weekly
# cadence with a longer budget.
(( ${#PATHS[@]} == 0 )) && PATHS=(scripts/)

if ! command -v npx >/dev/null 2>&1; then
  echo "check-duplication: npx not found; skipping (advisory)."
  exit 0
fi

echo "check-duplication: running jscpd over ${PATHS[*]} (config $CONFIG)…"
mkdir -p "$OUT"   # the 2>"$OUT/.stderr" redirect below fails if $OUT is absent
                  # (it is gitignored, so it does not exist on a fresh checkout)
# jscpd pinned to an exact version: `jscpd@4` would fetch+run the latest 4.x at
# runtime (arbitrary npm code on a scheduled runner). Bump deliberately.
if ! npx --yes jscpd@4.2.4 --config "$CONFIG" --reporters json --silent "${PATHS[@]}" >/dev/null 2>"$OUT/.stderr"; then
  echo "check-duplication: jscpd unavailable or errored; skipping (advisory)."
  [[ -f "$OUT/.stderr" ]] && sed 's/^/  jscpd: /' "$OUT/.stderr" | tail -5
  exit 0
fi

REPORT="$OUT/jscpd-report.json"
if [[ ! -f "$REPORT" ]]; then
  echo "check-duplication: no report produced; skipping (advisory)."
  exit 0
fi

PCT="$(jq -r '.statistics.total.percentage' "$REPORT" 2>/dev/null || echo 0)"
CLONES="$(jq -r '.statistics.total.clones' "$REPORT" 2>/dev/null || echo 0)"
DUPLINES="$(jq -r '.statistics.total.duplicatedLines' "$REPORT" 2>/dev/null || echo 0)"
echo "  duplicated lines: ${PCT}%  (clones=$CLONES, dup-lines=$DUPLINES)"
echo "  top clones:"
jq -r '.duplicates[:8][] | "    \(.firstFile.name):\(.firstFile.start) <-> \(.secondFile.name):\(.secondFile.start)  (\(.lines) lines)"' "$REPORT" 2>/dev/null || true

BUDGET="$(grep -vE '^\s*#' "$BASELINE_FILE" 2>/dev/null | grep -oE '[0-9.]+' | head -1 || echo "")"

if [[ "$MODE" == "update" ]]; then
  {
    echo "# duplication-baseline.txt — the jscpd duplicated-line % budget consumed"
    echo "# by scripts/check-duplication.sh --gate. Bump deliberately in its own"
    echo "# commit (verifier config). Generated baseline below:"
    echo "$PCT"
  } > "$BASELINE_FILE"
  echo "check-duplication: baseline updated to ${PCT}%."
  exit 0
fi

if [[ "$MODE" == "gate" && -n "$BUDGET" ]]; then
  over="$(awk -v p="$PCT" -v b="$BUDGET" 'BEGIN{print (p>b)?1:0}')"
  if [[ "$over" == "1" ]]; then
    echo "check-duplication (--gate) FAILED: ${PCT}% > budget ${BUDGET}%. New duplication sprawl — extract the convergent clones above, or bump $BASELINE_FILE deliberately." >&2
    exit 1
  fi
  echo "check-duplication: ${PCT}% within budget ${BUDGET}%. OK."
  exit 0
fi

echo "check-duplication: advisory only (exit 0). Budget=${BUDGET:-unset}%. Use --gate after calibration."
exit 0
