#!/usr/bin/env bash
#
# churn-report.sh — ADVISORY leading-indicator report on code churn (report
# R-C6; GitClear AI-churn data; CodeScene hotspots). Pure `git log`, no deps.
#
# Two signals, both purely informational (this script NEVER fails a build):
#
#   1. Top-churn files per window — files touched in the most commits over the
#      last N days. Sustained high churn on a .lean/scripts file is a hotspot:
#      either genuinely central, or thrashing. Worth a human glance, not a gate.
#
#   2. Short-lived churn — lines added then deleted again within ~SHORTLIVE
#      days. High short-lived churn is the GitClear "AI copy-paste then revert"
#      signature. Approximated cheaply as files that were *added* and later
#      *deleted* (or churned in both directions) inside the window.
#
# Deliberately advisory: churn is noisy and context-dependent (a refactor wave
# is healthy churn). Promote to a gate only after a threshold is calibrated.
#
# Usage:
#   scripts/churn-report.sh                  # last 90 days, top 20
#   scripts/churn-report.sh --days 30 --top 10
#   scripts/churn-report.sh --since <date>   # explicit lower bound
#
# POSIX/bash; deps: git, awk, sort.

set -uo pipefail
export LC_ALL=C

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

DAYS=90
TOP=20
SINCE=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --days) DAYS="$2"; shift 2 ;;
    --top) TOP="$2"; shift 2 ;;
    --since) SINCE="$2"; shift 2 ;;
    *) echo "usage: $0 [--days N] [--top N] [--since <date>]" >&2; exit 2 ;;
  esac
done
# Validate numeric args (these feed `head -n` and `git --since`); a bad value
# otherwise leaks a cryptic `head: invalid number` or a misleading window.
[[ "$DAYS" =~ ^[0-9]+$ ]] || { echo "churn-report: --days must be a non-negative integer (got '$DAYS')" >&2; exit 2; }
[[ "$TOP"  =~ ^[0-9]+$ ]] || { echo "churn-report: --top must be a non-negative integer (got '$TOP')" >&2; exit 2; }
[[ -z "$SINCE" ]] && SINCE="${DAYS} days ago"

# restrict to the surfaces we care about: Lean sources + the script suite
pathspec=(-- 'EvmAsm/***.lean' 'scripts/***')

echo "=================================================================="
echo " churn-report (ADVISORY) — since: $SINCE"
echo "=================================================================="

# ---- 1. top-churn files (commit-touch count) --------------------------
echo
echo "== Top $TOP churn files (commit-touch count) =="
git log --since="$SINCE" --no-merges --name-only --pretty=format: "${pathspec[@]}" 2>/dev/null \
  | grep -E '\.(lean|sh|py|json|txt)$' \
  | sort | uniq -c | sort -rn | head -n "$TOP" \
  | awk '{ printf "  %4d  %s\n", $1, $2 }'

# ---- 2. churn volume (lines added/removed) by file --------------------
echo
echo "== Top $TOP files by churned lines (added+removed) =="
git log --since="$SINCE" --no-merges --numstat --pretty=format: "${pathspec[@]}" 2>/dev/null \
  | awk 'NF==3 && $1!="-" && $2!="-" {
           add[$3]+=$1; del[$3]+=$2 }
         END { for (f in add) printf "%d\t%d\t%d\t%s\n", add[f]+del[f], add[f], del[f], f }' \
  | sort -rn | head -n "$TOP" \
  | awk -F'\t' '{ printf "  churn=%-7d (+%-6d -%-6d)  %s\n", $1, $2, $3, $4 }'

# ---- 3. short-lived churn (added then deleted in window) --------------
echo
echo "== Short-lived files (added AND deleted within window — possible thrash) =="
added=$(git log --since="$SINCE" --no-merges --diff-filter=A --name-only --pretty=format: "${pathspec[@]}" 2>/dev/null | grep -E '\.(lean|sh|py)$' | sort -u)
deleted=$(git log --since="$SINCE" --no-merges --diff-filter=D --name-only --pretty=format: "${pathspec[@]}" 2>/dev/null | grep -E '\.(lean|sh|py)$' | sort -u)
# `grep -c .` already prints 0 on no match (and exits 1, harmless without set -e).
# Do NOT add `|| echo 0` — that would append a SECOND "0", making `shortlived`
# the two-line string "0\n0" and breaking the (( )) test below.
shortlived=$(comm -12 <(printf '%s\n' "$added") <(printf '%s\n' "$deleted") 2>/dev/null | grep -c .)
if (( shortlived > 0 )); then
  echo "  $shortlived file(s) created AND removed within the window (refactor churn or thrash); first $TOP:"
  comm -12 <(printf '%s\n' "$added") <(printf '%s\n' "$deleted") 2>/dev/null | head -n "$TOP" | sed 's/^/    /'
else
  echo "  (none — no file both created and removed within the window)"
fi

echo
echo "churn-report: advisory only (exit 0). No threshold gate — see R-C6."
exit 0
