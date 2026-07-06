#!/usr/bin/env bash
#
# progress-velocity.sh — read the progress time-series and print deltas plus a
# regression alarm (R-A5, Phase 2 D2).
#
# Consumes the JSONL log produced by scripts/progress-snapshot.sh (one record
# per commit, kept on the `progress-history` orphan branch as history.jsonl).
# Reports the change between the first and last record and, with `--check`,
# exits non-zero if any *monotonic* metric regressed — the DIV-style silent
# `.proven → .partly/.conditional` downgrade that point-in-time PROGRESS.md
# cannot surface.
#
# Status (Phase 2): this is an ADVISORY / on-demand tool plus a post-merge
# signal surfaced by .github/workflows/progress-history.yml. It is NOT yet a
# blocking PR gate — gating belongs with the per-PR scorecard (report R-B1,
# Phase 4), which can fetch this history at PR time. See PLAN.md follow-up.
#
# Robust to schema evolution: a metric absent from the *first* record (e.g. an
# old datapoint predating `conditionalCount`) is reported `n/a` and skipped, not
# treated as a 0→N jump — so a schema bump can't manufacture a false regression
# (or, worse, crash-and-pass).
#
# Deterministic: pure sed/grep over the log. No LLM, no network.
#
# Usage:
#   scripts/progress-velocity.sh [history.jsonl]   # default: ./history.jsonl
#   scripts/progress-velocity.sh --check [file]    # exit 1 if a regression
#
# Monotonic-down-is-bad metrics: provenCount, provenBytes, conformanceCount,
# obligationsDone. (conditional/partial are not monotonic — a `.partly →
# .conditional` promotion legitimately moves counts between buckets.)

set -euo pipefail

CHECK=0
if [[ "${1:-}" == "--check" ]]; then CHECK=1; shift; fi
LOG="${1:-history.jsonl}"

if [[ ! -f "$LOG" ]]; then
  echo "progress-velocity: log not found: $LOG" >&2
  exit 2
fi

# Pull a field from a one-line JSON record (no jq dependency). Both return the
# EMPTY string when the key is absent — never the whole line — so a missing
# field is detectable rather than silently poisoning arithmetic. Exact-key
# match (`"key":`) avoids prefix collisions (notStartedCount vs notStartedBytes).
jnum() { grep -oE "\"$2\":[0-9]+" <<<"$1" | head -1 | grep -oE '[0-9]+$' || true; }
jstr() { grep -oE "\"$2\":\"[^\"]*\"" <<<"$1" | head -1 | sed -E 's/.*:"([^"]*)"/\1/' || true; }

FIRST="$(grep -m1 '^{' "$LOG" || true)"
LAST="$(grep '^{' "$LOG" | tail -1 || true)"

if [[ -z "$FIRST" || -z "$LAST" ]]; then
  echo "progress-velocity: no records in $LOG" >&2
  exit 2
fi

N="$(grep -c '^{' "$LOG")"

echo "## Progress velocity"
echo
echo "Records: ${N}  (\`$(jstr "$FIRST" commit | cut -c1-7)\` → \`$(jstr "$LAST" commit | cut -c1-7)\`)"
echo "EEST fixture tag: \`$(jstr "$LAST" eest_tag)\`"
echo

REGRESSED=0
row() {
  local label="$1" key="$2" monotonic="$3"
  local a b d sign
  a="$(jnum "$FIRST" "$key")"; b="$(jnum "$LAST" "$key")"
  # Guard against a field absent from either endpoint (schema evolution): report
  # n/a instead of doing arithmetic on an empty string (which would otherwise
  # error to stderr yet leave the script exiting 0 — see the adversarial review).
  if [[ ! "$a" =~ ^[0-9]+$ || ! "$b" =~ ^[0-9]+$ ]]; then
    printf -- "- %-22s n/a (field absent in an endpoint record)\n" "$label:"
    return
  fi
  d=$((b - a))
  if (( d >= 0 )); then sign="+${d}"; else sign="${d}"; fi
  local flag=""
  if [[ "$monotonic" == "mono" ]] && (( d < 0 )); then
    flag="  ⚠️ REGRESSION"
    REGRESSED=1
  fi
  printf -- "- %-22s %s → %s (%s)%s\n" "$label:" "$a" "$b" "$sign" "$flag"
}

row "proven (entries)"    provenCount        mono
row "proven (bytes)"      provenBytes        mono
row "conditional"         conditionalCount   free
row "partial"             partialCount       free
row "execSpec"            execSpecCount      free
row "notStarted"          notStartedCount    free
row "obligations done"    obligationsDone    mono
row "obligations blocked" obligationsBlocked free
row "conformance vectors" conformanceCount   mono
echo

if (( REGRESSED )); then
  echo "**A monotonic metric regressed** — a proven/conformance count went DOWN."
  echo "Investigate before merging (this is the DIV-class silent-downgrade alarm)."
  if (( CHECK )); then exit 1; fi
else
  echo "_No monotonic regression._"
fi
