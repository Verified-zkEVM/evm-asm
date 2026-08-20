#!/usr/bin/env bash
#
# progress-snapshot.sh — emit ONE JSON Lines record of the current
# kernel-checked progress counts to stdout (R-A5, Phase 2 D2).
#
# The record is appended (by .github/workflows/progress-history.yml) to
# `history.jsonl` on the long-lived `progress-history` orphan branch, giving a
# per-commit time series. `scripts/progress-velocity.sh` reads that log to
# print deltas and a regression alarm — so a silent `.proven → .partly` (the
# DIV-class downgrade) shows up as a negative velocity, not buried in a merge.
#
# Deterministic: no LLM, pure git + lake + awk. Re-running at the same commit
# with the same fixture tag yields an identical record (modulo `date`).
#
# Usage:
#   scripts/progress-snapshot.sh --report <path>
#                                           # parse counts from a report that
#                                           # `scripts/progress-report.sh
#                                           # --write <path>` just rendered.
#                                           # This is what the nightly does.
#   scripts/progress-snapshot.sh            # same, defaulting to ./PROGRESS.md
#                                           # (an untracked, locally generated
#                                           # artifact — run --write first).
#   scripts/progress-snapshot.sh --ref <commit>
#                                           # HISTORICAL ONLY: read the report
#                                           # from that commit via `git show`
#                                           # (no checkout). Works only for
#                                           # commits that still TRACKED
#                                           # PROGRESS.md, i.e. before #12683;
#                                           # for later commits pass --report.
#
# Counts are parsed from the rendered progress report. Before #12683 that file
# was committed and drift-gated, so this script needed no `lake build`; now the
# report is generated on demand (`scripts/progress-report.sh --write`) and the
# CALLER owns producing it — see .github/workflows/progress-history.yml, which
# builds once per night and passes --report. This script itself is still pure
# git + awk. The pinned EEST fixture tag comes from
# scripts/eest-fixture-tag.txt (still tracked), so the datapoint records which
# fixtures the conformance number reflects — report §6 fixture-pin non-goal.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

REF=""
REPORT_PATH=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --ref)
      REF="${2:-}"
      if [[ -z "$REF" ]]; then echo "progress-snapshot: --ref needs a commit" >&2; exit 2; fi
      shift 2
      ;;
    --report)
      REPORT_PATH="${2:-}"
      if [[ -z "$REPORT_PATH" ]]; then echo "progress-snapshot: --report needs a path" >&2; exit 2; fi
      shift 2
      ;;
    *)
      echo "progress-snapshot: unknown argument \`$1\`" >&2
      echo "usage: $0 [--report <path>] [--ref <commit>]" >&2
      exit 2
      ;;
  esac
done
if [[ -n "$REF" && -n "$REPORT_PATH" ]]; then
  # --ref still selects the recorded commit + fixture tag; the report text then
  # comes from --report. Allowed, but say so, because the pair is easy to
  # misread as "snapshot that commit's numbers".
  echo "progress-snapshot: --ref $REF selects commit/fixture-tag only; counts come from $REPORT_PATH" >&2
fi

# Read a tracked file either from the working tree (default) or, when --ref is
# given, from that commit via `git show` — so a snapshot can be taken for any
# commit without disturbing the checkout.
# `|| true` is load-bearing: under `set -e`, a failing command substitution in
# an assignment aborts the script, and a MISSING file is now the ordinary local
# case (PROGRESS.md is generated, not tracked — #12683). Without it the script
# died with a bare exit 1 and no message, which is exactly the silent failure
# the loud checks below exist to prevent. Callers test for an empty result.
read_tracked() {
  local path="$1"
  if [[ -n "$REF" ]]; then
    git show "${REF}:${path}" 2>/dev/null || true
  else
    cat "$path" 2>/dev/null || true
  fi
}

if [[ -n "$REF" ]]; then
  COMMIT="$(git rev-parse "$REF" 2>/dev/null || echo "$REF")"
else
  COMMIT="$(git rev-parse HEAD)"
fi
DATE="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
EEST_TAG="$(read_tracked scripts/eest-fixture-tag.txt | tr -d ' \n' || echo unknown)"
[[ -z "$EEST_TAG" ]] && EEST_TAG="unknown"

if [[ -n "$REPORT_PATH" ]]; then
  REPORT="$(cat "$REPORT_PATH" 2>/dev/null || true)"
  if [[ -z "$REPORT" ]]; then
    echo "progress-snapshot: --report $REPORT_PATH is missing or empty;" >&2
    echo "  render it first: scripts/progress-report.sh --write $REPORT_PATH" >&2
    exit 2
  fi
else
  # No --report: fall back to ./PROGRESS.md (untracked generated artifact), or
  # to that path at --ref for pre-#12683 commits where it was still tracked.
  REPORT="$(read_tracked PROGRESS.md)"
  if [[ -z "$REPORT" ]]; then
    echo "progress-snapshot: no progress report available${REF:+ at $REF}." >&2
    if [[ -n "$REF" ]]; then
      echo "  PROGRESS.md is no longer tracked (#12683), so --ref only works for" >&2
      echo "  commits that predate its removal. Render the report and pass --report." >&2
    else
      echo "  Render it first: scripts/progress-report.sh --write" >&2
    fi
    exit 2
  fi
fi

# Extract every count we track into KEY=VALUE shell assignments. The report
# renders, in order: the obligation count table (icons ✅/🟡/✗ + done/blocked/
# "not started"), then the entry-count table, then the byte-count table (after
# the "By **opcode byte**" line). We disambiguate the two tier tables by that
# marker. (The same disambiguation used to live in scripts/progress-delta.sh,
# retired in #12683 — its base↔head diff needed two COMMITTED reports.)
eval "$(printf '%s\n' "$REPORT" | awk '
  function emit(k, v) { printf "%s=%s\n", k, v }
  /^By \*\*opcode byte\*\*/ { in_bytes = 1 }
  # Obligation status counts (rendered before the tier tables).
  !in_bytes && /^\| ✅ done \|/        { n=split($0,c,"|"); gsub(/ /,"",c[n-1]); if(c[n-1]~/^[0-9]+$/) emit("OBL_DONE",c[n-1]) }
  !in_bytes && /^\| 🟡 blocked \|/     { n=split($0,c,"|"); gsub(/ /,"",c[n-1]); if(c[n-1]~/^[0-9]+$/) emit("OBL_BLOCKED",c[n-1]) }
  !in_bytes && /^\| ✗ not started \|/  { n=split($0,c,"|"); gsub(/ /,"",c[n-1]); if(c[n-1]~/^[0-9]+$/) emit("OBL_NOTSTARTED",c[n-1]) }
  # Tier ENTRY counts.
  !in_bytes && $0 ~ /\| (✅|🔶|🟡|⏳|✗) proven / { n=split($0,c,"|"); gsub(/ /,"",c[n-1]); if(c[n-1]~/^[0-9]+$/) emit("E_PROVEN",c[n-1]) }
  !in_bytes && $0 ~ /\| 🔶 conditional / { n=split($0,c,"|"); gsub(/ /,"",c[n-1]); if(c[n-1]~/^[0-9]+$/) emit("E_COND",c[n-1]) }
  !in_bytes && $0 ~ /\| 🟡 partial / { n=split($0,c,"|"); gsub(/ /,"",c[n-1]); if(c[n-1]~/^[0-9]+$/) emit("E_PARTIAL",c[n-1]) }
  !in_bytes && $0 ~ /\| ⏳ execSpec / { n=split($0,c,"|"); gsub(/ /,"",c[n-1]); if(c[n-1]~/^[0-9]+$/) emit("E_EXEC",c[n-1]) }
  !in_bytes && $0 ~ /\| ✗ notStarted / { n=split($0,c,"|"); gsub(/ /,"",c[n-1]); if(c[n-1]~/^[0-9]+$/) emit("E_NOTSTARTED",c[n-1]) }
  # Tier BYTE counts.
  in_bytes && $0 ~ /\| (✅|🔶|🟡|⏳|✗) proven / { n=split($0,c,"|"); gsub(/ /,"",c[n-1]); if(c[n-1]~/^[0-9]+$/) emit("B_PROVEN",c[n-1]) }
  in_bytes && $0 ~ /\| 🔶 conditional / { n=split($0,c,"|"); gsub(/ /,"",c[n-1]); if(c[n-1]~/^[0-9]+$/) emit("B_COND",c[n-1]) }
  in_bytes && $0 ~ /\| 🟡 partial / { n=split($0,c,"|"); gsub(/ /,"",c[n-1]); if(c[n-1]~/^[0-9]+$/) emit("B_PARTIAL",c[n-1]) }
  in_bytes && $0 ~ /\| ⏳ execSpec / { n=split($0,c,"|"); gsub(/ /,"",c[n-1]); if(c[n-1]~/^[0-9]+$/) emit("B_EXEC",c[n-1]) }
  in_bytes && $0 ~ /\| ✗ notStarted / { n=split($0,c,"|"); gsub(/ /,"",c[n-1]); if(c[n-1]~/^[0-9]+$/) emit("B_NOTSTARTED",c[n-1]) }
')"

# Fail loudly if any field failed to parse — do NOT default to 0. A silent 0
# would be recorded as a real datapoint and later read by progress-velocity.sh
# as a catastrophic (e.g. 42→0) regression, or could mask a real one (adversarial
# review). A parse miss means the report drifted in shape and must be fixed.
for v in E_PROVEN E_COND E_PARTIAL E_EXEC E_NOTSTARTED \
         B_PROVEN B_COND B_PARTIAL B_EXEC B_NOTSTARTED \
         OBL_DONE OBL_BLOCKED OBL_NOTSTARTED; do
  if [[ -z "${!v:-}" ]]; then
    echo "progress-snapshot: failed to parse $v from the progress report (table shape changed?)" >&2
    exit 1
  fi
done

printf '{'
printf '"commit":"%s",' "$COMMIT"
printf '"date":"%s",' "$DATE"
printf '"eest_tag":"%s",' "$EEST_TAG"
printf '"provenCount":%s,' "$E_PROVEN"
printf '"conditionalCount":%s,' "$E_COND"
printf '"partialCount":%s,' "$E_PARTIAL"
printf '"execSpecCount":%s,' "$E_EXEC"
printf '"notStartedCount":%s,' "$E_NOTSTARTED"
printf '"provenBytes":%s,' "$B_PROVEN"
printf '"conditionalBytes":%s,' "$B_COND"
printf '"partialBytes":%s,' "$B_PARTIAL"
printf '"execSpecBytes":%s,' "$B_EXEC"
printf '"notStartedBytes":%s,' "$B_NOTSTARTED"
printf '"obligationsDone":%s,' "$OBL_DONE"
printf '"obligationsBlocked":%s,' "$OBL_BLOCKED"
printf '"obligationsNotStarted":%s,' "$OBL_NOTSTARTED"
printf '}\n'
