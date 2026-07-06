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
#   scripts/progress-snapshot.sh            # emit one JSONL record (working tree)
#   scripts/progress-snapshot.sh --ref <commit>
#                                           # snapshot an arbitrary commit via
#                                           # `git show` (no checkout). Used by
#                                           # the PR-time velocity gate (Phase 4
#                                           # D7) to read the PR *base* commit.
#
# Counts are parsed from the committed PROGRESS.md (which `check-progress.sh`
# already pins to the kernel-checked renderer, so no `lake build` is needed
# here — keeps the history workflow cheap, report §6 build-budget non-goal),
# conformance from the `allConformanceVectorCount` theorem, and the pinned EEST
# fixture tag from scripts/eest-fixture-tag.txt (so the datapoint records which
# fixtures the conformance number reflects — report §6 fixture-pin non-goal).

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

REF=""
if [[ "${1:-}" == "--ref" ]]; then
  REF="${2:-}"
  if [[ -z "$REF" ]]; then echo "progress-snapshot: --ref needs a commit" >&2; exit 2; fi
fi

# Read a tracked file either from the working tree (default) or, when --ref is
# given, from that commit via `git show` — so a snapshot can be taken for any
# commit without disturbing the checkout.
read_tracked() {
  local path="$1"
  if [[ -n "$REF" ]]; then
    git show "${REF}:${path}" 2>/dev/null
  else
    cat "$path" 2>/dev/null
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

CONF_COUNT="$(read_tracked EvmAsm/EL/Conformance/All.lean \
  | grep -oE 'allConformanceVectorCount = [0-9]+' | head -1 | grep -oE '[0-9]+' || true)"
if [[ -z "$CONF_COUNT" ]]; then
  echo "progress-snapshot: failed to parse allConformanceVectorCount${REF:+ at $REF}" >&2
  exit 1
fi

REPORT="$(read_tracked PROGRESS.md)"
if [[ -z "$REPORT" ]]; then
  echo "progress-snapshot: PROGRESS.md missing${REF:+ at $REF}; run scripts/progress-report.sh --write" >&2
  exit 2
fi

# Extract every count we track into KEY=VALUE shell assignments. PROGRESS.md
# renders, in order: the obligation count table (icons ✅/🟡/✗ + done/blocked/
# "not started"), then the entry-count table, then the byte-count table (after
# the "By **opcode byte**" line). We disambiguate the two tier tables by that
# marker, exactly like scripts/progress-delta.sh.
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
# review). A parse miss means PROGRESS.md drifted in shape and must be fixed.
for v in E_PROVEN E_COND E_PARTIAL E_EXEC E_NOTSTARTED \
         B_PROVEN B_COND B_PARTIAL B_EXEC B_NOTSTARTED \
         OBL_DONE OBL_BLOCKED OBL_NOTSTARTED; do
  if [[ -z "${!v:-}" ]]; then
    echo "progress-snapshot: failed to parse $v from PROGRESS.md (table shape changed?)" >&2
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
printf '"conformanceCount":%s' "$CONF_COUNT"
printf '}\n'
