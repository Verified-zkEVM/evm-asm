#!/usr/bin/env bash
#
# progress-delta.sh — deterministic PR-level progress delta.
#
# Reads PROGRESS.md at two commits (base + head), parses the
# kernel-checked count tables and per-opcode tier table, emits a
# structured Markdown block to stdout suitable for splicing into the
# augmented-instructions file consumed by the AI PR-summary workflow.
#
# No LLM. No mutation. Pure git + awk.
#
# Usage:
#   scripts/progress-delta.sh <base-sha> <head-sha>
#
# Typical CI invocation (see .github/workflows/summary.yml):
#   scripts/progress-delta.sh \
#       "${{ github.event.pull_request.base.sha }}" \
#       "${{ github.event.pull_request.head.sha }}"
#
# Exit codes:
#   0 — emitted a delta block (possibly "metric-neutral").
#   1 — git access error or PROGRESS.md missing on one side.
#
# Idempotent: re-running on the same pair of SHAs produces identical
# output. PROGRESS.md drift is enforced separately by
# scripts/check-progress.sh, so the inputs here are trustworthy.

set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <base-sha> <head-sha>" >&2
  exit 2
fi

BASE="$1"
HEAD="$2"

cd "$(dirname "$0")/.."

# --------------------------------------------------------------------
# Fetch both versions of PROGRESS.md. If either side is missing the
# file (e.g. this PR is the one introducing PROGRESS.md), fall back
# gracefully — emit a block that flags the introduction event.
# --------------------------------------------------------------------

TMP_BASE="$(mktemp)"
TMP_HEAD="$(mktemp)"
trap 'rm -f "$TMP_BASE" "$TMP_HEAD"' EXIT

if ! git show "${BASE}:PROGRESS.md" > "$TMP_BASE" 2>/dev/null; then
  : > "$TMP_BASE"
  BASE_MISSING=1
else
  BASE_MISSING=0
fi

if ! git show "${HEAD}:PROGRESS.md" > "$TMP_HEAD" 2>/dev/null; then
  : > "$TMP_HEAD"
  HEAD_MISSING=1
else
  HEAD_MISSING=0
fi

# --------------------------------------------------------------------
# Helpers — extract a single named count from a PROGRESS.md.
# The exe (`lake exe progress-report`) renders count lines like:
#     | ✅ proven      | 43 |
# We grep the icon + label and pull the trailing integer.
# --------------------------------------------------------------------

count_field() {
  local file="$1"
  local label="$2"   # e.g. "proven", "conditional", "partial", "execSpec", "notStarted"
  awk -v lbl="$label" '
    $0 ~ ("\\| (✅|🔶|🟡|⏳|✗) " lbl " *\\|") {
      # The integer is the last pipe-separated cell on this line. Only
      # accept a row whose trailing cell is purely numeric: the per-tier
      # rubric in the template uses the same `| <icon> <tier> | … |` shape
      # but carries PROSE in that cell, and it renders BEFORE the count
      # tables. Skip non-numeric matches and keep scanning to the real
      # count table.
      n = split($0, cells, "|")
      val = cells[n-1]; gsub(/ /, "", val)
      if (val ~ /^[0-9]+$/) { print val; exit }
    }
  ' "$file"
}

bytes_field() {
  # Distinguish entry-count tables from byte-count tables by looking at
  # the nearest preceding section header. We rely on the rendered order:
  # the entry-count table comes first, the byte-count table second.
  # We pick the second occurrence by `awk` counting.
  local file="$1"
  local label="$2"
  awk -v lbl="$label" '
    /^By \*\*opcode byte\*\*/ { in_bytes = 1 }
    in_bytes && $0 ~ ("\\| (✅|🔶|🟡|⏳|✗) " lbl " *\\|") {
      n = split($0, cells, "|")
      val = cells[n-1]; gsub(/ /, "", val)
      if (val ~ /^[0-9]+$/) { print val; exit }
    }
  ' "$file"
}

conformance_count() {
  local file="$1"
  # The value cell carries a "(floor in …, gated by …)" annotation
  # (added in Phase 2), so pull the FIRST integer run rather than the
  # whole cell — keeps the delta numeric instead of "?".
  # NB: the token is backtick-wrapped (`allConformanceVectors_length`), so do
  # NOT require a space before it — the previous `.* allConformanceVectors`
  # pattern never matched and conformance delta silently read as "?".
  awk '
    /Conformance vectors.*allConformanceVectors_length/ {
      n = split($0, cells, "|")
      val = cells[n-1]
      if (match(val, /[0-9]+/)) { print substr(val, RSTART, RLENGTH); exit }
    }
  ' "$file"
}

sorry_field() {
  local file="$1"
  awk '
    /sorry. count in/ {
      n = split($0, cells, "|")
      gsub(/ /, "", cells[n-1])
      print cells[n-1]
      exit
    }
  ' "$file"
}

axiom_field() {
  local file="$1"
  awk '
    /axiom. count in/ {
      n = split($0, cells, "|")
      gsub(/ /, "", cells[n-1])
      print cells[n-1]
      exit
    }
  ' "$file"
}

# --------------------------------------------------------------------
# Per-opcode tier table — extract rows of the form:
#   | <icon> <NAME> | <tier> | `<witness>` | <notes> |
# Output as: NAME<TAB>TIER per line.
# --------------------------------------------------------------------

opcode_tiers() {
  local file="$1"
  awk '
    BEGIN { in_table = 0 }
    /^### Per-opcode registry/ { in_table = 1; next }
    in_table && /^\| (✅|🔶|🟡|⏳|✗) / {
      # Strip the leading icon, then split.
      sub(/^\| (✅|🔶|🟡|⏳|✗) /, "| ", $0)
      n = split($0, cells, "|")
      # cells[2] = name, cells[3] = tier
      name = cells[2]; gsub(/^ +| +$/, "", name)
      tier = cells[3]; gsub(/^ +| +$/, "", tier)
      print name "\t" tier
    }
    in_table && /^## / { in_table = 0 }
  ' "$file"
}

# --------------------------------------------------------------------
# Compose the delta
# --------------------------------------------------------------------

# Pulls — base then head — for each tracked scalar.
B_PROVEN="$(count_field "$TMP_BASE" "proven" 2>/dev/null || echo "")"
B_CONDITIONAL="$(count_field "$TMP_BASE" "conditional" 2>/dev/null || echo "")"
B_PARTIAL="$(count_field "$TMP_BASE" "partial" 2>/dev/null || echo "")"
B_EXECSPEC="$(count_field "$TMP_BASE" "execSpec" 2>/dev/null || echo "")"
B_NOTSTARTED="$(count_field "$TMP_BASE" "notStarted" 2>/dev/null || echo "")"

H_PROVEN="$(count_field "$TMP_HEAD" "proven" 2>/dev/null || echo "")"
H_CONDITIONAL="$(count_field "$TMP_HEAD" "conditional" 2>/dev/null || echo "")"
H_PARTIAL="$(count_field "$TMP_HEAD" "partial" 2>/dev/null || echo "")"
H_EXECSPEC="$(count_field "$TMP_HEAD" "execSpec" 2>/dev/null || echo "")"
H_NOTSTARTED="$(count_field "$TMP_HEAD" "notStarted" 2>/dev/null || echo "")"

B_BYTES_PROVEN="$(bytes_field "$TMP_BASE" "proven" 2>/dev/null || echo "")"
H_BYTES_PROVEN="$(bytes_field "$TMP_HEAD" "proven" 2>/dev/null || echo "")"

B_CONF="$(conformance_count "$TMP_BASE" 2>/dev/null || echo "")"
H_CONF="$(conformance_count "$TMP_HEAD" 2>/dev/null || echo "")"

B_SORRY="$(sorry_field "$TMP_BASE" 2>/dev/null || echo "")"
H_SORRY="$(sorry_field "$TMP_HEAD" 2>/dev/null || echo "")"

B_AXIOM="$(axiom_field "$TMP_BASE" 2>/dev/null || echo "")"
H_AXIOM="$(axiom_field "$TMP_HEAD" 2>/dev/null || echo "")"

# Per-opcode transitions: compare BASE→HEAD tier per opcode name.
TIER_DIFF="$(mktemp)"
trap 'rm -f "$TMP_BASE" "$TMP_HEAD" "$TIER_DIFF"' EXIT

opcode_tiers "$TMP_BASE" > "${TIER_DIFF}.base" 2>/dev/null || : > "${TIER_DIFF}.base"
opcode_tiers "$TMP_HEAD" > "${TIER_DIFF}.head" 2>/dev/null || : > "${TIER_DIFF}.head"

# Join on opcode name, emit transitions where tier differs or entry is new/removed.
TRANSITIONS="$(awk -F'\t' '
  NR == FNR { base[$1] = $2; next }
  {
    if (!($1 in base)) {
      print "+ " $1 " (new entry, tier: " $2 ")"
    } else if (base[$1] != $2) {
      print "* " $1 ": " base[$1] " → " $2
    }
    seen[$1] = 1
  }
  END {
    for (op in base) {
      if (!(op in seen)) {
        print "- " op " (removed, was: " base[op] ")"
      }
    }
  }
' "${TIER_DIFF}.base" "${TIER_DIFF}.head" 2>/dev/null || true)"

rm -f "${TIER_DIFF}.base" "${TIER_DIFF}.head"

# --------------------------------------------------------------------
# Diff-derived scorecard inputs (R-B1, Phase 4 D3). Deterministic: pure
# git over the SAME BASE/HEAD pair, no LLM. Heuristic, advisory triage —
# NOT a gate, NOT auto-merge authority for the verified core (report §6).
#
# Mirrors the trusted-core path set in scripts/check-statement-tamper.sh
# and the CODEOWNERS verified-core map, so "touches trusted core" here
# means the same thing the human-review boundary means.
#
# errexit/pipefail are relaxed for this block: these are best-effort
# heuristics over a possibly-shallow CI clone; a grep non-match or an
# unresolvable merge base must degrade to "unknown", never abort.
# --------------------------------------------------------------------

set +e
MERGE_BASE="$(git merge-base "$BASE" "$HEAD" 2>/dev/null)"
[[ -z "$MERGE_BASE" ]] && MERGE_BASE="$BASE"

mapfile -t CHANGED_FILES < <(git diff --name-only "$MERGE_BASE" "$HEAD" 2>/dev/null)

# Full unified diff captured once to a temp file so the heuristics below
# grep it without re-shelling git per query (and without pipefail traps).
DIFF_TMP="$(mktemp)"
git diff "$MERGE_BASE" "$HEAD" > "$DIFF_TMP" 2>/dev/null || : > "$DIFF_TMP"

# Verified-core / verifier-config classifier (last-match-wins is irrelevant
# here — any single hit flags the PR). Kept in lockstep with
# check-statement-tamper.sh::is_verifier_config + .github/CODEOWNERS.
is_trusted_core() {
  case "$1" in
    EvmAsm/Progress.lean|EvmAsm/Progress/*)                       return 0 ;;
    EvmAsm/Rv64/*)                                                return 0 ;;
    EvmAsm/EL/Conformance/*)                                      return 0 ;;
    */Spec.lean|EvmAsm/*Spec.lean)                                return 0 ;;
    lakefile.toml|lean-toolchain)                                 return 0 ;;
    scripts/check-*.sh)                                           return 0 ;;
    scripts/axiom-allow.txt|scripts/conformance-baseline.txt)     return 0 ;;
    scripts/approved-heartbeat-overrides.txt)                     return 0 ;;
    scripts/duplication-baseline.txt|scripts/jscpd.json)          return 0 ;;
    scripts/churn-report.sh|scripts/cycles-append.sh)             return 0 ;;
    scripts/eest-fixture-tag.txt)                                 return 0 ;;
    scripts/codegen-eest-stateless-check.sh)                      return 0 ;;
    scripts/progress-report.sh|scripts/progress-snapshot.sh)      return 0 ;;
    scripts/progress-velocity.sh|scripts/progress-delta.sh)       return 0 ;;
    .github/workflows/*|.github/CODEOWNERS|.github/labeler.yml)   return 0 ;;
    *)                                                            return 1 ;;
  esac
}

TOUCHES_CORE=0          # any verified-core / verifier-config path
HIGH_FILE=0             # the report's named HIGH set: Progress.lean, Rv64/Basic.lean, *Spec.lean
CODEGEN_CHANGED=0       # codegen lowering (.lean) changed
ROUNDTRIP_CHANGED=0     # a round-trip/conformance script (or RoundTripTests) changed alongside
for f in "${CHANGED_FILES[@]}"; do
  is_trusted_core "$f" && TOUCHES_CORE=1
  case "$f" in
    EvmAsm/Progress.lean|EvmAsm/Rv64/Basic.lean) HIGH_FILE=1 ;;
    */Spec.lean|EvmAsm/*Spec.lean)               HIGH_FILE=1 ;;
  esac
  case "$f" in
    EvmAsm/Codegen/*.lean) CODEGEN_CHANGED=1 ;;
  esac
  case "$f" in
    scripts/codegen-*.sh|EvmAsm/Codegen/RoundTripTests.lean) ROUNDTRIP_CHANGED=1 ;;
  esac
done

# Theorem-statement edit: a REMOVED/MODIFIED signature line ('-' side).
# Same header regex as check-statement-tamper.sh. A pure addition (a new
# theorem) is NOT a tamper signal, so we only scan '-' lines.
STMT_HDR_RE='^-[[:space:]]*(private[[:space:]]+|protected[[:space:]]+|noncomputable[[:space:]]+|@\[[^]]*\][[:space:]]*)*(theorem|lemma)[[:space:]]'
if grep -qE "$STMT_HDR_RE" "$DIFF_TMP"; then STATEMENT_DIFF=1; else STATEMENT_DIFF=0; fi

# New top-level stack-spec triples added on the '+' side (distinct names).
NEW_TRIPLES="$(grep '^+' "$DIFF_TMP" \
  | grep -oE 'theorem evm_[a-zA-Z0-9_]+_stack_spec(_within)?' \
  | sort -u | wc -l)"
NEW_TRIPLES="${NEW_TRIPLES//[[:space:]]/}"

# Changed-line magnitude for the XL flag, EXCLUDING bulk codegen-*.sh
# regens (a 500-script refresh is not a "large risky diff"; mirrors the
# D4 size-labeler exclusion).
CHANGED_LINES="$(awk '
    $1 ~ /^[0-9]+$/ && $2 ~ /^[0-9]+$/ && $3 !~ /^scripts\/codegen-.*\.sh$/ { s += $1 + $2 }
    END { print s + 0 }' <(git diff --numstat "$MERGE_BASE" "$HEAD" 2>/dev/null))"
CHANGED_LINES="${CHANGED_LINES//[[:space:]]/}"
[[ "$CHANGED_LINES" =~ ^[0-9]+$ ]] || CHANGED_LINES=0
XL_THRESHOLD=1000      # calibratable — Phase 4 PR open question #3
XL=0; (( CHANGED_LINES > XL_THRESHOLD )) && XL=1

rm -f "$DIFF_TMP"
set -e

# Net Δ sorries + axioms (an INCREASE is the risk signal). Empty → 0.
sdelta() {  # signed delta string "+n"/"-n"/"?"
  local a="$1" b="$2"
  if [[ "$a" =~ ^[0-9]+$ && "$b" =~ ^[0-9]+$ ]]; then
    local d=$((b - a)); (( d >= 0 )) && echo "+$d" || echo "$d"
  else
    echo "?"
  fi
}
ndelta() { # numeric delta or 0 when an endpoint is unknown
  local a="$1" b="$2"
  if [[ "$a" =~ ^[0-9]+$ && "$b" =~ ^[0-9]+$ ]]; then echo $((b - a)); else echo 0; fi
}
NET_AS=$(( $(ndelta "$B_SORRY" "$H_SORRY") + $(ndelta "$B_AXIOM" "$H_AXIOM") ))

# --------------------------------------------------------------------
# Risk label: HIGH triggers are exactly the report's set (R-B1); MEDIUM
# escalations are the softer trust-core / spec-weakening signals.
# --------------------------------------------------------------------
HIGH_REASONS=()
MED_REASONS=()
(( HIGH_FILE )) && HIGH_REASONS+=("touches a trust-core statement file (\`Progress.lean\` / \`Rv64/Basic.lean\` / \`*Spec.lean\`)")
(( XL )) && HIGH_REASONS+=("XL diff: ${CHANGED_LINES} changed lines (excl. \`codegen-*.sh\`) > ${XL_THRESHOLD}")
(( CODEGEN_CHANGED == 1 && ROUNDTRIP_CHANGED == 0 )) && HIGH_REASONS+=("codegen lowering changed with no round-trip / conformance script change")
(( TOUCHES_CORE )) && MED_REASONS+=("touches verified-core / verifier-config")
(( STATEMENT_DIFF )) && MED_REASONS+=("removes/modifies a theorem statement (review for a weakened spec)")
(( NET_AS > 0 )) && MED_REASONS+=("net +${NET_AS} sorries/axioms")

if (( ${#HIGH_REASONS[@]} > 0 )); then
  RISK="HIGH"
elif (( ${#MED_REASONS[@]} > 0 )); then
  RISK="MEDIUM"
else
  RISK="LOW"
fi

# --------------------------------------------------------------------
# Format a count delta as "old → new (±n)" or omit if unchanged.
# --------------------------------------------------------------------

count_delta_line() {
  local label="$1" old="$2" new="$3"
  if [[ -z "$old" && -z "$new" ]]; then return; fi
  if [[ "$old" == "$new" ]]; then
    printf -- "- %s: %s (unchanged)\n" "$label" "${new:-unknown}"
  else
    local sign
    if [[ -z "$old" || -z "$new" ]]; then
      sign="?"
    else
      local delta=$((new - old))
      if (( delta >= 0 )); then sign="+${delta}"; else sign="${delta}"; fi
    fi
    printf -- "- %s: %s → %s (%s)\n" "$label" "${old:-?}" "${new:-?}" "$sign"
  fi
}

# --------------------------------------------------------------------
# Emit
# --------------------------------------------------------------------

cat <<EOF
## Computed progress delta for this PR

Inputs: \`PROGRESS.md\` at base \`${BASE:0:7}\` vs head \`${HEAD:0:7}\`.
Source is the kernel-checked registry in \`EvmAsm/Progress.lean\`;
drift between the registry and \`PROGRESS.md\` is gated separately by
\`scripts/check-progress.sh\` in CI.

EOF

if (( BASE_MISSING )); then
  echo "_Note: PROGRESS.md did not exist at base; this PR appears to introduce it._"
  echo
fi
if (( HEAD_MISSING )); then
  echo "_Note: PROGRESS.md is absent at head; downstream sections may be empty._"
  echo
fi

echo "### Count deltas"
echo
count_delta_line "proven (entries)"      "$B_PROVEN"        "$H_PROVEN"
count_delta_line "conditional (entries)" "$B_CONDITIONAL"   "$H_CONDITIONAL"
count_delta_line "partial (entries)"     "$B_PARTIAL"       "$H_PARTIAL"
count_delta_line "execSpec (entries)"    "$B_EXECSPEC"      "$H_EXECSPEC"
count_delta_line "notStarted (entries)"  "$B_NOTSTARTED"    "$H_NOTSTARTED"
count_delta_line "proven (opcode bytes)" "$B_BYTES_PROVEN"  "$H_BYTES_PROVEN"
count_delta_line "conformance vectors"   "$B_CONF"          "$H_CONF"
count_delta_line "sorry count"           "$B_SORRY"         "$H_SORRY"
count_delta_line "axiom count"           "$B_AXIOM"         "$H_AXIOM"
echo

echo "### Per-opcode tier transitions"
echo
if [[ -z "$TRANSITIONS" ]]; then
  echo "_No tier transitions._"
else
  echo "$TRANSITIONS" | sed 's/^/    /'
fi
echo

# --------------------------------------------------------------------
# Scorecard + risk label (R-B1, Phase 4 D3). Deterministic triage for
# the human reviewer — five objective columns plus a HIGH/MEDIUM/LOW
# label. Triage ORDERING, not auto-merge authority for the verified
# core (report §6).
# --------------------------------------------------------------------

yesno() { (( $1 )) && echo "yes" || echo "no"; }

echo "### Scorecard"
echo
echo "| Field | Value |"
echo "|---|---|"
echo "| New top-level triples (added \`evm_*_stack_spec[_within]\`) | ${NEW_TRIPLES} |"
printf '| Δ tier counts (proven / conditional / partial / execSpec) | %s / %s / %s / %s |\n' \
  "$(sdelta "$B_PROVEN" "$H_PROVEN")" \
  "$(sdelta "$B_CONDITIONAL" "$H_CONDITIONAL")" \
  "$(sdelta "$B_PARTIAL" "$H_PARTIAL")" \
  "$(sdelta "$B_EXECSPEC" "$H_EXECSPEC")"
echo "| Net Δ sorries + axioms | $( (( NET_AS >= 0 )) && echo "+${NET_AS}" || echo "${NET_AS}") |"
echo "| Δ conformance vectors | $(sdelta "$B_CONF" "$H_CONF") (EEST full-match: n/a at PR time — merge-queue/nightly harness) |"
echo "| Touches trusted core | $(yesno "$TOUCHES_CORE") |"
echo "| Statement edit (theorem signature removed/modified) | $(yesno "$STATEMENT_DIFF") |"
echo "| Changed lines (excl. \`codegen-*.sh\`) | ${CHANGED_LINES} |"
echo

echo "### Risk: ${RISK}"
echo
if [[ "$RISK" == "HIGH" ]]; then
  for r in "${HIGH_REASONS[@]}"; do echo "- $r"; done
elif [[ "$RISK" == "MEDIUM" ]]; then
  for r in "${MED_REASONS[@]}"; do echo "- $r"; done
else
  echo "- No trust-core, statement, XL, or sorry/axiom-increase signals."
fi
echo
echo "_Risk is **deterministic triage ordering** for the human reviewer — not a"
echo "gate and **not auto-merge authority for the verified core** (report §6)."
echo "The XL threshold (${XL_THRESHOLD} lines) and the trusted-core path set are"
echo "calibratable; see the Phase 4 PR open questions._"
echo
