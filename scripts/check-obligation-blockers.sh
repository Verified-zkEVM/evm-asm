#!/usr/bin/env bash
#
# check-obligation-blockers.sh — ADVISORY architecture fitness function.
#
# Flags obligation-matrix blockers that cite an already-CLOSED GitHub issue.
#
# Why this exists (#11803)
# ------------------------
# `EvmAsm/Progress/Obligations.lean` is the dashboard the end-to-end effort
# steers by, and its `blockedBy` lists are claims about the present. #11803's
# audit found three distinct ways they decay:
#
#   1. an opcode blocker naming an already-`.proven` opcode (obligation 5 named
#      eight of them) — now KERNEL-gated by `no_proven_opcode_blockers`;
#   2. an infra blocker citing shipped work in prose (obligation 4 cited codegen
#      M5, done since PLAN.md:23) — not mechanically detectable, which is why
#      rows carry an `auditedAt` date + commit instead;
#   3. an infra blocker citing a CLOSED issue (obligation 10 carried #11346,
#      #11347 and #11422 after all three closed) — that is THIS script.
#
# Class 3 is mechanically checkable but not from inside Lean: the kernel cannot
# query GitHub. So it lives here, and it is **advisory** (always exit 0) for two
# reasons: it needs network + `gh` auth, which CI environments may not have, and
# per `AGENTS.md` a new gate is seeded green rather than red-lighting day one.
#
# Input is the RENDERED table in PROGRESS.md rather than the Lean source: the
# rendered "Blocked by" cell is exactly the blocker text, one obligation per
# line, already pipe-delimited — far more robust to parse than Lean string
# literals with `\`-continuations. It also means a blocker only trips this check
# once it is actually visible on the dashboard.
#
# Deliberately scoped to the "Blocked by" COLUMN, not whole rows: the `note`
# prose legitimately cites closed issues as evidence ("#11347 and #11422
# closed"), and flagging those would be pure noise.
#
# Usage:
#   scripts/check-obligation-blockers.sh          # advisory (always exit 0)
#   scripts/check-obligation-blockers.sh --strict # exit 1 on a closed blocker
#
set -uo pipefail
cd "$(dirname "$0")/.."

STRICT=0
[[ "${1:-}" == "--strict" ]] && STRICT=1

REPO="Verified-zkEVM/evm-asm"
PROGRESS="PROGRESS.md"

if [[ ! -f "$PROGRESS" ]]; then
  echo "check-obligation-blockers: $PROGRESS not found — skipping." >&2
  exit 0
fi

if ! command -v gh >/dev/null 2>&1; then
  echo "check-obligation-blockers: \`gh\` not on PATH — skipping (advisory)." >&2
  exit 0
fi

if ! gh auth status >/dev/null 2>&1; then
  echo "check-obligation-blockers: \`gh\` not authenticated — skipping (advisory)." >&2
  exit 0
fi

# Extract the obligation table's rows. The table is introduced by the header
# `| # | Obligation | Status | Blocked by | Audited |`; rows are the following
# `| <n> | ...` lines. Field 5 is the "Blocked by" cell (field 1 is the empty
# string before the leading pipe).
rows="$(awk -F'|' '
  /^\| # \| Obligation \| Status \| Blocked by \|/ { intable = 1; next }
  intable && /^\|[[:space:]]*[0-9]+[[:space:]]*\|/ {
    gsub(/^[[:space:]]+|[[:space:]]+$/, "", $2)
    gsub(/^[[:space:]]+|[[:space:]]+$/, "", $5)
    print $2 "\t" $5
    next
  }
  intable && !/^\|/ { intable = 0 }
' "$PROGRESS")"

if [[ -z "$rows" ]]; then
  echo "check-obligation-blockers: no obligation table found in $PROGRESS — skipping." >&2
  exit 0
fi

# Collect every distinct issue number cited in a blocker cell.
#
# `obligation #N` is a reference to another ROW of this matrix, not to an issue —
# obligation 8 is blocked by obligations #4/#5/#6/#7. Those low numbers happen to
# collide with real issue numbers, so scanning naively reported #6 and #7 as
# "closed blockers" when they are neither closed nor blockers. Strip that form
# before extracting.
declare -A cited_by
while IFS=$'\t' read -r oid cell; do
  [[ -z "$cell" ]] && continue
  cell="$(sed -E 's/[Oo]bligation[[:space:]]*#[0-9]+//g' <<<"$cell")"
  for num in $(grep -oE '#[0-9]+' <<<"$cell" | tr -d '#' | sort -u); do
    if [[ -n "${cited_by[$num]:-}" ]]; then
      cited_by[$num]="${cited_by[$num]},$oid"
    else
      cited_by[$num]="$oid"
    fi
  done
done <<<"$rows"

if [[ ${#cited_by[@]} -eq 0 ]]; then
  echo "check-obligation-blockers: no issue-numbered blockers to check. OK."
  exit 0
fi

stale=0
checked=0
for num in $(printf '%s\n' "${!cited_by[@]}" | sort -n); do
  state="$(gh issue view "$num" --repo "$REPO" --json state --jq '.state' 2>/dev/null)"
  if [[ -z "$state" ]]; then
    echo "  ?  #$num — could not resolve (obligation ${cited_by[$num]}); skipped."
    continue
  fi
  checked=$((checked + 1))
  if [[ "$state" == "CLOSED" ]]; then
    title="$(gh issue view "$num" --repo "$REPO" --json title --jq '.title' 2>/dev/null | cut -c1-70)"
    echo "  ✗  #$num is CLOSED but still blocks obligation ${cited_by[$num]}: $title"
    stale=$((stale + 1))
  fi
done

echo "check-obligation-blockers: $checked issue-numbered blocker(s) checked, $stale stale."

if [[ $stale -gt 0 ]]; then
  cat <<'EOF'

A closed issue left in a `blockedBy` list makes the obligation read as further
from done than it is, and hides the real blockers behind plausible-looking rows.
Remove it from `EvmAsm/Progress/Obligations.lean`, refresh that row's
`auditedAt`, then re-run `scripts/progress-report.sh --write` and
`scripts/drift-report.sh --write`.
EOF
  [[ $STRICT -eq 1 ]] && exit 1
fi

exit 0
