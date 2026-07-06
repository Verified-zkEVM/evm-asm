#!/usr/bin/env bash
#
# check-heartbeats-approved.sh — heartbeats are OFF-LIMITS. Flag EVERY mention
# of "heartbeats" in the proof sources + lakefiles; each must be sanctioned in
# scripts/approved-heartbeat-overrides.txt at its exact (path, value).
#
# DELIBERATELY DUMB: this is a case-insensitive substring scan, NOT a Lean
# lexer. There is nothing to parse and nothing to bypass — a `set_option
# maxHeartbeats N`, a docstring, a string literal, a char literal, a lakefile
# global option are all flagged identically. (Three prior review rounds each
# found a fresh bypass in a clever comment/string-aware scanner; the policy is
# simply "nobody touches heartbeats," so the gate matches the policy: any
# appearance at all is logged in the allowlist.)
#
# The allowlist is the single source of truth for WHERE a heartbeat budget may
# even be mentioned and (for numeric overrides) at WHAT value — so raising
# 800000 -> 900000, or adding an override/mention anywhere, is an explicit
# reviewable edit to that file (CODEOWNERS-gated verifier config).
#
# Allowlist format, one entry per line:   <repo-relative-path> <value>
#   <value> = the heartbeat number on the line (e.g. 800000, underscores
#   stripped), or `-` for a sanctioned NON-numeric mention (a docstring/comment
#   that names the option without setting a value). A file with several
#   mentions gets one line each.
#
# Usage:
#   scripts/check-heartbeats-approved.sh           # exit 1 on any unapproved mention
#   scripts/check-heartbeats-approved.sh --report  # always exit 0; list state
#
# POSIX/bash; deps: grep. No build, no parsing.

set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

ALLOW="scripts/approved-heartbeat-overrides.txt"
REPORT=0
[[ "${1:-}" == "--report" ]] && REPORT=1

[[ -f "$ALLOW" ]] || { echo "check-heartbeats-approved: missing allowlist $ALLOW" >&2; exit 2; }

# ---- load allowlist: exact (path,value) pairs + per-path value set --------
declare -A APPROVED_PAIR APPROVED_VALS
while read -r path val _rest; do
  [[ -z "${path:-}" ]] && continue
  [[ "$path" == \#* ]] && continue
  APPROVED_PAIR["$path"$'\t'"$val"]=1
  APPROVED_VALS["$path"]="${APPROVED_VALS[$path]:-} $val"
done < "$ALLOW"

# ---- scan: every line mentioning "heartbeats" in .lean + lakefiles --------
# Scope is ALL repo `.lean` (not just EvmAsm/ — the root Main*.lean / EvmAsm.lean
# also compile and could carry an override), EXCLUDING `.lake/` (Mathlib & other
# dependency sources mention maxHeartbeats heavily and are not ours to gate).
# grep exit: 0=match, 1=no match (fine), >1=real error (fail loud).
# NOTE: CI `lake build -D…heartbeats=…` build args (a .github/workflows edit) are
# out of this scan's scope but are fenced by check-statement-tamper + CODEOWNERS.
# Accepted limitations (both reviewable acts themselves): a SYMLINKED `.lean`
# target is not followed (grep -r), and an override split across a newline from
# its `set_option maxHeartbeats` keyword still flags the keyword line.
HITS_RAW="$(grep -rniE 'heartbeats' . --include='*.lean' --exclude-dir='.lake' 2>/dev/null)"; rc=$?
(( rc > 1 )) && { echo "check-heartbeats-approved: scanner error (grep rc=$rc); failing loud." >&2; exit 2; }
HITS="$(printf '%s' "$HITS_RAW" | sed 's#^\./##')"   # normalize leading ./ to match allowlist paths
for lf in lakefile.toml lakefile.lean; do
  [[ -f "$lf" ]] || continue
  while IFS= read -r ln; do HITS+="$lf:$ln"$'\n'; done \
    < <(grep -niE 'heartbeats' "$lf" 2>/dev/null || true)
done

violations=0
found=0
while IFS= read -r hit; do
  [[ -z "$hit" ]] && continue
  file="${hit%%:*}"
  text="${hit#*:}"; text="${text#*:}"     # strip "path:" then "lineno:"
  # EVERY number adjacent to a "heartbeats" token on the line (underscores
  # stripped), or '-' for a non-numeric mention. Checking *all* of them — not
  # just the first/last — defeats value-spoofing (a real override plus a
  # trailing/leading comment that re-states an allowlisted number): each value
  # must be sanctioned independently.
  nums="$(printf '%s' "$text" | grep -oiE 'heartbeats[^0-9]*[0-9][0-9_]*' | grep -oE '[0-9][0-9_]*' | tr -d '_')"
  [[ -z "$nums" ]] && nums='-'

  while IFS= read -r num; do
    [[ -z "$num" ]] && continue
    found=$((found + 1))
    if [[ -n "${APPROVED_PAIR["$file"$'\t'"$num"]+x}" ]]; then
      (( REPORT )) && echo "  ok          $file  (heartbeats $num)"
    elif [[ -n "${APPROVED_VALS[$file]+x}" ]]; then
      echo "  VALUE-DRIFT $file  (line has $num, allowlist permits${APPROVED_VALS[$file]})"
      violations=$((violations + 1))
    else
      echo "  UNAPPROVED  $file  (heartbeats $num) — not in $ALLOW"
      violations=$((violations + 1))
    fi
  done <<< "$nums"
done <<< "$HITS"

if (( REPORT )); then
  echo "check-heartbeats-approved: $found mention(s) found, $violations unapproved/mis-valued."
  exit 0
fi

if (( violations > 0 )); then
  cat >&2 <<EOF
==================================================================
check-heartbeats-approved FAILED: $violations heartbeat mention(s)
above are not sanctioned in $ALLOW (or carry a different value).

Heartbeats are off-limits: EVERY mention is flagged. The standing
guidance (AGENTS.md) is to simplify the proof, never raise the budget.
If a mention is genuinely warranted, add its exact "<path> <value>"
entry to $ALLOW in a reviewable edit (use value '-' for a non-numeric
docstring mention) — that file is verifier config (CODEOWNERS-gated).
==================================================================
EOF
  exit 1
fi

echo "check-heartbeats-approved: all $found heartbeat mention(s) sanctioned. OK."
exit 0
