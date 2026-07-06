#!/usr/bin/env bash
#
# check-naming.sh — advisory nudge against the PR #1497 regression class:
# snake_case proof hypotheses (`h_lt`, `h_pos`) being (re)introduced in
# camelCase (`hLt`, `hPos`). Report R-D1 / AGENTS.md "Naming convention":
#
#   * camelCase  for VALUE identifiers (let-bound data, def/lemma params).
#   * snake_case for HYPOTHESIS names introduced by have/obtain/intro/rcases.
#
# The kernel does not care what a binder is called, so naming is a pure
# legibility/maintainability convention — exactly the sort of prose rule a
# fitness function should surface (without the false-positive friction of a
# hard gate).
#
# CALIBRATION — why this is diff-scoped + advisory, never blocking:
#   The current tree already contains *thousands* of camelCase hypothesis
#   names (hP, hR, hLoop, …). A full-tree gate would be pure noise and could
#   never go green. So the default scans only hypotheses ADDED in the PR diff
#   (vs the merge-base) and ALWAYS exits 0. It is a review nudge that feeds the
#   PR scorecard, not a build gate. The heuristic intentionally ignores
#   single-capital short names (hP, hR) and all-caps suffixes; it flags only
#   `h<Upper><lower…>` (a camelCased multi-letter word — the #1497 shape).
#
# HEURISTIC CAVEAT: matching is per added line — the intro keyword and the
# binder must share a line, so a binder wrapped onto the next line, or a
# match/fun/case-arm binder with no intro keyword, is not flagged. That is fine
# for an advisory nudge (false negatives only; never blocks).
#
# Usage:
#   scripts/check-naming.sh                 # diff vs base; advisory; exit 0
#   scripts/check-naming.sh --base <ref>    # explicit base (default:
#                                           #   $GITHUB_BASE_REF or origin/main)
#   scripts/check-naming.sh --all           # whole-tree census (count only)
#
# POSIX/bash; deps: git, grep. Pure source scan, no build.

set -uo pipefail
export LC_ALL=C   # byte-wise grep: \b stays correct next to multibyte ⟨⟩ binders

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

# `h` + uppercase + at least one lowercase = a camelCased word (hLt, hPos,
# hLoop). Excludes hP / hR (single cap) and hRHS-style all-caps.
CAMEL_HYP='\bh[A-Z][a-z][A-Za-z0-9]*'
# only on binder-introducing tactics, to avoid flagging mere references
INTRO_CTX='\b(have|obtain|intro|rintro|rcases|set|let)\b'

BASE=""
MODE="diff"
while [[ $# -gt 0 ]]; do
  case "$1" in
    --base) BASE="$2"; shift 2 ;;
    --all) MODE="all"; shift ;;
    *) echo "usage: $0 [--base <ref>] [--all]" >&2; exit 2 ;;
  esac
done

if [[ "$MODE" == "all" ]]; then
  n=$(grep -rhoE "${INTRO_CTX}[^:=]*${CAMEL_HYP}" EvmAsm --include='*.lean' 2>/dev/null \
        | grep -oE "$CAMEL_HYP" | sort -u | wc -l)
  echo "check-naming (--all): $n distinct camelCase hypothesis name(s) tree-wide (legacy; advisory)."
  exit 0
fi

# ---- resolve base ref (mirror check-statement-tamper.sh) --------------
if [[ -z "$BASE" ]]; then
  BASE="origin/${GITHUB_BASE_REF:-}"
  [[ "$BASE" == "origin/" ]] && BASE="origin/main"
fi
if ! git rev-parse --verify --quiet "$BASE^{commit}" >/dev/null; then
  git fetch --no-tags --depth=200 origin "${BASE#origin/}" >/dev/null 2>&1 || true
fi
if ! git rev-parse --verify --quiet "$BASE^{commit}" >/dev/null; then
  echo "check-naming: base ref '$BASE' unavailable (shallow clone?); skipping. (advisory)"
  exit 0
fi
MERGE_BASE="$(git merge-base "$BASE" HEAD 2>/dev/null || echo "$BASE")"

mapfile -t CHANGED < <(git diff --name-only "$MERGE_BASE"...HEAD 2>/dev/null | grep -E '\.lean$' || true)
if (( ${#CHANGED[@]} == 0 )); then
  echo "check-naming: no changed .lean files vs $BASE. (advisory)"
  exit 0
fi

echo "== camelCase hypothesis names ADDED in this PR (advisory — prefer h_snake_case) =="
hits=0
for f in "${CHANGED[@]}"; do
  [[ -f "$f" ]] || continue
  # ADDED lines ('+', not the '+++' header) that introduce a binder with a
  # camelCased h-name.
  added="$(git diff "$MERGE_BASE"...HEAD -- "$f" 2>/dev/null \
    | grep -E '^\+' | grep -vE '^\+\+\+' \
    | grep -E "$INTRO_CTX" | grep -oE "$CAMEL_HYP" | sort -u || true)"
  if [[ -n "$added" ]]; then
    echo "  $f:"
    printf '    %s\n' $added
    hits=$((hits + 1))
  fi
done
(( hits == 0 )) && echo "  (none — no new camelCase hypotheses)"

echo
echo "check-naming: advisory scan complete (exit 0). Rename new h<Upper> binders to h_snake_case where they name a Prop."
exit 0
