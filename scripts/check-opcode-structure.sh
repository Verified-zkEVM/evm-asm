#!/usr/bin/env bash
#
# check-opcode-structure.sh — keep new EVM-opcode subtrees on the
# OPCODE_TEMPLATE.md substrate so they don't recreate the DivMod retrofit tax
# (~39k LOC of cleanup across issues #261–#312). Report R-D1; fitness function
# in the Ford/Parsons sense (the prose template, made executable).
#
# The template lists conventions that land at *different* first-commits
# (AddrNorm on the first non-trivial address computation; Offsets on the second
# block; FullPath is the end-state composition). So we CANNOT require the full
# bundle on a dir's first appearance — most in-progress complex opcodes
# (AddMod, Exp, MulMod, SDiv, SMod) legitimately have no FullPath yet. The gate
# therefore splits into:
#
#   HARD INVARIANT (blocks, scanned tree-wide):
#     AddrNorm pairing — within any EvmAsm/Evm64/<Op>/, AddrNorm.lean and
#     AddrNormAttr.lean must co-occur (both, or neither). Lean forbids using a
#     `register_simp_attr` in the same file that declares it (AGENTS.md "Import
#     Hygiene"; template §2.5), so a lone AddrNorm.lean is a real structural
#     bug, not a style preference. Holds across the whole tree today.
#
#   ADVISORY CHECKLIST (reports, never blocks; diff-scoped to NEW complex
#   dirs): when a PR introduces a *new* complex opcode subtree (one that adds a
#   Compose/ or LimbSpec/ directory), nudge toward the remaining template
#   essentials it has not yet shipped: a FullPath spec, an @[irreducible] Post
#   def, and Compose/Offsets.lean. These are reminders for review, calibrated
#   so the build stays green on day one.
#
# On a non-PR CI event (push / merge_group) the diff-scoped advisory checklist
# is skipped (no PR base to diff); the HARD AddrNorm pairing invariant always
# runs. Locally (no GITHUB_EVENT_NAME) the checklist runs vs origin/main.
#
# Usage:
#   scripts/check-opcode-structure.sh             # HARD invariant; advisory
#                                                 #   checklist vs base ref
#   scripts/check-opcode-structure.sh --base <r>  # explicit diff base
#   scripts/check-opcode-structure.sh --report    # full census; always exit 0
#
# POSIX/bash; deps: git, grep, find. Pure source scan, no build.

set -uo pipefail
export LC_ALL=C

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

OPDIR="EvmAsm/Evm64"
BASE=""
REPORT=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --base) BASE="$2"; shift 2 ;;
    --report) REPORT=1; shift ;;
    *) echo "usage: $0 [--base <ref>] [--report]" >&2; exit 2 ;;
  esac
done

is_complex() { [[ -d "$1/Compose" || -d "$1/LimbSpec" ]]; }
has_fullpath() { find "$1" -name '*FullPath*.lean' 2>/dev/null | grep -q .; }
has_irreducible_post() {
  # an @[irreducible] attribute anywhere in the subtree near a Post/Iter def
  grep -rlE '@\[irreducible\]' "$1" --include='*.lean' >/dev/null 2>&1
}
has_offsets() { [[ -f "$1/Compose/Offsets.lean" ]]; }

# ---- HARD: AddrNorm/AddrNormAttr pairing (tree-wide) ------------------
# Driven off `find` over ALL of EvmAsm/, so a lone AddrNorm.lean in a nested
# subdir (…/Compose/AddrNorm.lean) or outside Evm64/ (e.g. Rv64/AddrNorm.lean)
# cannot evade the pairing invariant by living below the opcode-dir level.
echo "== HARD: AddrNorm.lean <-> AddrNormAttr.lean must co-occur in the same dir =="
pair_viol=0
while IFS= read -r d; do
  [[ -z "$d" ]] && continue
  a=0; aa=0
  [[ -f "$d/AddrNorm.lean" ]] && a=1
  [[ -f "$d/AddrNormAttr.lean" ]] && aa=1
  if (( a != aa )); then
    echo "  VIOLATION $d: AddrNorm.lean=$a AddrNormAttr.lean=$aa (must be both or neither)"
    pair_viol=$((pair_viol + 1))
  fi
done < <( { find EvmAsm -name 'AddrNorm.lean' -o -name 'AddrNormAttr.lean'; } 2>/dev/null \
            | xargs -r -n1 dirname | sort -u )
(( pair_viol == 0 )) && echo "  (clean)"

# ---- ADVISORY checklist for NEW complex opcode dirs -------------------
echo
echo "== ADVISORY: new complex opcode dirs missing template essentials =="
new_dirs=()
if (( REPORT )); then
  for d in "$OPDIR"/*/; do d="${d%/}"; is_complex "$d" && new_dirs+=("$d"); done
elif [[ -z "$BASE" && -z "${GITHUB_BASE_REF:-}" && -n "${GITHUB_EVENT_NAME:-}" && "${GITHUB_EVENT_NAME}" != "pull_request" ]]; then
  # Non-PR CI event (push / merge_group): there is no PR base to diff against,
  # so the diff-scoped advisory checklist is meaningless — skip it (and its
  # network fetch). The HARD AddrNorm pairing above already ran. (Locally,
  # GITHUB_EVENT_NAME is unset, so the checklist still runs vs origin/main.)
  echo "  (non-PR event ${GITHUB_EVENT_NAME}; new-dir checklist skipped — advisory)"
else
  if [[ -z "$BASE" ]]; then
    BASE="origin/${GITHUB_BASE_REF:-}"; [[ "$BASE" == "origin/" ]] && BASE="origin/main"
  fi
  if ! git rev-parse --verify --quiet "$BASE^{commit}" >/dev/null; then
    git fetch --no-tags --depth=200 origin "${BASE#origin/}" >/dev/null 2>&1 || true
  fi
  if ! git rev-parse --verify --quiet "$BASE^{commit}" >/dev/null; then
    echo "  (base ref '$BASE' unavailable; skipping new-dir checklist — advisory)"
  else
    MB="$(git merge-base "$BASE" HEAD 2>/dev/null || echo "$BASE")"
    # opcode dirs that appear in the diff and didn't exist at the merge base
    while IFS= read -r op; do
      d="$OPDIR/$op"
      [[ -d "$d" ]] || continue
      is_complex "$d" || continue
      if ! git cat-file -e "$MB:$OPDIR/$op/Program.lean" 2>/dev/null \
         && ! git ls-tree -r --name-only "$MB" -- "$OPDIR/$op" 2>/dev/null | grep -q .; then
        new_dirs+=("$d")
      fi
    done < <(git diff --name-only "$MB"...HEAD -- "$OPDIR" 2>/dev/null \
              | sed -nE "s#^$OPDIR/([^/]+)/.*#\1#p" | sort -u)
  fi
fi

checklist_hits=0
for d in "${new_dirs[@]:-}"; do
  [[ -z "$d" ]] && continue
  missing=()
  has_fullpath "$d"          || missing+=("FullPath spec")
  has_irreducible_post "$d"  || missing+=("@[irreducible] Post def")
  has_offsets "$d"           || missing+=("Compose/Offsets.lean")
  if (( ${#missing[@]} > 0 )); then
    echo "  $d (complex): consider adding — $(IFS=', '; echo "${missing[*]}")"
    checklist_hits=$((checklist_hits + 1))
  elif (( REPORT )); then
    echo "  $d (complex): all essentials present"
  fi
done
(( checklist_hits == 0 )) && echo "  (no new complex opcode dirs missing essentials)"

# ---- verdict ----------------------------------------------------------
echo
if (( REPORT )); then
  echo "check-opcode-structure: pairing-violations=$pair_viol (report mode, exit 0)"
  exit 0
fi
if (( pair_viol > 0 )); then
  cat >&2 <<EOF
==================================================================
check-opcode-structure FAILED: $pair_viol AddrNorm pairing violation(s).
AddrNorm.lean and AddrNormAttr.lean must co-occur — Lean forbids using
a register_simp_attr in its declaring file, so the attribute MUST live
in its own AddrNormAttr.lean. Add the missing half (copy the canonical
EvmAsm/Evm64/Exp/AddrNorm*.lean pair) or remove the stray file.
==================================================================
EOF
  exit 1
fi
echo "check-opcode-structure: AddrNorm pairing holds. OK. (checklist above is advisory)"
exit 0
