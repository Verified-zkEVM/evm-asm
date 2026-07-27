#!/usr/bin/env bash
# Every working-RAM anchor declared in MemoryLayout must have a corresponding
# entry in RegionMap's schemeAAnchors base list.
#
# Why this exists: three anchors (STORAGE_WRITES_AREA, TX_STORAGE_WRITES_AREA,
# STORAGE_WRITES_UNDO_AREA) were silently dropped from RegionMap by a merge
# resolution while their constants and the guest's use of the addresses remained.
# The result was three in-use RAM regions with no pairwise-disjointness and no
# zone-fit proof, and NOTHING objected: check-region-map.sh compares the
# DECLARED map against the ELF, so a region that is not declared is not checked.
# This script asserts the missing invariant -- declaration implies coverage.
set -uo pipefail
cd "$(dirname "$0")/.."

LAYOUT=EvmAsm/Stateless/MemoryLayout.lean
REGIONS=EvmAsm/Codegen/RegionMap.lean
[[ -f $LAYOUT && -f $REGIONS ]] || { echo "missing $LAYOUT or $REGIONS" >&2; exit 2; }

# Anchors are `def NAME : Word := 0x...` in MemoryLayout. STATELESS_WORK_BASE is a
# base reference rather than a region, and the SSZ scratch pair is covered by its
# own dedicated theorem (sszScratch_matches_layout), so both are exempt.
mapfile -t anchors < <(
  grep -oE '^def [A-Z][A-Z0-9_]*[[:space:]]*:[[:space:]]*Word' "$LAYOUT" \
    | awk '{print $2}' \
    | grep -vE '^(STATELESS_WORK_BASE|SSZ_SCRATCH_BASE|SSZ_SCRATCH_SIZE)$' \
    | sort -u
)

(( ${#anchors[@]} > 0 )) || { echo "no anchors parsed from $LAYOUT -- selector is stale" >&2; exit 2; }

missing=()
for a in "${anchors[@]}"; do
  grep -qE "EvmAsm\.Stateless\.$a\b" "$REGIONS" || missing+=("$a")
done

echo "MemoryLayout anchors checked: ${#anchors[@]}"
if (( ${#missing[@]} )); then
  echo "MISSING from RegionMap (declared, but no region entry -> no disjointness/fit proof):" >&2
  for m in "${missing[@]}"; do echo "  $m" >&2; done
  echo "check-memorylayout-region-coverage: FAIL (${#missing[@]} uncovered)" >&2
  exit 1
fi
echo "check-memorylayout-region-coverage: every anchor has a RegionMap entry"
