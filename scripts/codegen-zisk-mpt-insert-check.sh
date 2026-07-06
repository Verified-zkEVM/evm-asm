#!/usr/bin/env bash
# codegen-zisk-mpt-insert-check.sh -- verify mpt_insert (bead
# evm-asm-fhsxz.2.4.2.6.2): insert a NEW key into a witness-backed MPT and
# recompute the root, against the validated Python reference scripts/mpt_ref.py.
#
# mpt_insert = mpt_insert_walk (classify divergence) + per-case terminal
# restructure + the mpt_set bubble-up. This slice supports EMPTY_TRIE and
# BRANCH_EMPTY_SLOT (depth 0 and depth 1). The probe writes the new 32-byte
# root to OUTPUT+0 and status to OUTPUT+32; we compare both against the
# reference (expected new root, status 0).
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

VDIR="$REPO_ROOT/gen-out/mpt-set"
echo "==> generate vectors via the validated Python reference"
uv run --directory execution-specs --quiet python3 "$REPO_ROOT/scripts/mpt_ref.py" "$VDIR"

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_mpt_insert probe ELF"
lake exe codegen --program zisk_mpt_insert --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_mpt_insert"

read_u64() { od -An -tu8 -j "$2" -N 8 "$1" | tr -d ' \n'; }

fail=0
for name in mi_branch_empty mi_empty_trie mi_ext_then_branch mi_ext_split \
            mi_leaf_split mi_leaf_split_m0 mi_depth2 mi_leafsplit_depth1 \
            mi_acctkey mi_acctkey_f9; do
  out="$VDIR/$name.mi.output"
  if ! "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_mpt_insert.elf" \
        -i "$VDIR/$name.input" -o "$out" -n 5000000 >/dev/null 2>&1 </dev/null; then
    echo "  ERROR  $name (ziskemu)"; fail=1; continue
  fi
  st="$(read_u64 "$out" 32)"
  act="$(od -An -tx1 -j 0 -N 32 "$out" | tr -d ' \n')"
  exp="$(cat "$VDIR/$name.expected")"
  if [[ "$st" == "0" && "$act" == "$exp" ]]; then
    echo "  PASS   $name  root=${act:0:16}.."
  else
    echo "  FAIL   $name  status=$st"
    echo "         expected $exp"
    echo "         got      $act"
    fail=1
  fi
done
[[ "$fail" -eq 0 ]] && echo "==> PASS: mpt_insert matches reference" \
  || { echo "==> FAIL"; exit 1; }
