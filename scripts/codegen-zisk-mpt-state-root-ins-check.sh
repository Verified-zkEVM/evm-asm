#!/usr/bin/env bash
# codegen-zisk-mpt-state-root-ins-check.sh -- verify mpt_state_root_ins (bead
# evm-asm-fhsxz.2.4.2.6.3): the insert-aware multi-change driver. The vector is
# a MODIFY of an existing key followed by an INSERT into an empty branch slot,
# plus a focused no-op/modify/delete descriptor-mode case. The insert/delete
# paths must resolve modified roots from the appendable node DB.
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
echo "==> generate vectors"
uv run --directory execution-specs --quiet python3 "$REPO_ROOT/scripts/mpt_ref.py" "$VDIR"
echo "==> lake build codegen"; lake build codegen >/dev/null
echo "==> emit zisk_mpt_state_root_ins probe ELF"
lake exe codegen --program zisk_mpt_state_root_ins --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_mpt_state_root_ins"
read_u64() { od -An -tu8 -j "$2" -N 8 "$1" | tr -d ' \n'; }
fail=0
for name in state_root_ins state_root_ins_deep state_root_ins_dbchild state_root_ins_delete_noop; do
  out="$VDIR/$name.sri.output"
  if ! "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_mpt_state_root_ins.elf" \
        -i "$VDIR/$name.input" -o "$out" -n 8000000 >/dev/null 2>&1 </dev/null; then
    echo "  ERROR  $name (ziskemu)"; fail=1; continue
  fi
  st="$(read_u64 "$out" 32)"
  act="$(od -An -tx1 -j 0 -N 32 "$out" | tr -d ' \n')"
  exp="$(cat "$VDIR/$name.expected")"
  if [[ "$st" == "0" && "$act" == "$exp" ]]; then
    echo "  PASS   $name  root=${act:0:16}.."
  else
    echo "  FAIL   $name  status=$st"; echo "    exp $exp"; echo "    got $act"; fail=1
  fi
done
[[ "$fail" -eq 0 ]] && echo "==> PASS: mpt_state_root_ins matches reference" || { echo "==> FAIL"; exit 1; }
