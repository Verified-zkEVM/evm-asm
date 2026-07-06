#!/usr/bin/env bash
# codegen-zisk-mpt-node-classify-check.sh -- PR-K111.
#
# Classify MPT node: 0=branch, 1=extension, 2=leaf.
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else
    echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2
    exit 1
  fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_mpt_node_classify ELF"
lake exe codegen --program zisk_mpt_node_classify --halt linux93 \
  -o gen-out/zisk_mpt_node_classify

REPO_ROOT="$(pwd)"

# run_case <name> <kind> <node_kind_for_python> [extra_args]
# kind: "branch", "leaf", "extension", "invalid_3item"
run_case() {
  local name="$1" k="$2" exp="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_node_classify_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_node_classify_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
from ethereum.merkle_patricia_trie import nibble_list_to_compact

k = '$k'
if k == 'branch':
    # 17-item branch
    children = [b''] * 16
    node = children + [b'value']
elif k == 'branch_with_children':
    children = [bytes([0x99]*32)] * 16
    node = children + [b'value']
elif k == 'leaf_short':
    path = nibble_list_to_compact(bytes([1, 2, 3]), True)
    node = [path, b'value']
elif k == 'leaf_long':
    path = nibble_list_to_compact(bytes(range(16)), True)
    node = [path, bytes(range(80))]
elif k == 'leaf_even':
    path = nibble_list_to_compact(bytes([1, 2, 3, 4]), True)
    node = [path, b'value']
elif k == 'ext_short':
    path = nibble_list_to_compact(bytes([1, 2]), False)
    node = [path, bytes([0x88]*32)]
elif k == 'ext_long':
    path = nibble_list_to_compact(bytes(range(16)), False)
    node = [path, bytes([0x99]*32)]
elif k == 'ext_even':
    path = nibble_list_to_compact(bytes([1, 2]), False)
    node = [path, bytes([0xaa]*32)]
elif k == 'invalid_3item':
    node = [b'a', b'b', b'c']
elif k == 'invalid_1item':
    node = [b'a']
elif k == 'invalid_18item':
    node = [b''] * 18
else:
    raise ValueError(k)

node_rlp = rlp.encode(node)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(node_rlp)))
    f.write(node_rlp)
    pad = (-(8 + len(node_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_node_classify.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_node_classify_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_kind_le; actual_kind_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_kind; actual_kind="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_kind_le'))[0])")"

  if [[ "$exp" == "invalid" ]]; then
    if [[ "$actual_status" == "0100000000000000" ]]; then
      printf "  %-32s OK   status=1 (invalid as expected)\n" "$name"
      return 0
    else
      printf "  %-32s FAIL expected invalid status=1 got 0x%s kind=%d\n" "$name" "$actual_status" "$actual_kind"
      return 1
    fi
  fi
  if [[ "$actual_status" == "0000000000000000" && "$actual_kind" == "$exp" ]]; then
    printf "  %-32s OK   kind=%d\n" "$name" "$exp"
    return 0
  else
    printf "  %-32s FAIL status=0x%s kind=%d expected=%d\n" "$name" "$actual_status" "$actual_kind" "$exp"
    return 1
  fi
}

FAILED=0
run_case "branch_empty"        branch                  0 || FAILED=1
run_case "branch_with_kids"    branch_with_children    0 || FAILED=1
run_case "leaf_short"          leaf_short              2 || FAILED=1
run_case "leaf_long"           leaf_long               2 || FAILED=1
run_case "leaf_even"           leaf_even               2 || FAILED=1
run_case "ext_short"           ext_short               1 || FAILED=1
run_case "ext_long"            ext_long                1 || FAILED=1
run_case "ext_even"            ext_even                1 || FAILED=1
run_case "invalid_3item"       invalid_3item           invalid || FAILED=1
run_case "invalid_1item"       invalid_1item           invalid || FAILED=1
run_case "invalid_18item"      invalid_18item          invalid || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_node_classify identifies branch/extension/leaf nodes"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
