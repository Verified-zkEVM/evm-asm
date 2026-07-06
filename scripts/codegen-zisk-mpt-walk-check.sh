#!/usr/bin/env bash
# codegen-zisk-mpt-walk-check.sh -- PR-K24.
#
# End-to-end MPT walk: root_hash + witness + path → value.
#
# Test fixtures build synthetic MPTs via Python and check the
# resulting walk matches an explicit (status, value) expectation.
# Covers:
#   * Single-leaf MPT (root is a leaf node) -- found / not found.
#   * 2-leaf MPT joined by a branch node.
#   * Extension + branch + leaf (3-level path).
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

echo "==> emit zisk_mpt_walk ELF"
lake exe codegen --program zisk_mpt_walk --halt linux93 \
  -o gen-out/zisk_mpt_walk

REPO_ROOT="$(pwd)"

# Build SSZ list section from list of element-byte-strings.
build_ssz_section() {
  python3 -c "
import struct, sys
elements = [bytes.fromhex(a) for a in sys.argv[1:]]
n = len(elements)
if n == 0:
    sys.stdout.write('')
    sys.exit(0)
section = b''
offset = 4 * n
for e in elements:
    section += struct.pack('<I', offset)
    offset += len(e)
for e in elements:
    section += e
sys.stdout.write(section.hex())
" "$@"
}

run_case() {
  local name="$1" path_hex="$2" root_hash_hex="$3" \
        witness_hex="$4" expected_status="$5" expected_value_hex="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_walk_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_walk_${name}.output"

  python3 -c "
import struct, sys
path = bytes.fromhex('$path_hex')
root_hash = bytes.fromhex('$root_hash_hex')
witness = bytes.fromhex('$witness_hex')
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(witness)))   # witness_len
    f.write(struct.pack('<Q', len(path)))      # path_len
    f.write(root_hash)                         # 32 bytes
    f.write(path)
    f.write(witness)
    total = 8 + 8 + 32 + len(path) + len(witness)
    pad = (-total) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_walk.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_walk_${name}.emu.log" 2>&1 || true

  local actual_status actual_value_len actual_value
  actual_status="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  actual_value_len="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_value_byte_count=$(( ${#expected_value_hex} / 2 ))
  if (( exp_value_byte_count > 0 )); then
    actual_value="$(dd if="$out_file" bs=1 skip=16 count="$exp_value_byte_count" 2>/dev/null | xxd -p | tr -d '\n')"
  else
    actual_value=""
  fi

  local exp_status_le exp_value_len_le
  exp_status_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"
  exp_value_len_le="$(python3 -c "print(int('$exp_value_byte_count').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" && \
        "$actual_value_len" == "$exp_value_len_le" && \
        "$actual_value" == "$expected_value_hex" ]]; then
    printf "  %-26s OK   status=%d len=%d value=%s\n" \
      "$name" "$expected_status" "$exp_value_byte_count" "$expected_value_hex"
    return 0
  else
    printf "  %-26s FAIL\n    expected: status=%d len=%d value=%s\n    actual:   status=0x%s len=0x%s value=%s\n" \
      "$name" "$expected_status" "$exp_value_byte_count" "$expected_value_hex" \
      "$actual_status" "$actual_value_len" "$actual_value"
    return 1
  fi
}

# Python helpers: build MPT nodes + the witness section.
PY_HELPERS=$(cat <<'EOF'
from Crypto.Hash import keccak
import rlp

def k256(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

def hp_encode(nibbles, is_leaf):
    flag = 2 if is_leaf else 0
    if len(nibbles) % 2 == 1:
        flag |= 1
        result = bytes([flag * 0x10 + nibbles[0]])
        nibbles = nibbles[1:]
    else:
        result = bytes([flag * 0x10])
    for i in range(0, len(nibbles), 2):
        result += bytes([nibbles[i] * 0x10 + nibbles[i+1]])
    return result

def leaf_node(path_nibbles, value):
    return rlp.encode([hp_encode(path_nibbles, True), value])

def extension_node(path_nibbles, child_ref):
    # child_ref is a bytes object (either 32-byte hash or inlined RLP)
    return rlp.encode([hp_encode(path_nibbles, False), child_ref])

def branch_node(children, value=b''):
    # children: list of 16 entries, each either bytes (hash or inlined) or b''
    items = list(children) + [value]
    return rlp.encode(items)
EOF
)

FAILED=0

# Fixture 1: 1-leaf MPT, path matches.
F1=$(uv run --directory execution-specs --quiet python3 -c "
$PY_HELPERS
leaf = leaf_node([1, 2, 3, 4], b'hello')
root_hash = k256(leaf)
print('LEAF', leaf.hex())
print('ROOT', root_hash.hex())
")
LEAF_HEX=$(echo "$F1" | grep '^LEAF ' | awk '{print $2}')
ROOT_HEX=$(echo "$F1" | grep '^ROOT ' | awk '{print $2}')
WITNESS_HEX=$(build_ssz_section "$LEAF_HEX")
run_case "leaf_match"    "01020304" "$ROOT_HEX" "$WITNESS_HEX" 0 "68656c6c6f"  || FAILED=1

# Fixture 2: 1-leaf MPT, path doesn't match.
run_case "leaf_no_match" "01020305" "$ROOT_HEX" "$WITNESS_HEX" 1 ""            || FAILED=1

# Fixture 3: 2-leaf MPT with branch root.
F2=$(uv run --directory execution-specs --quiet python3 -c "
$PY_HELPERS
# Two leaves, each with 1-nibble paths under different branch slots.
# Path: nibble0 = 3 → leaf with remaining path [a, b]
#       nibble0 = 7 → leaf with remaining path [c, d]
leaf_a = leaf_node([0xa, 0xb], b'apple')
leaf_b = leaf_node([0xc, 0xd], b'banana')
# These leaves are < 32 bytes? Let's compute.
# leaf_a: HP([a,b], leaf, even) = 0x20 0xab (2 bytes). Plus value 'apple' (5 bytes) RLP = 6 bytes.
#   Inner RLP: 0x82 0x20 0xab (3 bytes), 0x85 'apple' (6 bytes). Outer: 0xc9 (1+9=10 bytes). Total 10 bytes.
# leaf_b similar.
# Each leaf is 10 bytes < 32, so they're inlined in the branch.
children = [b''] * 16
children[3] = leaf_a   # inlined
children[7] = leaf_b
branch = branch_node(children)
root_hash = k256(branch)
print('BRANCH', branch.hex())
print('LEAFA', leaf_a.hex())
print('LEAFB', leaf_b.hex())
print('ROOT', root_hash.hex())
")
BRANCH_HEX=$(echo "$F2" | grep '^BRANCH ' | awk '{print $2}')
ROOT2_HEX=$(echo "$F2" | grep '^ROOT ' | awk '{print $2}')
WITNESS2_HEX=$(build_ssz_section "$BRANCH_HEX")
# Path = 3, a, b → should find 'apple' (path nibbles: 0x3, 0xa, 0xb)
run_case "branch_slot3"  "030a0b" "$ROOT2_HEX" "$WITNESS2_HEX" 0 "6170706c65"   || FAILED=1
# Path = 7, c, d → should find 'banana'
run_case "branch_slot7"  "070c0d" "$ROOT2_HEX" "$WITNESS2_HEX" 0 "62616e616e61" || FAILED=1
# Path = 5, ... → empty slot
run_case "branch_empty5" "050000" "$ROOT2_HEX" "$WITNESS2_HEX" 1 ""             || FAILED=1

# Fixture 4: 2-leaf MPT where branch's leaves are LARGE (> 32 bytes) so they're stored by hash.
F4=$(uv run --directory execution-specs --quiet python3 -c "
$PY_HELPERS
leaf_a = leaf_node([0xa, 0xb], b'apple' * 10)   # 50 bytes value
leaf_b = leaf_node([0xc, 0xd], b'banana' * 10)  # 60 bytes value
# These leaves are > 32 bytes. Branch stores their hashes.
hash_a = k256(leaf_a)
hash_b = k256(leaf_b)
children = [b''] * 16
children[3] = hash_a
children[7] = hash_b
branch = branch_node(children)
root_hash = k256(branch)
print('BRANCH', branch.hex())
print('LEAFA', leaf_a.hex())
print('LEAFB', leaf_b.hex())
print('ROOT', root_hash.hex())
")
BRANCH4_HEX=$(echo "$F4" | grep '^BRANCH ' | awk '{print $2}')
LEAFA4_HEX=$(echo "$F4" | grep '^LEAFA ' | awk '{print $2}')
LEAFB4_HEX=$(echo "$F4" | grep '^LEAFB ' | awk '{print $2}')
ROOT4_HEX=$(echo "$F4" | grep '^ROOT ' | awk '{print $2}')
WITNESS4_HEX=$(build_ssz_section "$BRANCH4_HEX" "$LEAFA4_HEX" "$LEAFB4_HEX")
# Path = 3, a, b → 'apple' * 10
APPLE10_HEX=$(python3 -c "print((b'apple' * 10).hex())")
BANANA10_HEX=$(python3 -c "print((b'banana' * 10).hex())")
run_case "branch_hash3"  "030a0b" "$ROOT4_HEX" "$WITNESS4_HEX" 0 "$APPLE10_HEX"  || FAILED=1
run_case "branch_hash7"  "070c0d" "$ROOT4_HEX" "$WITNESS4_HEX" 0 "$BANANA10_HEX" || FAILED=1
# If a branch points to a hashed child, that child must be present in the
# witness. This is a malformed proof, not a valid absence proof.
WITNESS4_MISSING_CHILD_HEX=$(build_ssz_section "$BRANCH4_HEX")
run_case "branch_hash_missing_child" "030a0b" "$ROOT4_HEX" "$WITNESS4_MISSING_CHILD_HEX" 2 "" || FAILED=1

# Fixture 5: 3-level MPT with extension. Path: [1,2,3,4,5,6,7]
# Extension at root with path [1,2,3], child = branch
# Branch at slot 4 has leaf with path [5,6,7]
F5=$(uv run --directory execution-specs --quiet python3 -c "
$PY_HELPERS
leaf = leaf_node([5, 6, 7], b'deeply')
# leaf size?
leaf_size = len(leaf)
# If leaf > 32 bytes, branch stores its hash; else inlines.
# leaf: HP([5,6,7]) = 0x35 (odd leaf, first nibble 5) + 0x67 = 0x35 0x67 (2 bytes).
# Item 0: 0x82 0x35 0x67 (3 bytes). Item 1: 0x86 'deeply' (7 bytes). Payload 10. Outer 0xca (1+10=11 bytes).
children = [b''] * 16
children[4] = leaf if leaf_size > 32 else leaf
branch = branch_node(children)
# branch size? 16 × 0x80 (16) + leaf (11) + 0x80 (1) = 28 payload. Outer 0xdc + 28 = 29 bytes.
branch_size = len(branch)
# If branch > 32, ext stores hash; else inlines.
ext_child = branch  # inlined since branch_size is likely 29 < 32
ext = extension_node([1, 2, 3], ext_child)
root_hash = k256(ext)
print('EXT', ext.hex())
print('BRANCH', branch.hex())
print('LEAF', leaf.hex())
print('LEAFSZ', leaf_size)
print('BRANCHSZ', branch_size)
print('ROOT', root_hash.hex())
")
EXT_HEX=$(echo "$F5" | grep '^EXT ' | awk '{print $2}')
ROOT5_HEX=$(echo "$F5" | grep '^ROOT ' | awk '{print $2}')
WITNESS5_HEX=$(build_ssz_section "$EXT_HEX")
# Path = 1,2,3,4,5,6,7 → 'deeply'
run_case "ext_branch_leaf" "01020304050607" "$ROOT5_HEX" "$WITNESS5_HEX" 0 "646565706c79" || FAILED=1
# Wrong path → not found
run_case "ext_no_match"    "01020305050607" "$ROOT5_HEX" "$WITNESS5_HEX" 1 ""             || FAILED=1

# Fixture 6: empty witness → not found.
ZERO_HASH="0000000000000000000000000000000000000000000000000000000000000000"
run_case "empty_witness"   "01020304" "$ZERO_HASH" "" 1 ""                                || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_walk handles every MPT shape end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
