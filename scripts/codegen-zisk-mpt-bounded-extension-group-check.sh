#!/usr/bin/env bash
# Grouped existing-extension split KAT for sd13v's bounded state-root walk.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
workdir="$(mktemp -d)"; trap 'rm -rf "$workdir"' EXIT
bash scripts/codegen-force-relink.sh >/dev/null
lake exe codegen --program zisk_mpt_bounded_missing_group --halt linux93 -o "$workdir/root" >/dev/null
uv run --directory execution-specs --quiet python3 - "$workdir" <<'PY'
from ethereum.crypto.hash import keccak256
from ethereum.merkle_patricia_trie import (
    BranchNode, ExtensionNode, LeafNode, encode_internal_node,
)
from ethereum_types.bytes import Bytes
import pathlib, struct, sys

root = pathlib.Path(sys.argv[1])
def bstr(value):
    if len(value) == 1 and value[0] < 0x80: return value
    if len(value) < 56: return bytes([0x80 + len(value)]) + value
    n = (len(value).bit_length() + 7) // 8
    return bytes([0xb7 + n]) + len(value).to_bytes(n, 'big') + value
def rlist(items):
    payload = b''.join(items)
    if len(payload) < 56: return bytes([0xc0 + len(payload)]) + payload
    n = (len(payload).bit_length() + 7) // 8
    return bytes([0xf7 + n]) + len(payload).to_bytes(n, 'big') + payload
def hp(path, leaf):
    flag = 2 if leaf else 0
    nibbles = ([flag + 1] if len(path) & 1 else [flag, 0]) + path
    return bytes((nibbles[i] << 4) | nibbles[i + 1] for i in range(0, len(nibbles), 2))
def ref(node): return node if len(node) < 32 else keccak256(node)
def refitem(node): return bstr(ref(node))
def leaf(path, value): return rlist([bstr(hp(path, True)), bstr(value)])
def ext(path, child): return rlist([bstr(hp(path, False)), refitem(child)])
def branch(children):
    return rlist([refitem(child) if child is not None else b'\x80' for child in children] + [b'\x80'])

old_leaf0 = leaf([0] * 61, b'')
old_leaf1 = leaf([1] + [0] * 60, b'')
old_branch = branch([old_leaf0, old_leaf1] + [None] * 14)
old_root = ext([0, 0], old_branch)
new20, new21 = leaf([0] * 61, b'\x01'), leaf([0] * 61, b'\x02')
new2 = branch([new20, new21] + [None] * 14)
split = branch([old_branch, None, new2] + [None] * 13)
new_root = ext([0], split)
empty = Bytes(b'')
old_leaf0_spec = LeafNode(Bytes([0] * 61), empty)
old_leaf1_spec = LeafNode(Bytes([1] + [0] * 60), empty)
old_branch_spec = BranchNode(
    (encode_internal_node(old_leaf0_spec), encode_internal_node(old_leaf1_spec)) + (b'',) * 14,
    empty,
)
old_root_spec = ExtensionNode(Bytes([0, 0]), encode_internal_node(old_branch_spec))
new20_spec = LeafNode(Bytes([0] * 61), Bytes(b'\x01'))
new21_spec = LeafNode(Bytes([0] * 61), Bytes(b'\x02'))
new2_spec = BranchNode(
    (encode_internal_node(new20_spec), encode_internal_node(new21_spec)) + (b'',) * 14,
    empty,
)
split_spec = BranchNode(
    (encode_internal_node(old_branch_spec), b'', encode_internal_node(new2_spec)) + (b'',) * 13,
    empty,
)
new_root_spec = ExtensionNode(Bytes([0]), encode_internal_node(split_spec))
assert keccak256(old_root) == bytes(encode_internal_node(old_root_spec))
assert keccak256(new_root) == bytes(encode_internal_node(new_root_spec))
nodes = [old_root, old_branch, old_leaf0, old_leaf1]
offsets, cursor = [], 4 * len(nodes)
for node in nodes:
    offsets.append(cursor); cursor += len(node)
section = b''.join(struct.pack('<I', offset) for offset in offsets) + b''.join(nodes)
key0 = bytes([0, 2, 0]) + b'\0' * 61
key1 = bytes([0, 2, 1]) + b'\0' * 61
blob = (struct.pack('<Q', len(section)) + keccak256(old_root) + key0 + b'\x01' + b'\0' * 7 +
        key1 + b'\x02' + b'\0' * 7 + section)
(root / 'input').write_bytes(blob + b'\0' * (-len(blob) % 8))
(root / 'expected').write_bytes(bytes(encode_internal_node(new_root_spec)))
PY
"$ZISKEMU" -e "$workdir/root.elf" -i "$workdir/input" -o "$workdir/output" -n 3000000 >/dev/null </dev/null
python3 - "$workdir" <<'PY'
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1]); out = (root / 'output').read_bytes()
status = struct.unpack_from('<Q', out)[0]
assert status == 0, status
assert out[8:40] == (root / 'expected').read_bytes(), out[8:40].hex()
print('PASS: bounded builder splits an existing extension into an old suffix and grouped new subtree')
PY
