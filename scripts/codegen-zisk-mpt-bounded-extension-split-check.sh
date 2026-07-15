#!/usr/bin/env bash
# Canonical divergent-extension insertion KAT for sd13v's bounded root walk.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
workdir="$(mktemp -d)"; trap 'rm -rf "$workdir"' EXIT
bash scripts/codegen-force-relink.sh >/dev/null
lake exe codegen --program zisk_mpt_bounded_state_root --halt linux93 -o "$workdir/root" >/dev/null
uv run --directory execution-specs --quiet python3 - "$workdir" <<'PY'
from ethereum.crypto.hash import keccak256
from ethereum.merkle_patricia_trie import (
    BranchNode, ExtensionNode, LeafNode, encode_internal_node,
)
from ethereum_types.bytes import Bytes
import pathlib, struct, sys

root = pathlib.Path(sys.argv[1])
def bstr(x):
    if len(x) == 1 and x[0] < 0x80: return x
    if len(x) < 56: return bytes([0x80 + len(x)]) + x
    n = (len(x).bit_length() + 7) // 8
    return bytes([0xb7 + n]) + len(x).to_bytes(n, 'big') + x
def rlist(items):
    p = b''.join(items)
    if len(p) < 56: return bytes([0xc0 + len(p)]) + p
    n = (len(p).bit_length() + 7) // 8
    return bytes([0xf7 + n]) + len(p).to_bytes(n, 'big') + p
def hp(path, leaf):
    flag = 2 if leaf else 0
    if len(path) & 1: ns = [flag + 1] + path
    else: ns = [flag, 0] + path
    return bytes((ns[i] << 4) | ns[i + 1] for i in range(0, len(ns), 2))
def ref(node): return node if len(node) < 32 else keccak256(node)
def refitem(node):
    r = ref(node)
    return r if len(r) < 32 else bstr(r)
def leaf(path, value): return rlist([bstr(hp(path, True)), bstr(value)])
def ext(path, child): return rlist([bstr(hp(path, False)), refitem(child)])
def branch(children):
    return rlist([refitem(c) if c is not None else b'\x80' for c in children] + [b'\x80'])

# Existing extension 000 -> branch is canonical. Insert key 010... diverges
# at the second extension nibble, so the expected root is ext(0, branch(...)).
old_leaf0 = leaf([0] * 60, b'')
old_leaf1 = leaf([1] + [0] * 59, b'')
old_branch = branch([old_leaf0, old_leaf1] + [None] * 14)
old_root = ext([0, 0, 0], old_branch)
old_side = ext([0], old_branch)
new_side = leaf([0] * 62, b'\x01')
expected = ext([0], branch([old_side, new_side] + [None] * 14))
empty = Bytes(b'')
old_leaf0_spec = LeafNode(Bytes([0] * 60), empty)
old_leaf1_spec = LeafNode(Bytes([1] + [0] * 59), empty)
old_branch_spec = BranchNode(
    (encode_internal_node(old_leaf0_spec), encode_internal_node(old_leaf1_spec)) + (b'',) * 14,
    empty,
)
old_root_spec = ExtensionNode(Bytes([0, 0, 0]), encode_internal_node(old_branch_spec))
old_side_spec = ExtensionNode(Bytes([0]), encode_internal_node(old_branch_spec))
new_side_spec = LeafNode(Bytes([0] * 62), Bytes(b'\x01'))
expected_spec = ExtensionNode(
    Bytes([0]),
    encode_internal_node(BranchNode(
        (encode_internal_node(old_side_spec), encode_internal_node(new_side_spec)) + (b'',) * 14,
        empty,
    )),
)
assert keccak256(old_root) == bytes(encode_internal_node(old_root_spec))
assert keccak256(expected) == bytes(encode_internal_node(expected_spec))
nodes = [old_root, old_branch, old_leaf0, old_leaf1]
offsets, cursor = [], 4 * len(nodes)
for node in nodes:
    offsets.append(cursor); cursor += len(node)
section = b''.join(struct.pack('<I', x) for x in offsets) + b''.join(nodes)
key = bytes([0, 1]) + b'\0' * 62
blob = (struct.pack('<Q', len(section)) + keccak256(old_root) + key +
        struct.pack('<Q', 1) + b'\x01' + b'\0' * 7 + struct.pack('<Q', 1) + section)
(root / 'input').write_bytes(blob + b'\0' * (-len(blob) % 8))
(root / 'expected').write_bytes(bytes(encode_internal_node(expected_spec)))
PY
"$ZISKEMU" -e "$workdir/root.elf" -i "$workdir/input" -o "$workdir/output" -n 4000000 >/dev/null </dev/null
python3 - "$workdir" <<'PY'
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1]); out = (root / 'output').read_bytes()
status = struct.unpack_from('<Q', out)[0]
assert status == 0, status
assert out[8:40] == (root / 'expected').read_bytes(), out[8:40].hex()
print('PASS: bounded builder splits a divergent extension canonically')
PY
