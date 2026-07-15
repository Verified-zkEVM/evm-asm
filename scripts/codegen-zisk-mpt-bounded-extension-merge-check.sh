#!/usr/bin/env bash
# Canonical extension-child merge KAT for sd13v's bounded state-root walk.
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
def leaf_60(value):
    return b'\xe1\x9f\x20' + b'\0' * 30 + value
def leaf_62(value):
    return b'\xe2\xa0\x20' + b'\0' * 31 + value
def extension_1(child):
    return b'\xe2\x10\xa0' + keccak256(child)
def branch(children):
    slots = [b'\xa0' + h if h is not None else b'\x80' for h in children]
    payload = b''.join(slots) + b'\x80'
    return b'\xf8' + bytes([len(payload)]) + payload

# root extension [0] -> branch; branch child 0 is extension [0] -> branch,
# and deleting child 1 makes it collapse to extension [0,0].  Both extension
# nodes are canonical because their child is a branch.  The parent must merge
# to extension [0,0,0], rather than encoding extension->extension.
deep0, deep1 = leaf_60(b'\x80'), leaf_60(b'\x80')
deep_branch = branch([keccak256(deep0), keccak256(deep1)] + [None] * 14)
old_child0 = extension_1(deep_branch)
old_child1 = leaf_62(b'\x80')
old_branch = branch([keccak256(old_child0), keccak256(old_child1)] + [None] * 14)
old_root = extension_1(old_branch)
expected = b'\xe4\x82\x10\x00\xa0' + keccak256(deep_branch)
empty = Bytes(b'')
deep0_spec = LeafNode(Bytes([0] * 60), empty)
deep1_spec = LeafNode(Bytes([0] * 60), empty)
deep_branch_spec = BranchNode(
    (encode_internal_node(deep0_spec), encode_internal_node(deep1_spec)) + (b'',) * 14,
    empty,
)
child_extension_spec = ExtensionNode(Bytes([0]), encode_internal_node(deep_branch_spec))
child1_spec = LeafNode(Bytes([0] * 62), empty)
old_branch_spec = BranchNode(
    (encode_internal_node(child_extension_spec), encode_internal_node(child1_spec)) + (b'',) * 14,
    empty,
)
old_root_spec = ExtensionNode(Bytes([0]), encode_internal_node(old_branch_spec))
merged_spec = ExtensionNode(Bytes([0, 0, 0]), encode_internal_node(deep_branch_spec))
assert keccak256(old_root) == bytes(encode_internal_node(old_root_spec))
assert keccak256(expected) == bytes(encode_internal_node(merged_spec))
nodes = [old_root, old_branch, old_child0, old_child1, deep_branch, deep0, deep1]
offsets, cursor = [], 4 * len(nodes)
for node in nodes:
    offsets.append(cursor); cursor += len(node)
section = b''.join(struct.pack('<I', x) for x in offsets) + b''.join(nodes)
key = bytes([0, 1]) + b'\0' * 62
blob = (struct.pack('<Q', len(section)) + keccak256(old_root) + key +
        struct.pack('<Q', 0) + struct.pack('<Q', 2) + section)
(root / 'input').write_bytes(blob + b'\0' * (-len(blob) % 8))
(root / 'expected').write_bytes(bytes(encode_internal_node(merged_spec)))
PY
"$ZISKEMU" -e "$workdir/root.elf" -i "$workdir/input" -o "$workdir/output" -n 3000000 >/dev/null </dev/null
python3 - "$workdir" <<'PY'
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1]); out = (root / 'output').read_bytes()
status = struct.unpack_from('<Q', out)[0]
assert status == 0, status
assert out[8:40] == (root / 'expected').read_bytes(), out[8:40].hex()
print('PASS: bounded builder canonically merges a rebuilt extension child')
PY
