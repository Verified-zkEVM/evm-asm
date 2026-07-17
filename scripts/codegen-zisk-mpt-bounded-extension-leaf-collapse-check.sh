#!/usr/bin/env bash
# Deleting one child below an extension must merge extension + surviving leaf.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
EXECUTION_SPECS_DIR="${EXECUTION_SPECS_DIR:-execution-specs}"
workdir="$(mktemp -d)"; trap 'rm -rf "$workdir"' EXIT
bash scripts/codegen-force-relink.sh >/dev/null
lake exe codegen --program zisk_mpt_bounded_missing_group --halt linux93 -o "$workdir/root" >/dev/null
uv run --directory "$EXECUTION_SPECS_DIR" --quiet python3 - "$workdir" <<'PY'
from ethereum.crypto.hash import keccak256
from ethereum.merkle_patricia_trie import BranchNode, ExtensionNode, LeafNode, encode_internal_node
from ethereum_types.bytes import Bytes
import pathlib, struct, sys

root = pathlib.Path(sys.argv[1]); empty = Bytes(b'')
def branch(children):
    payload = b''.join(b'\xa0' + h if h is not None else b'\x80' for h in children) + b'\x80'
    return b'\xf8' + bytes([len(payload)]) + payload
def ext_one(child_hash):
    return b'\xe2\x10\xa0' + child_hash
def leaf_62(value):
    return b'\xe2\xa0\x20' + b'\0' * 31 + value

# Canonical pre-state: Ext([0]) -> Branch({0: leaf, 1: leaf}).  Delete the
# first leaf.  The canonical post-state is one Leaf([0, 1, ...]), not an
# extension pointing at a leaf.
old0 = leaf_62(b'\x80')
old1 = leaf_62(b'\x01')
old_branch = branch([keccak256(old0), keccak256(old1)] + [None] * 14)
old_root = ext_one(keccak256(old_branch))
old0_spec = LeafNode(Bytes([0] * 62), empty)
old1_spec = LeafNode(Bytes([0] * 62), Bytes(b'\x01'))
old_branch_spec = BranchNode(
    (encode_internal_node(old0_spec), encode_internal_node(old1_spec)) + (b'',) * 14, empty)
old_root_spec = ExtensionNode(Bytes([0]), encode_internal_node(old_branch_spec))
assert keccak256(old_root) == bytes(encode_internal_node(old_root_spec))
expected_spec = LeafNode(Bytes([0, 1] + [0] * 62), Bytes(b'\x02'))
expected = bytes(encode_internal_node(expected_spec))
nodes = [old_root, old_branch, old0, old1]
offsets, cursor = [], 4 * len(nodes)
for node in nodes:
    offsets.append(cursor); cursor += len(node)
section = b''.join(struct.pack('<I', off) for off in offsets) + b''.join(nodes)
deleted_key = bytes([0, 0]) + b'\0' * 62
survivor_key = bytes([0, 1]) + b'\0' * 62
blob = (struct.pack('<Q', len(section)) + keccak256(old_root) +
        deleted_key + b'\0' * 8 + survivor_key + b'\x02' + b'\0' * 7 +
        struct.pack('<QQ', 2, 0) + section)
(root / 'input').write_bytes(blob + b'\0' * (-len(blob) % 8))
(root / 'expected').write_bytes(expected)
PY
"$ZISKEMU" -e "$workdir/root.elf" -i "$workdir/input" -o "$workdir/output" -n 5000000 >/dev/null </dev/null
python3 - "$workdir" <<'PY'
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1]); out = (root / 'output').read_bytes()
status = struct.unpack_from('<Q', out)[0]
assert status == 0, status
assert out[8:40] == (root / 'expected').read_bytes(), out[8:40].hex()
print('PASS: bounded builder merges an extension with its collapsed leaf child')
PY
