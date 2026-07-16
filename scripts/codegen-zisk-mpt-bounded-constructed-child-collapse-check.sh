#!/usr/bin/env bash
# A branch collapse must reopen a freshly constructed hashed child, not look
# it up in the immutable witness.  Delete root child 0 while updating a leaf
# below root child 1; the rebuilt child branch is hash-referenced and becomes
# the sole survivor.
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
def leaf_63(first, value):
    return b'\xe2\xa0' + bytes([0x30 | first]) + b'\0' * 31 + value
def leaf_62(value):
    return b'\xe2\xa0\x20' + b'\0' * 31 + value

# Canonical old trie: root child 0 is a leaf; root child 1 is a branch with
# two leaves.  Both branches and leaves are hashed witness references.
old0 = leaf_63(0, b'\x80')
old10, old11 = leaf_62(b'\x80'), leaf_62(b'\x80')
old1 = branch([keccak256(old10), keccak256(old11)] + [None] * 14)
old_root = branch([keccak256(old0), keccak256(old1)] + [None] * 14)

old0_spec = LeafNode(Bytes([0] * 63), empty)
old10_spec = LeafNode(Bytes([0] * 62), empty)
old11_spec = LeafNode(Bytes([0] * 62), empty)
old1_spec = BranchNode(
    (encode_internal_node(old10_spec), encode_internal_node(old11_spec)) + (b'',) * 14, empty)
old_spec = BranchNode(
    (encode_internal_node(old0_spec), encode_internal_node(old1_spec)) + (b'',) * 14, empty)
assert keccak256(old_root) == bytes(encode_internal_node(old_spec))

# Delete [0, 0, ...] and update [1, 0, ...].  The sole root survivor is the
# newly built (not witness-backed) branch, so canonical collapse wraps it in
# extension [1].
updated10_spec = LeafNode(Bytes([0] * 62), Bytes(b'\x03'))
updated1_spec = BranchNode(
    (encode_internal_node(updated10_spec), encode_internal_node(old11_spec)) + (b'',) * 14, empty)
expected_spec = ExtensionNode(Bytes([1]), encode_internal_node(updated1_spec))
expected = bytes(encode_internal_node(expected_spec))
assert len(expected) == 32

nodes = [old_root, old0, old1, old10, old11]
offsets, cursor = [], 4 * len(nodes)
for node in nodes:
    offsets.append(cursor); cursor += len(node)
section = b''.join(struct.pack('<I', x) for x in offsets) + b''.join(nodes)
key_delete = b'\0' * 64
key_update = bytes([1, 0]) + b'\0' * 62
blob = (struct.pack('<Q', len(section)) + keccak256(old_root) +
        key_delete + b'\0' * 8 + key_update + b'\x03' + b'\0' * 7 +
        struct.pack('<QQ', 2, 0) + section)
(root / 'input').write_bytes(blob + b'\0' * (-len(blob) % 8))
(root / 'expected').write_bytes(expected)
PY
"$ZISKEMU" -e "$workdir/root.elf" -i "$workdir/input" -o "$workdir/output" -n 5000000 >/dev/null </dev/null
python3 - "$workdir" <<'PY'
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1]); out = (root / 'output').read_bytes()
assert struct.unpack_from('<Q', out)[0] == 0
assert out[8:40] == (root / 'expected').read_bytes(), out[8:40].hex()
print('PASS: bounded builder collapses to a freshly constructed hashed child')
PY
