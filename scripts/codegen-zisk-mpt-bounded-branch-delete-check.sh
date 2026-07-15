#!/usr/bin/env bash
# Deleting one child of a three-child branch must retain a canonical branch.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
workdir="$(mktemp -d)"; trap 'rm -rf "$workdir"' EXIT
bash scripts/codegen-force-relink.sh >/dev/null
lake exe codegen --program zisk_mpt_bounded_state_root --halt linux93 -o "$workdir/root" >/dev/null
uv run --directory execution-specs --quiet python3 - "$workdir" <<'PY'
from ethereum.crypto.hash import keccak256
from ethereum.merkle_patricia_trie import BranchNode, LeafNode, encode_internal_node
from ethereum_types.bytes import Bytes
import pathlib, struct, sys

root = pathlib.Path(sys.argv[1])
def leaf(first): return b'\xe2\xa0' + bytes([0x30 | first]) + b'\0' * 31 + b'\x80'
def branch(children):
    slots = [b'\xa0' + h if h is not None else b'\x80' for h in children]
    payload = b''.join(slots) + b'\x80'
    return b'\xf8' + bytes([len(payload)]) + payload

leaves = [leaf(i) for i in range(3)]
hashes = [keccak256(x) for x in leaves]
old_root = branch(hashes + [None] * 13)
expected = branch([None, hashes[1], hashes[2]] + [None] * 13)
empty = Bytes(b'')
leaf_specs = [LeafNode(Bytes([i] + [0] * 62), empty) for i in range(3)]
old_spec = BranchNode(tuple(encode_internal_node(x) for x in leaf_specs) + (b'',) * 13, empty)
expected_spec = BranchNode(
    (b'', encode_internal_node(leaf_specs[1]), encode_internal_node(leaf_specs[2])) + (b'',) * 13,
    empty,
)
assert keccak256(old_root) == bytes(encode_internal_node(old_spec))
assert keccak256(expected) == bytes(encode_internal_node(expected_spec))
nodes = [old_root] + leaves
offsets, cursor = [], 4 * len(nodes)
for node in nodes:
    offsets.append(cursor); cursor += len(node)
section = b''.join(struct.pack('<I', x) for x in offsets) + b''.join(nodes)
key = b'\0' * 64
blob = (struct.pack('<Q', len(section)) + keccak256(old_root) + key +
        struct.pack('<Q', 0) + b'\0' * 8 + struct.pack('<Q', 2) + section)
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
print('PASS: bounded builder deletes a branch child without collapse')
PY
