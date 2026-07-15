#!/usr/bin/env bash
# Deleting one of two branch leaves must collapse to the survivor leaf path.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
workdir="$(mktemp -d)"; trap 'rm -rf "$workdir"' EXIT
lake build codegen >/dev/null
lake exe codegen --program zisk_mpt_bounded_state_root --halt linux93 -o "$workdir/root" >/dev/null
uv run --directory execution-specs --quiet python3 - "$workdir" <<'PY'
from ethereum.crypto.hash import keccak256
from ethereum.merkle_patricia_trie import BranchNode, LeafNode, encode_internal_node
from ethereum_types.bytes import Bytes
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1])
def leaf(first): return b'\xe2\xa0' + bytes([0x30 | first]) + b'\0' * 31 + b'\x80'
def branch(children):
    p = b''.join(b'\xa0' + h if h is not None else b'\x80' for h in children) + b'\x80'
    return b'\xf8' + bytes([len(p)]) + p
old0, old1 = leaf(0), leaf(1)
old_root = branch([keccak256(old0), keccak256(old1)] + [None] * 14)
# The survivor's branch digit 1 prefixes its 63-nibble leaf suffix, whose
# first nibble is also 1.  The canonical 64-nibble compact path is therefore
# 0x20, 0x11, then 31 zero bytes.
expected = b'\xe3\xa1\x20\x11' + b'\0' * 31 + b'\x80'
empty = Bytes(b'')
old0_spec = LeafNode(Bytes([0] * 63), empty)
old1_spec = LeafNode(Bytes([1] + [0] * 62), empty)
old_spec = BranchNode(
    (encode_internal_node(old0_spec), encode_internal_node(old1_spec)) + (b'',) * 14,
    empty,
)
collapsed_spec = LeafNode(Bytes([1, 1] + [0] * 62), empty)
assert keccak256(old_root) == bytes(encode_internal_node(old_spec))
assert keccak256(expected) == bytes(encode_internal_node(collapsed_spec))
nodes = [old_root, old0, old1]; offs=[]; pos=4*len(nodes)
for n in nodes: offs.append(pos); pos += len(n)
section = b''.join(struct.pack('<I', x) for x in offs) + b''.join(nodes)
blob = (struct.pack('<Q', len(section)) + keccak256(old_root) + b'\0'*64 +
        struct.pack('<Q', 0) + b'\0'*8 + struct.pack('<Q', 2) + section)
(root/'input').write_bytes(blob + b'\0' * (-len(blob) % 8))
(root/'expected').write_bytes(bytes(encode_internal_node(collapsed_spec)))
PY
"$ZISKEMU" -e "$workdir/root.elf" -i "$workdir/input" -o "$workdir/output" -n 4000000 >/dev/null </dev/null
python3 - "$workdir" <<'PY'
import pathlib,struct,sys
r=pathlib.Path(sys.argv[1]);o=(r/'output').read_bytes();assert struct.unpack_from('<Q',o)[0]==0;assert o[8:40]==(r/'expected').read_bytes(),o[8:40].hex();print('PASS: bounded builder collapses a branch to its leaf survivor')
PY
