#!/usr/bin/env bash
# Deleting one root child must wrap a surviving branch in a one-nibble extension.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"; [[ -n "$ZISKEMU" ]] || exit 1
workdir="$(mktemp -d)"; trap 'rm -rf "$workdir"' EXIT
bash scripts/codegen-force-relink.sh >/dev/null
lake exe codegen --program zisk_mpt_bounded_state_root --halt linux93 -o "$workdir/root" >/dev/null
uv run --directory execution-specs --quiet python3 - "$workdir" <<'PY'
from ethereum.crypto.hash import keccak256
from ethereum.merkle_patricia_trie import BranchNode, ExtensionNode, LeafNode, encode_internal_node
from ethereum_types.bytes import Bytes
import pathlib,struct,sys
r=pathlib.Path(sys.argv[1])
def leaf_63(n): return b'\xe2\xa0'+bytes([0x30|n])+b'\0'*31+b'\x80'
def leaf_62(): return b'\xe2\xa0\x20'+b'\0'*31+b'\x80'
def branch(xs):
 p=b''.join(b'\xa0'+x if x else b'\x80' for x in xs)+b'\x80';return b'\xf8'+bytes([len(p)])+p
deleted=leaf_63(0); a,b=leaf_62(),leaf_62(); child=branch([None,None,keccak256(a),keccak256(b)]+[None]*12)
old=branch([keccak256(deleted),keccak256(child)]+[None]*14)
expected=b'\xe2\x11\xa0'+keccak256(child)
empty = Bytes(b'')
deleted_spec = LeafNode(Bytes([0] * 63), empty)
survivor_leaf_spec = LeafNode(Bytes([0] * 62), empty)
child_spec = BranchNode(
    (b'', b'', encode_internal_node(survivor_leaf_spec),
     encode_internal_node(survivor_leaf_spec)) + (b'',) * 12,
    empty,
)
old_spec = BranchNode(
    (encode_internal_node(deleted_spec), encode_internal_node(child_spec)) + (b'',) * 14,
    empty,
)
collapsed_spec = ExtensionNode(Bytes([1]), encode_internal_node(child_spec))
assert keccak256(old) == bytes(encode_internal_node(old_spec))
assert keccak256(expected) == bytes(encode_internal_node(collapsed_spec))
nodes=[old,deleted,child,a,b]; offs=[];p=4*len(nodes)
for n in nodes:offs.append(p);p+=len(n)
sec=b''.join(struct.pack('<I',x) for x in offs)+b''.join(nodes)
blob=struct.pack('<Q',len(sec))+keccak256(old)+b'\0'*64+struct.pack('<Q',0)+b'\0'*8+struct.pack('<Q',2)+sec
(r/'input').write_bytes(blob+b'\0'*(-len(blob)%8));(r/'expected').write_bytes(bytes(encode_internal_node(collapsed_spec)))
PY
"$ZISKEMU" -e "$workdir/root.elf" -i "$workdir/input" -o "$workdir/output" -n 5000000 >/dev/null </dev/null
python3 - "$workdir" <<'PY'
import pathlib,struct,sys
r=pathlib.Path(sys.argv[1]);o=(r/'output').read_bytes();assert struct.unpack_from('<Q',o)[0]==0;assert o[8:40]==(r/'expected').read_bytes(),o[8:40].hex();print('PASS: bounded builder collapses a branch to its branch survivor')
PY
