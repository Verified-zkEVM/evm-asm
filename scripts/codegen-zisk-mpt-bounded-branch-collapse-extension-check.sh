#!/usr/bin/env bash
# Deleting one branch child must merge its survivor extension's prefix.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"; [[ -n "$ZISKEMU" ]] || exit 1
workdir="$(mktemp -d)"; trap 'rm -rf "$workdir"' EXIT
lake build codegen >/dev/null
lake exe codegen --program zisk_mpt_bounded_state_root --halt linux93 -o "$workdir/root" >/dev/null
uv run --directory execution-specs --quiet python3 - "$workdir" <<'PY'
from ethereum.crypto.hash import keccak256
from ethereum.merkle_patricia_trie import (
    BranchNode, ExtensionNode, LeafNode, encode_internal_node,
)
from ethereum_types.bytes import Bytes
import pathlib,struct,sys
r=pathlib.Path(sys.argv[1])
def branch(xs):
 p=b''.join(b'\xa0'+x if x else b'\x80' for x in xs)+b'\x80';return b'\xf8'+bytes([len(p)])+p
# Canonical pre-state: root child 1 is an extension [2] whose child is a
# branch.  Extension-to-leaf is noncanonical and cannot be a spec-derived
# MPT state.  After deleting root child 0, canonical collapse prefixes the
# survivor branch with [1, 2].
old0=b'\xe2\xa0\x30'+b'\0'*31+b'\x80'
leaf20=b'\xe1\x9f\x30'+b'\0'*30+b'\x80'
leaf21=b'\xe1\x9f\x31'+b'\0'*30+b'\x80'
survivor_branch=branch([keccak256(leaf20),keccak256(leaf21)]+[None]*14)
old_ext=b'\xe2\x12\xa0'+keccak256(survivor_branch)
old=branch([keccak256(old0),keccak256(old_ext)]+[None]*14)
expected=b'\xe4\x82\x00\x12\xa0'+keccak256(survivor_branch)
# Independently derive both commitments through execution-specs' MPT node
# encoder.  This also proves that the hand-written witness nodes are a
# canonical pre-state and that the expected collapsed root is canonical.
empty = Bytes(b'')
def slots(first=None, second=None):
    return (first or b'', second or b'') + (b'',) * 14
old0_spec = LeafNode(Bytes([0] * 63), empty)
leaf20_spec = LeafNode(Bytes([0] * 61), empty)
leaf21_spec = LeafNode(Bytes([1] + [0] * 60), empty)
branch_spec = BranchNode(
    slots(encode_internal_node(leaf20_spec), encode_internal_node(leaf21_spec)), empty)
extension_spec = ExtensionNode(Bytes([2]), encode_internal_node(branch_spec))
old_spec = BranchNode(
    slots(encode_internal_node(old0_spec), encode_internal_node(extension_spec)), empty)
collapsed_spec = ExtensionNode(Bytes([1, 2]), encode_internal_node(branch_spec))
assert keccak256(old) == bytes(encode_internal_node(old_spec))
assert keccak256(expected) == bytes(encode_internal_node(collapsed_spec))
nodes=[old,old0,old_ext,survivor_branch,leaf20,leaf21];o=[];p=4*len(nodes)
for n in nodes:o.append(p);p+=len(n)
sec=b''.join(struct.pack('<I',x) for x in o)+b''.join(nodes)
blob=struct.pack('<Q',len(sec))+keccak256(old)+b'\0'*64+struct.pack('<Q',0)+b'\0'*8+struct.pack('<Q',2)+sec
(r/'input').write_bytes(blob+b'\0'*(-len(blob)%8));(r/'expected').write_bytes(bytes(encode_internal_node(collapsed_spec)))
PY
"$ZISKEMU" -e "$workdir/root.elf" -i "$workdir/input" -o "$workdir/output" -n 4000000 >/dev/null </dev/null
python3 - "$workdir" <<'PY'
import pathlib,struct,sys
r=pathlib.Path(sys.argv[1]);o=(r/'output').read_bytes();assert struct.unpack_from('<Q',o)[0]==0;assert o[8:40]==(r/'expected').read_bytes(),o[8:40].hex();print('PASS: bounded builder collapses a branch to its extension survivor')
PY
