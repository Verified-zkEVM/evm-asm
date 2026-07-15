#!/usr/bin/env bash
# Multi-slot existing-leaf split KAT for sd13v's bounded state-root walk.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
workdir="$(mktemp -d)"; trap 'rm -rf "$workdir"' EXIT
# Force the code generator itself to relink.  The probe ELF below is always
# new, but a cached `codegen` binary can otherwise retain an old linked guest.
rm -f .lake/build/bin/codegen .lake/build/bin/codegen.hash .lake/build/bin/codegen.trace
lake build codegen >/dev/null
lake exe codegen --program zisk_mpt_bounded_missing_group --halt linux93 -o "$workdir/root" >/dev/null
uv run --directory execution-specs --quiet python3 - "$workdir" <<'PY'
from ethereum.crypto.hash import keccak256
from ethereum.merkle_patricia_trie import BranchNode, LeafNode, encode_internal_node
from ethereum_types.bytes import Bytes
import pathlib, struct, sys

root = pathlib.Path(sys.argv[1])
def leaf_64(value):
    return b'\xe3\xa1\x20' + b'\0' * 32 + value
def leaf_63(value):
    return b'\xe2\xa0\x30' + b'\0' * 31 + value
def branch(children):
    slots = [b'\xa0' + h if h is not None else b'\x80' for h in children]
    payload = b''.join(slots) + b'\x80'
    return b'\xf8' + bytes([len(payload)]) + payload

old = leaf_64(b'\x80')
old_child = leaf_63(b'\x80')
new_root = branch([keccak256(old_child), None, keccak256(leaf_63(b'\x01')),
                   keccak256(leaf_63(b'\x02'))] + [None] * 12)
empty = Bytes(b'')
old_spec = LeafNode(Bytes([0] * 64), empty)
old_child_spec = LeafNode(Bytes([0] * 63), empty)
new2_spec = LeafNode(Bytes([0] * 63), Bytes(b'\x01'))
new3_spec = LeafNode(Bytes([0] * 63), Bytes(b'\x02'))
new_root_spec = BranchNode(
    (encode_internal_node(old_child_spec), b'', encode_internal_node(new2_spec),
     encode_internal_node(new3_spec)) + (b'',) * 12,
    empty,
)
assert keccak256(old) == bytes(encode_internal_node(old_spec))
assert keccak256(new_root) == bytes(encode_internal_node(new_root_spec))
section = struct.pack('<I', 4) + old
key0 = bytes([2]) + b'\0' * 63
key1 = bytes([3]) + b'\0' * 63
blob = (struct.pack('<Q', len(section)) + keccak256(old) + key0 + b'\x01' + b'\0' * 7 +
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
print('PASS: bounded builder splits an existing leaf across multiple new radix slots')
PY
