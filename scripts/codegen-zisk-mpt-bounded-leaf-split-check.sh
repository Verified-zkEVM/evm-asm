#!/usr/bin/env bash
# Canonical divergent-leaf insertion KAT for sd13v's bounded state-root walk.
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
def leaf(first, value):
    # Even leaf HP path: one leading state-key nibble followed by 63 zeroes.
    return b'\xe3\xa1\x20' + bytes([first << 4]) + b'\0' * 31 + value
def branch(children):
    payload = b''.join(b'\xa0' + h if h is not None else b'\x80' for h in children) + b'\x80'
    return b'\xf8' + bytes([len(payload)]) + payload

old = leaf(0, b'\x80')
# After splitting the first nibble, both child leaves retain 63 zero nibbles.
new = b'\xe2\xa0\x30' + b'\0' * 31 + b'\x01'
old_child = b'\xe2\xa0\x30' + b'\0' * 31 + b'\x80'
expected = branch([keccak256(old_child), keccak256(new)] + [None] * 14)
empty = Bytes(b'')
old_spec = LeafNode(Bytes([0] * 64), empty)
old_child_spec = LeafNode(Bytes([0] * 63), empty)
new_child_spec = LeafNode(Bytes([0] * 63), Bytes(b'\x01'))
expected_spec = BranchNode(
    (encode_internal_node(old_child_spec), encode_internal_node(new_child_spec)) + (b'',) * 14,
    empty,
)
assert keccak256(old) == bytes(encode_internal_node(old_spec))
assert keccak256(expected) == bytes(encode_internal_node(expected_spec))
section = struct.pack('<I', 4) + old
key = bytes([1]) + b'\0' * 63
blob = (struct.pack('<Q', len(section)) + keccak256(old) + key +
        struct.pack('<Q', 1) + b'\x01' + b'\0' * 7 + struct.pack('<Q', 1) + section)
(root / 'input').write_bytes(blob + b'\0' * (-len(blob) % 8))
(root / 'expected').write_bytes(bytes(encode_internal_node(expected_spec)))
PY
"$ZISKEMU" -e "$workdir/root.elf" -i "$workdir/input" -o "$workdir/output" -n 3000000 >/dev/null </dev/null
python3 - "$workdir" <<'PY'
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1]); out = (root / 'output').read_bytes()
status = struct.unpack_from('<Q', out)[0]
assert status == 0, status
assert out[8:40] == (root / 'expected').read_bytes(), out[8:40].hex()
print('PASS: bounded builder splits a divergent leaf canonically')
PY
