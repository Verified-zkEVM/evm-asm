#!/usr/bin/env bash
# Existing-leaf update plus same-radix insertion KAT for sd13v.
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
old_rlp = b'\xe3\xa1\x20' + b'\0' * 32 + b'\x80'
old = LeafNode(Bytes([0] * 64), empty)
old_update = LeafNode(Bytes([0] * 62), Bytes(b'\x03'))
new_insert = LeafNode(Bytes([0] * 62), Bytes(b'\x02'))
inner = BranchNode((encode_internal_node(old_update), b'', encode_internal_node(new_insert)) + (b'',) * 13, empty)
expected = bytes(encode_internal_node(ExtensionNode(Bytes([0]), encode_internal_node(inner))))
assert keccak256(old_rlp) == bytes(encode_internal_node(old))
section = struct.pack('<I', 4) + old_rlp
key0 = b'\0' * 64
key1 = bytes([0, 2]) + b'\0' * 62
blob = (struct.pack('<Q', len(section)) + keccak256(old_rlp) + key0 + b'\x03' + b'\0' * 7 +
        key1 + b'\x02' + b'\0' * 7 + struct.pack('<QQ', 0, 1) + section)
(root / 'input').write_bytes(blob + b'\0' * (-len(blob) % 8))
(root / 'expected').write_bytes(expected)
PY
"$ZISKEMU" -e "$workdir/root.elf" -i "$workdir/input" -o "$workdir/output" -n 3000000 >/dev/null </dev/null
python3 - "$workdir" <<'PY'
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1]); out = (root / 'output').read_bytes()
assert struct.unpack_from('<Q', out)[0] == 0
assert out[8:40] == (root / 'expected').read_bytes(), out[8:40].hex()
print('PASS: bounded builder recursively rebuilds an old leaf slot beside a new insertion')
PY
