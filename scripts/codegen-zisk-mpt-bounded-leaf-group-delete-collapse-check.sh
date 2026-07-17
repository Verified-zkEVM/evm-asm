#!/usr/bin/env bash
# Existing-leaf deletion plus singleton-sibling collapse KAT for sd13v.
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
from ethereum.merkle_patricia_trie import LeafNode, encode_internal_node
from ethereum_types.bytes import Bytes
import pathlib, struct, sys

root = pathlib.Path(sys.argv[1])
empty = Bytes(b'')
old_rlp = b'\xe3\xa1\x20' + b'\0' * 32 + b'\x80'
old = LeafNode(Bytes([0] * 64), empty)
survivor = LeafNode(Bytes([2, 0] + [0] * 62), Bytes(b'\x02'))
assert keccak256(old_rlp) == bytes(encode_internal_node(old))
section = struct.pack('<I', 4) + old_rlp
deleted_key = b'\0' * 64
survivor_key = bytes([2, 0]) + b'\0' * 62
blob = (
    struct.pack('<Q', len(section)) + keccak256(old_rlp) +
    deleted_key + b'\x01' + b'\0' * 7 +
    survivor_key + b'\x02' + b'\0' * 7 +
    struct.pack('<QQ', 2, 1) + section
)
(root / 'input').write_bytes(blob + b'\0' * (-len(blob) % 8))
(root / 'expected').write_bytes(bytes(encode_internal_node(survivor)))
PY
"$ZISKEMU" -e "$workdir/root.elf" -i "$workdir/input" -o "$workdir/output" -n 3000000 >/dev/null </dev/null
python3 - "$workdir" <<'PY'
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1]); out = (root / 'output').read_bytes()
assert struct.unpack_from('<Q', out)[0] == 0
assert out[8:40] == (root / 'expected').read_bytes(), out[8:40].hex()
print('PASS: bounded builder collapses deleted leaf-group branch to its singleton sibling')
PY
