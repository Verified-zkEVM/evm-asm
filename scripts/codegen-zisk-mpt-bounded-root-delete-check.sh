#!/usr/bin/env bash
# Deleting the sole bounded state leaf must produce the canonical empty trie.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
workdir="$(mktemp -d)"; trap 'rm -rf "$workdir"' EXIT
bash scripts/codegen-force-relink.sh >/dev/null
lake exe codegen --program zisk_mpt_bounded_state_root --halt linux93 -o "$workdir/root" >/dev/null
uv run --directory execution-specs --quiet python3 - "$workdir" <<'PY'
from ethereum.crypto.hash import keccak256
from ethereum.merkle_patricia_trie import EMPTY_TRIE_ROOT, LeafNode, encode_internal_node
from ethereum_types.bytes import Bytes
import pathlib, struct, sys

root = pathlib.Path(sys.argv[1])
old = b'\xe3\xa1\x20' + b'\0' * 32 + b'\x80'
old_spec = LeafNode(Bytes([0] * 64), Bytes(b''))
assert keccak256(old) == bytes(encode_internal_node(old_spec))
section = struct.pack('<I', 4) + old
blob = (struct.pack('<Q', len(section)) + keccak256(old) + b'\0' * 64 +
        struct.pack('<Q', 0) + b'\0' * 8 + struct.pack('<Q', 2) + section)
(root / 'input').write_bytes(blob + b'\0' * (-len(blob) % 8))
(root / 'expected').write_bytes(EMPTY_TRIE_ROOT)
PY
"$ZISKEMU" -e "$workdir/root.elf" -i "$workdir/input" -o "$workdir/output" -n 2000000 >/dev/null </dev/null
python3 - "$workdir" <<'PY'
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1]); out = (root / 'output').read_bytes()
status = struct.unpack_from('<Q', out)[0]
assert status == 0, status
assert out[8:40] == (root / 'expected').read_bytes(), out[8:40].hex()
print('PASS: bounded builder deletes a singleton root to EMPTY_TRIE_ROOT')
PY
