#!/usr/bin/env bash
# Terminal-suffix divergent-leaf KAT: both branch children are empty-path leaves.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
workdir="$(mktemp -d)"; trap 'rm -rf "$workdir"' EXIT
bash scripts/codegen-force-relink.sh >/dev/null
lake exe codegen --program zisk_mpt_bounded_state_root --halt linux93 -o "$workdir/root" >/dev/null
uv run --directory execution-specs --quiet python3 - "$workdir" <<'PY'
from ethereum.crypto.hash import keccak256
import pathlib, struct, sys

root = pathlib.Path(sys.argv[1])
old = b'\xe3\xa1\x20' + b'\0' * 32 + b'\x80'
# The two terminal children are inline RLP leaves: [HP(leaf, empty), value].
old_child, new_child = b'\xc2\x20\x80', b'\xc2\x20\x01'
payload = old_child + new_child + b'\x80' * 15
branch = bytes([0xc0 + len(payload)]) + payload
# The first 63 nibbles remain shared, so canonical Patricia form restores
# them as an odd-length extension above the terminal branch.
path = b'\x10' + b'\0' * 31
expected = bytes([0xc0 + 33 + len(branch)]) + b'\xa0' + path + branch
section = struct.pack('<I', 4) + old
key = b'\0' * 63 + b'\x01'
blob = (struct.pack('<Q', len(section)) + keccak256(old) + key +
        struct.pack('<Q', 1) + b'\x01' + b'\0' * 7 + struct.pack('<Q', 1) + section)
(root / 'input').write_bytes(blob + b'\0' * (-len(blob) % 8))
(root / 'expected').write_bytes(keccak256(expected))
PY
"$ZISKEMU" -e "$workdir/root.elf" -i "$workdir/input" -o "$workdir/output" -n 3000000 >/dev/null </dev/null
python3 - "$workdir" <<'PY'
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1]); out = (root / 'output').read_bytes()
status = struct.unpack_from('<Q', out)[0]
assert status == 0, status
assert out[8:40] == (root / 'expected').read_bytes(), out[8:40].hex()
print('PASS: bounded builder splits a terminal divergent leaf canonically')
PY
