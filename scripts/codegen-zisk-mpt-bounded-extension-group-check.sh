#!/usr/bin/env bash
# Grouped existing-extension split KAT for sd13v's bounded state-root walk.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
workdir="$(mktemp -d)"; trap 'rm -rf "$workdir"' EXIT
lake build codegen >/dev/null
lake exe codegen --program zisk_mpt_bounded_missing_group --halt linux93 -o "$workdir/root" >/dev/null
uv run --directory execution-specs --quiet python3 - "$workdir" <<'PY'
from ethereum.crypto.hash import keccak256
import pathlib, struct, sys

root = pathlib.Path(sys.argv[1])
def leaf(nibbles, value):
    # All paths here are even-length all-zero suffixes.
    path = b'\x20' + b'\0' * (nibbles // 2)
    return bytes([0xc0 + 1 + len(path)]) + bytes([0x80 + len(path)]) + path + value
def ext(path, child):
    path_item = bytes([0x80 + len(path)]) + path
    child_item = b'\xa0' + child
    return bytes([0xc0 + len(path_item) + len(child_item)]) + path_item + child_item
def branch(children):
    slots = [b'\xa0' + h if h is not None else b'\x80' for h in children]
    payload = b''.join(slots) + b'\x80'
    return b'\xf8' + bytes([len(payload)]) + payload

old_leaf = leaf(62, b'\x80')
old_root = ext(b'\x00\x00', keccak256(old_leaf))
old_suffix = leaf(62, b'\x80')
new20, new21 = leaf(61, b'\x01'), leaf(61, b'\x02')
new2 = branch([keccak256(new20), keccak256(new21)] + [None] * 14)
split = branch([keccak256(old_suffix), None, keccak256(new2)] + [None] * 13)
new_root = ext(b'\x10', keccak256(split))
section = struct.pack('<I', 4) + old_root
key0 = bytes([0, 2, 0]) + b'\0' * 61
key1 = bytes([0, 2, 1]) + b'\0' * 61
blob = (struct.pack('<Q', len(section)) + keccak256(old_root) + key0 + b'\x01' + b'\0' * 7 +
        key1 + b'\x02' + b'\0' * 7 + section)
(root / 'input').write_bytes(blob + b'\0' * (-len(blob) % 8))
(root / 'expected').write_bytes(keccak256(new_root))
PY
"$ZISKEMU" -e "$workdir/root.elf" -i "$workdir/input" -o "$workdir/output" -n 3000000 >/dev/null </dev/null
python3 - "$workdir" <<'PY'
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1]); out = (root / 'output').read_bytes()
status = struct.unpack_from('<Q', out)[0]
assert status == 0, status
assert out[8:40] == (root / 'expected').read_bytes(), out[8:40].hex()
print('PASS: bounded builder splits an existing extension into an old suffix and grouped new subtree')
PY
