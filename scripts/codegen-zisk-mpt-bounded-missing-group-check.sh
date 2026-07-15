#!/usr/bin/env bash
# Grouped empty-child construction KAT for sd13v's bounded state-root walk.
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
def leaf_63(value):
    return b'\xe2\xa0\x30' + b'\0' * 31 + value
def leaf_62(value):
    return b'\xe2\xa0\x20' + b'\0' * 31 + value
def branch(children):
    slots = [b'\xa0' + h if h is not None else b'\x80' for h in children]
    payload = b''.join(slots) + b'\x80'
    return b'\xf8' + bytes([len(payload)]) + payload

old0, old1 = leaf_63(b'\x80'), leaf_63(b'\x80')
h0, h1 = keccak256(old0), keccak256(old1)
old_root = branch([h0, h1] + [None] * 14)
new20, new21 = leaf_62(b'\x01'), leaf_62(b'\x02')
new2 = branch([keccak256(new20), keccak256(new21)] + [None] * 14)
new_root = branch([h0, h1, keccak256(new2)] + [None] * 13)
nodes = [old_root, old0, old1]
offsets, cursor = [], 4 * len(nodes)
for node in nodes:
    offsets.append(cursor); cursor += len(node)
section = b''.join(struct.pack('<I', x) for x in offsets) + b''.join(nodes)
key0 = bytes([2, 0]) + b'\0' * 62
key1 = bytes([2, 1]) + b'\0' * 62
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
print('PASS: bounded builder recursively constructs a grouped missing subtree')
PY
