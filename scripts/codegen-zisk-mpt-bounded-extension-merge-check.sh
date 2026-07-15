#!/usr/bin/env bash
# Canonical extension-child merge KAT for sd13v's bounded state-root walk.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
workdir="$(mktemp -d)"; trap 'rm -rf "$workdir"' EXIT
lake build codegen >/dev/null
lake exe codegen --program zisk_mpt_bounded_state_root --halt linux93 -o "$workdir/root" >/dev/null
uv run --directory execution-specs --quiet python3 - "$workdir" <<'PY'
from ethereum.crypto.hash import keccak256
import pathlib, struct, sys

root = pathlib.Path(sys.argv[1])
def leaf_61(value):
    return b'\xe0\x9f\x30' + b'\0' * 30 + value
def leaf_62(value):
    return b'\xe2\xa0\x20' + b'\0' * 31 + value
def extension_1(child):
    return b'\xe2\x10\xa0' + keccak256(child)
def branch(children):
    slots = [b'\xa0' + h if h is not None else b'\x80' for h in children]
    payload = b''.join(slots) + b'\x80'
    return b'\xf8' + bytes([len(payload)]) + payload

# root extension [0] -> branch; branch child 0 is extension [0] -> leaf,
# and deleting child 1 makes it collapse to extension [0,0].  The parent
# must merge to extension [0,0,0], rather than encoding extension->extension.
deep_leaf = leaf_61(b'\x80')
old_child0 = extension_1(deep_leaf)
old_child1 = leaf_62(b'\x80')
old_branch = branch([keccak256(old_child0), keccak256(old_child1)] + [None] * 14)
old_root = extension_1(old_branch)
expected = b'\xe3\x82\x10\x00\xa0' + keccak256(deep_leaf)
nodes = [old_root, old_branch, old_child0, old_child1, deep_leaf]
offsets, cursor = [], 4 * len(nodes)
for node in nodes:
    offsets.append(cursor); cursor += len(node)
section = b''.join(struct.pack('<I', x) for x in offsets) + b''.join(nodes)
key = bytes([0, 1]) + b'\0' * 62
blob = (struct.pack('<Q', len(section)) + keccak256(old_root) + key +
        struct.pack('<Q', 0) + struct.pack('<Q', 2) + section)
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
print('PASS: bounded builder canonically merges a rebuilt extension child')
PY
