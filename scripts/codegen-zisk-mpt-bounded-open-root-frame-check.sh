#!/usr/bin/env bash
# Exercise sd13v's root-frame opener: witness-only resolve, classify, and
# canonical branch-reference capture in one bounded depth-zero frame.
set -euo pipefail
cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

workdir="$(mktemp -d)"
trap 'rm -rf "$workdir"' EXIT
lake build codegen >/dev/null
lake exe codegen --program zisk_mpt_bounded_open_root_frame --halt linux93 -o "$workdir/open" >/dev/null

python3 - "$workdir/input" <<'PY'
from Crypto.Hash import keccak
import pathlib
import struct
import sys

# branch children 0..2: empty, inline empty-list, hash(00..1f); the rest and
# branch value are empty.  This exercises each retained reference encoding.
node = b'\xf1' + b'\x80\xc0\xa0' + bytes(range(32)) + b'\x80' * 14
h = keccak.new(digest_bits=256); h.update(node)
section = struct.pack('<I', 4) + node
pathlib.Path(sys.argv[1]).write_bytes(struct.pack('<Q', len(section)) + h.digest() + section)
PY

"$ZISKEMU" -e "$workdir/open.elf" -i "$workdir/input" -o "$workdir/output" -n 1000000 >/dev/null </dev/null

python3 - "$workdir/output" <<'PY'
import pathlib
import struct
import sys

out = pathlib.Path(sys.argv[1]).read_bytes()
assert struct.unpack_from('<QQQQ', out) == (0, 4, 50, 0)
slots, cursor = [], 32
for _ in range(3):
    n = struct.unpack_from('<Q', out, cursor)[0]
    slots.append((n, out[cursor + 8:cursor + 40]))
    cursor += 40
assert slots[0] == (0, b'\0' * 32)
assert slots[1] == (1, b'\xc0' + b'\0' * 31)
assert slots[2] == (32, bytes(range(32)))
print('PASS: bounded root opener resolves, classifies, and retains canonical branch refs')
PY
