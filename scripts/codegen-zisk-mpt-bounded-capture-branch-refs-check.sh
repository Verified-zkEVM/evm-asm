#!/usr/bin/env bash
# Verify that sd13v preserves the three canonical branch-reference forms:
# empty, inline RLP, and a 32-byte hash.  This is a frontier-frame primitive,
# not an end-to-end root test, so ziskemu is used only for this focused probe.
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
lake exe codegen --program zisk_mpt_bounded_capture_branch_refs --halt linux93 -o "$workdir/capture" >/dev/null

python3 - "$workdir/input" <<'PY'
import pathlib
import struct
import sys

# branch = [empty, inline-empty-list, hash(00..1f), empty * 13, empty value]
payload = b'\x80\xc0\xa0' + bytes(range(32)) + b'\x80' * 14
node = bytes([0xc0 + len(payload)]) + payload
blob = struct.pack('<Q', len(node)) + node
pathlib.Path(sys.argv[1]).write_bytes(blob + b'\0' * (-len(blob) % 8))
PY

"$ZISKEMU" -e "$workdir/capture.elf" -i "$workdir/input" -o "$workdir/output" -n 1000000 >/dev/null </dev/null

python3 - "$workdir/output" <<'PY'
import pathlib
import struct
import sys

out = pathlib.Path(sys.argv[1]).read_bytes()
assert struct.unpack_from('<Q', out, 0)[0] == 0
slots = []
cursor = 8
for _ in range(3):
    n = struct.unpack_from('<Q', out, cursor)[0]
    slots.append((n, out[cursor + 8:cursor + 40]))
    cursor += 40
assert slots[0] == (0, b'\0' * 32)
assert slots[1] == (1, b'\xc0' + b'\0' * 31)
assert slots[2] == (32, bytes(range(32)))
print('PASS: bounded frontier capture preserves empty, inline, and hash branch references')
PY
