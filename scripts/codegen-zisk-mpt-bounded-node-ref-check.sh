#!/usr/bin/env bash
# Verify the bounded builder's raw-reference rule: inline below 32 bytes,
# Keccak hash at 32 bytes and above, with no NodeDb involvement.
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
lake exe codegen --program zisk_mpt_bounded_node_ref --halt linux93 -o "$workdir/ref" >/dev/null

uv run --directory execution-specs --quiet python3 - "$workdir" <<'PY'
from ethereum.crypto.hash import keccak256
import pathlib
import struct
import sys

root = pathlib.Path(sys.argv[1])
for name, node in [('inline', bytes(range(31))), ('hashed', bytes(range(32)))]:
    blob = struct.pack('<Q', len(node)) + node
    (root / f'{name}.input').write_bytes(blob + b'\0' * (-len(blob) % 8))
    (root / f'{name}.expected').write_bytes(node if len(node) < 32 else keccak256(node))
PY

for kind in inline hashed; do
  "$ZISKEMU" -e "$workdir/ref.elf" -i "$workdir/$kind.input" -o "$workdir/$kind.output" -n 1000000 >/dev/null </dev/null
done

python3 - "$workdir" <<'PY'
import pathlib
import struct
import sys

root = pathlib.Path(sys.argv[1])
for name, expected_len in [('inline', 31), ('hashed', 32)]:
    out = (root / f'{name}.output').read_bytes()
    assert struct.unpack_from('<QQ', out) == (0, expected_len)
    assert out[16:16 + expected_len] == (root / f'{name}.expected').read_bytes()
print('PASS: bounded node references inline short nodes and hash 32-byte nodes')
PY
