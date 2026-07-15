#!/usr/bin/env bash
# Verify frontier classification of branch, extension, and leaf witness nodes.
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
lake exe codegen --program zisk_mpt_bounded_classify_node --halt linux93 -o "$workdir/classify" >/dev/null

python3 - "$workdir" <<'PY'
import pathlib
import struct
import sys

root = pathlib.Path(sys.argv[1])
nodes = {
    'branch': b'\xd1' + b'\x80' * 17,
    'extension': b'\xc2\x00\xc0',
    'leaf': b'\xc2\x20\x80',
}
for name, node in nodes.items():
    (root / f'{name}.input').write_bytes(struct.pack('<Q', len(node)) + node)
PY

for kind in branch extension leaf; do
  "$ZISKEMU" -e "$workdir/classify.elf" -i "$workdir/$kind.input" -o "$workdir/$kind.output" -n 1000000 >/dev/null </dev/null
done

python3 - "$workdir" <<'PY'
import pathlib
import struct
import sys

root = pathlib.Path(sys.argv[1])
for name, expected in [('branch', 0), ('extension', 1), ('leaf', 2)]:
    assert struct.unpack_from('<QQ', (root / f'{name}.output').read_bytes()) == (0, expected)
print('PASS: bounded frontier classification recognizes branch, extension, and leaf')
PY
