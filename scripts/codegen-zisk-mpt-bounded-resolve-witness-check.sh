#!/usr/bin/env bash
# Verify sd13v's resolver can find a pre-state witness node without NodeDb.
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

bash scripts/codegen-force-relink.sh >/dev/null
lake exe codegen --program zisk_mpt_bounded_resolve_witness --halt linux93 -o "$workdir/resolve" >/dev/null

uv run --directory execution-specs --quiet python3 - "$workdir/input" <<'PY'
from ethereum.crypto.hash import keccak256
import pathlib
import struct
import sys

node = b'\xc0'                         # a one-byte inline MPT node
section = struct.pack('<I', 4) + node   # SSZ List[ByteList] with one element
blob = struct.pack('<Q', len(section)) + keccak256(node) + section
pathlib.Path(sys.argv[1]).write_bytes(blob + b'\0' * (-len(blob) % 8))
PY

"$ZISKEMU" -e "$workdir/resolve.elf" -i "$workdir/input" -o "$workdir/output" -n 1000000 >/dev/null </dev/null

python3 - "$workdir/output" <<'PY'
import pathlib
import struct
import sys

out = pathlib.Path(sys.argv[1]).read_bytes()
assert struct.unpack_from('<QQQ', out) == (0, 4, 1)
print('PASS: bounded resolver finds the pre-state witness node without NodeDb')
PY
