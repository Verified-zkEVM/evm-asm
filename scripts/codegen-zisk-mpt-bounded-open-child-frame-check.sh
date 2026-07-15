#!/usr/bin/env bash
# Verify hashed-child descent resolves only from the immutable witness.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
workdir="$(mktemp -d)"; trap 'rm -rf "$workdir"' EXIT
bash scripts/codegen-force-relink.sh >/dev/null
lake exe codegen --program zisk_mpt_bounded_open_child_frame --halt linux93 -o "$workdir/open" >/dev/null
uv run --directory execution-specs --quiet python3 - "$workdir/input" <<'PY'
from ethereum.crypto.hash import keccak256
import pathlib, struct, sys
node = b'\xc2\x20\x80'  # leaf([], empty-value), compact flag classifies as leaf
section = struct.pack('<I', 4) + node
blob = struct.pack('<Q', len(section)) + keccak256(node) + section
pathlib.Path(sys.argv[1]).write_bytes(blob + b'\0' * (-len(blob) % 8))
PY
"$ZISKEMU" -e "$workdir/open.elf" -i "$workdir/input" -o "$workdir/output" -n 1000000 >/dev/null </dev/null
python3 - "$workdir/output" <<'PY'
import pathlib, struct, sys
out = pathlib.Path(sys.argv[1]).read_bytes()
assert struct.unpack_from('<QQQQ', out) == (0, 3, 2, 4)
print('PASS: bounded child opener resolves a hashed child from witness and classifies its leaf frame')
PY
