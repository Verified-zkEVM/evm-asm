#!/usr/bin/env bash
# Check raw-hash child conversion and canonical bounded extension re-encoding.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
workdir="$(mktemp -d)"; trap 'rm -rf "$workdir"' EXIT
lake build codegen >/dev/null
lake exe codegen --program zisk_mpt_bounded_encode_extension --halt linux93 -o "$workdir/ext" >/dev/null
dd if=/dev/zero of="$workdir/input" bs=8 count=1 status=none
"$ZISKEMU" -e "$workdir/ext.elf" -i "$workdir/input" -o "$workdir/output" -n 1000000 >/dev/null </dev/null
uv run --directory execution-specs --quiet python3 - "$workdir/output" <<'PY'
from ethereum.crypto.hash import keccak256
import pathlib, struct, sys
out = pathlib.Path(sys.argv[1]).read_bytes()
node = b'\xe4\x82\x11\x23\xa0' + bytes(range(32))
digest = keccak256(node)
assert struct.unpack_from('<QQQ', out) == (0, len(node), 32)
assert out[24:24 + len(node)] == node
assert out[24 + len(node):24 + len(node) + 32] == digest
print('PASS: bounded extension encoder prefixes raw hash children and derives the canonical node reference')
PY
