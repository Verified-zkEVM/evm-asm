#!/usr/bin/env bash
# Verify the bounded empty-account leaf and its raw hashed parent reference.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
workdir="$(mktemp -d)"
trap 'rm -rf "$workdir"' EXIT
lake build codegen >/dev/null
lake exe codegen --program zisk_mpt_bounded_encode_leaf_ref --halt linux93 -o "$workdir/leaf" >/dev/null
dd if=/dev/zero of="$workdir/input" bs=8 count=1 status=none
"$ZISKEMU" -e "$workdir/leaf.elf" -i "$workdir/input" -o "$workdir/output" -n 1000000 >/dev/null </dev/null
uv run --directory execution-specs --quiet python3 - "$workdir/output" <<'PY'
from ethereum.crypto.hash import keccak256
import pathlib, struct, sys
out = pathlib.Path(sys.argv[1]).read_bytes()
node = b'\xe4\xb8\x21\x20' + b'\0' * 32 + b'\x80'
assert struct.unpack_from('<QQQ', out) == (0, len(node), 32)
assert out[24:24 + len(node)] == node
assert out[24 + len(node):24 + len(node) + 32] == keccak256(node)
print('PASS: bounded leaf encoder produces canonical account leaf and raw hash ref')
PY
