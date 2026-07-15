#!/usr/bin/env bash
# Verify canonical RLP reconstruction of a fixed frontier branch frame.
set -euo pipefail
cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
workdir="$(mktemp -d)"
trap 'rm -rf "$workdir"' EXIT
bash scripts/codegen-force-relink.sh >/dev/null
lake exe codegen --program zisk_mpt_bounded_encode_branch --halt linux93 -o "$workdir/branch" >/dev/null
dd if=/dev/zero of="$workdir/input" bs=8 count=1 status=none
"$ZISKEMU" -e "$workdir/branch.elf" -i "$workdir/input" -o "$workdir/output" -n 1000000 >/dev/null </dev/null
python3 - "$workdir/output" <<'PY'
import pathlib, struct, sys
out = pathlib.Path(sys.argv[1]).read_bytes()
expected = b'\xf1\x80\xc0\xa0' + bytes(range(32)) + b'\x80' * 14
assert struct.unpack_from('<QQ', out) == (0, len(expected))
assert out[16:16 + len(expected)] == expected
print('PASS: bounded branch encoder preserves canonical empty, inline, and hash slots')
PY
