#!/usr/bin/env bash
# Verify bounded leaf compact-path decoding and pre-write rejection.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
workdir="$(mktemp -d)"; trap 'rm -rf "$workdir"' EXIT
bash scripts/codegen-force-relink.sh >/dev/null
lake exe codegen --program zisk_mpt_bounded_decode_leaf --halt linux93 -o "$workdir/leaf" >/dev/null
python3 - "$workdir" <<'PY'
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1])
cases = {
    'valid': b'\xc4\x82\x31\x23\x80',
    'extension': b'\xc4\x82\x11\x23\x80',
    'long': b'\xf8\x44\xb8\x41' + b'\x20' + b'\x00' * 64 + b'\x80',
}
for name, node in cases.items():
    blob = struct.pack('<Q', len(node)) + node
    (root / f'{name}.input').write_bytes(blob + b'\0' * (-len(blob) % 8))
PY
for kind in valid extension long; do
  "$ZISKEMU" -e "$workdir/leaf.elf" -i "$workdir/$kind.input" -o "$workdir/$kind.output" -n 1000000 >/dev/null </dev/null
done
python3 - "$workdir" <<'PY'
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1])
out = (root / 'valid.output').read_bytes()
assert struct.unpack_from('<QQQQ', out) == (0, 3, 5, 0)
assert out[32:35] == b'\x01\x02\x03'
for name in ['extension', 'long']:
    assert struct.unpack_from('<Q', (root / f'{name}.output').read_bytes())[0] == 1
print('PASS: bounded leaf decoder materializes a leaf path and rejects non-leaf/overlong paths')
PY
