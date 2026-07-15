#!/usr/bin/env bash
# Verify bounded compact-path decoding and pre-write overlength rejection.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
workdir="$(mktemp -d)"; trap 'rm -rf "$workdir"' EXIT
lake build codegen >/dev/null
lake exe codegen --program zisk_mpt_bounded_decode_extension --halt linux93 -o "$workdir/ext" >/dev/null
python3 - "$workdir" <<'PY'
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1])
cases = {
    'valid': b'\xc4\x82\x11\x23\xc0',
    'leaf': b'\xc4\x82\x31\x23\xc0',
    'long': b'\xf8\x44\xb8\x41' + b'\x00' * 65 + b'\xc0',
}
for name, node in cases.items():
    blob = struct.pack('<Q', len(node)) + node
    (root / f'{name}.input').write_bytes(blob + b'\0' * (-len(blob) % 8))
PY
for kind in valid leaf long; do
  "$ZISKEMU" -e "$workdir/ext.elf" -i "$workdir/$kind.input" -o "$workdir/$kind.output" -n 1000000 >/dev/null </dev/null
done
python3 - "$workdir" <<'PY'
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1])
out = (root / 'valid.output').read_bytes()
assert struct.unpack_from('<QQQQ', out) == (0, 3, 4, 1)
assert out[32:35] == b'\x01\x02\x03'
for name in ['leaf', 'long']:
    assert struct.unpack_from('<Q', (root / f'{name}.output').read_bytes())[0] == 1
print('PASS: bounded extension decoder materializes short paths and rejects leaf/overlong paths')
PY
