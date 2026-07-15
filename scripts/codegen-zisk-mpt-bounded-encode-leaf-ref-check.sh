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
python3 - "$workdir" <<'PY'
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1])
for name, n in [('root', 64), ('suffix', 3), ('terminal', 0)]:
    (root / f'{name}.input').write_bytes(struct.pack('<Q', n))
PY
for kind in root suffix terminal; do
  "$ZISKEMU" -e "$workdir/leaf.elf" -i "$workdir/$kind.input" -o "$workdir/$kind.output" -n 1000000 >/dev/null </dev/null
done
uv run --directory execution-specs --quiet python3 - "$workdir" <<'PY'
from ethereum.crypto.hash import keccak256
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1])
for name, node in {
    'root': b'\xe3\xa1\x20' + b'\0' * 32 + b'\x80',
    'suffix': b'\xc4\x82\x30\x00\x80',
    'terminal': b'\xc2\x20\x80',
}.items():
    out = (root / f'{name}.output').read_bytes()
    raw_len = 32 if len(node) >= 32 else len(node)
    got = struct.unpack_from('<QQQ', out)
    assert got == (0, len(node), raw_len), (name, got)
    assert out[24:24 + len(node)] == node, (name, out[24:24 + len(node)].hex())
    expected_ref = keccak256(node) if raw_len == 32 else node
    assert out[24 + len(node):24 + len(node) + raw_len] == expected_ref, name
print('PASS: bounded leaf encoder produces canonical root, suffix, and terminal leaves')
PY
