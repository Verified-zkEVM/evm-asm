#!/usr/bin/env bash
# End-to-end exact-leaf replacement KAT for sd13v's bounded root driver.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
workdir="$(mktemp -d)"; trap 'rm -rf "$workdir"' EXIT
lake build codegen >/dev/null
lake exe codegen --program zisk_mpt_bounded_state_root --halt linux93 -o "$workdir/root" >/dev/null
uv run --directory execution-specs --quiet python3 - "$workdir" <<'PY'
from ethereum.crypto.hash import keccak256
import pathlib, struct, sys

root = pathlib.Path(sys.argv[1])
old_node = b'\xe3\xa1\x20' + b'\0' * 32 + b'\x80'
section = struct.pack('<I', 4) + old_node
blob = (struct.pack('<Q', len(section)) + keccak256(old_node) + b'\0' * 64 +
        struct.pack('<Q', 1) + b'\x01' + b'\0' * 7 + struct.pack('<Q', 0) + section)
(root / 'input').write_bytes(blob + b'\0' * (-len(blob) % 8))
expected_node = b'\xe3\xa1\x20' + b'\0' * 32 + b'\x01'
(root / 'expected').write_bytes(keccak256(expected_node))
PY
"$ZISKEMU" -e "$workdir/root.elf" -i "$workdir/input" -o "$workdir/output" -n 2000000 >/dev/null </dev/null
python3 - "$workdir" <<'PY'
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1])
out = (root / 'output').read_bytes()
status = struct.unpack_from('<Q', out)[0]
assert status == 0, status
assert out[8:40] == (root / 'expected').read_bytes(), out[8:40].hex()
print('PASS: bounded state-root driver replaces an exact leaf through witness-only resolution')
PY
