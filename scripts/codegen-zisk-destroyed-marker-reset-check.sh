#!/usr/bin/env bash
# Verifies the multi-transaction SELFDESTRUCT marker boundary: a stale marker
# would skip an omitted persistent storage write, while the per-transaction
# reset forces the same write to be covered by the BAL.
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-$HOME/.zisk/bin/ziskemu}"
if [[ ! -x "$ZISKEMU" ]]; then
  echo "ziskemu not found -- set ZISKEMU" >&2
  exit 1
fi

lake build codegen
lake exe codegen --program zisk_bal_storage_covers_exec_log --halt linux93 \
  -o gen-out/zisk_destroyed_marker_reset
: > gen-out/zisk_destroyed_marker_reset.input
"$ZISKEMU" -e gen-out/zisk_destroyed_marker_reset.elf \
  -i gen-out/zisk_destroyed_marker_reset.input \
  -o gen-out/zisk_destroyed_marker_reset.output -n 100000000

python3 - <<'PY'
import struct
import sys

data = open('gen-out/zisk_destroyed_marker_reset.output', 'rb').read()
def u64(off):
    return struct.unpack_from('<Q', data, off)[0] if off + 8 <= len(data) else None

checks = [
    ('stale destroyed marker skips omitted write', u64(24), 0),
    ('cleared marker demands omitted write', u64(32), 1),
]
failed = False
for label, got, expected in checks:
    ok = got == expected
    failed |= not ok
    print(f"  {'OK' if ok else 'FAIL'} {label}: got={got} expected={expected}")
sys.exit(1 if failed else 0)
PY
