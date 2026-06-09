#!/usr/bin/env bash
# codegen-zisk-bal-storage-change-values-check.sh -- bead bmvmx.1.6.1.
#
# Checks bal_storage_change_values: parse a BAL AccountChanges storage_changes
# into (slot key, final post-value) pairs. The probe builds an AccountChanges with
#   slot 0x07 -> [[0,0x11],[1,0x22]]   (post = 0x22, the LAST tuple)
#   slot 0x09 -> [[0,0x33]]            (post = 0x33)
# and asserts count=2 and the two (key, value) low bytes.
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2; exit 1; fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_bal_storage_change_values ELF"
lake exe codegen --program zisk_bal_storage_change_values --halt linux93 -o gen-out/zisk_bal_storage_change_values

: > gen-out/zisk_bal_storage_change_values.input
"$ZISKEMU" -e gen-out/zisk_bal_storage_change_values.elf \
  -i gen-out/zisk_bal_storage_change_values.input -o gen-out/zisk_bal_storage_change_values.output -n 100000000 \
  >gen-out/zisk_bal_storage_change_values.emu.log 2>&1

python3 - <<'PY'
import struct, sys
data = open('gen-out/zisk_bal_storage_change_values.output', 'rb').read()
def u64(off): return struct.unpack('<Q', data[off:off+8])[0] if off + 8 <= len(data) else None
checks = [
    ('count',                u64(0),  2),
    ('slot0 key[31]',        u64(8),  0x07),
    ('slot0 post-value[31]', u64(16), 0x22),  # last tuple of [[0,0x11],[1,0x22]]
    ('slot1 key[31]',        u64(24), 0x09),
    ('slot1 post-value[31]', u64(32), 0x33),
]
failed = False
for label, got, exp in checks:
    ok = got == exp
    failed = failed or not ok
    print(f"  {'OK  ' if ok else 'FAIL'} {label:24s} got={got} exp={exp}")
sys.exit(1 if failed else 0)
PY

echo
echo "==> PASS: bal_storage_change_values extracts (slot key, final post-value) pairs"
