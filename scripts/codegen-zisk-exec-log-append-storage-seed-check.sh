#!/usr/bin/env bash
# codegen-zisk-exec-log-append-storage-seed-check.sh -- bead bmvmx.1.6.4.1 (option A).
#
# Checks exec_log_append_storage_seed: append one persistent-storage-log entry with an
# explicit per-account addrHash (original==current==value), bumping the entry count.
# This is the verdict-specific primitive for seeding NESTED-CALLEE storage into the
# exec log WITHOUT touching the shared 64B preload input contract. The probe appends
# (A=0xAA, slot 7, 0x42) then (B=0xBB, slot 9, 0x99) from an empty log and reads back
# the two 128-byte entries + the returned count.
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

echo "==> emit zisk_exec_log_append_storage_seed ELF"
lake exe codegen --program zisk_exec_log_append_storage_seed --halt linux93 -o gen-out/zisk_exec_log_append_storage_seed

: > gen-out/zisk_exec_log_append_storage_seed.input
"$ZISKEMU" -e gen-out/zisk_exec_log_append_storage_seed.elf \
  -i gen-out/zisk_exec_log_append_storage_seed.input -o gen-out/zisk_exec_log_append_storage_seed.output -n 100000000 \
  >gen-out/zisk_exec_log_append_storage_seed.emu.log 2>&1

python3 - <<'PY'
import struct, sys
data = open('gen-out/zisk_exec_log_append_storage_seed.output', 'rb').read()
def u64(off): return struct.unpack('<Q', data[off:off+8])[0] if off + 8 <= len(data) else None
checks = [
    ('final count',  u64(0),  2),
    ('e0 addrHash',  u64(8),  0xAA),
    ('e0 slotKey',   u64(16), 0x07),
    ('e0 original',  u64(24), 0x42),
    ('e0 current',   u64(32), 0x42),
    ('e1 addrHash',  u64(40), 0xBB),
    ('e1 current',   u64(48), 0x99),
]
failed = False
for label, got, exp in checks:
    ok = got == exp
    failed = failed or not ok
    print(f"  {'OK  ' if ok else 'FAIL'} {label:14s} got={got} exp={exp}")
sys.exit(1 if failed else 0)
PY

echo
echo "==> PASS: exec_log_append_storage_seed writes (addrHash,key,value->orig+cur) and bumps count"
