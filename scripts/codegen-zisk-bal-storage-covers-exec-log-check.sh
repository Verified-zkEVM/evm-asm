#!/usr/bin/env bash
# codegen-zisk-bal-storage-covers-exec-log-check.sh -- bead bmvmx.1.6.5.
#
# Checks bal_storage_covers_exec_log (the converse of bal_storage_matches_exec_log):
# every NET storage change the execution log records for an account must be CLAIMED by
# the BAL storage_changes — catches an OMITTED write. The probe uses one BAL
# (slot7->0x22, slot9->0x33) and varies the exec log (addrHash A):
#   (1) S7 (0x11 then 0x22), S9 0x33, SB read no-op -> all net changes claimed -> 0
#   (2) + S5 net change 0x44 not in the BAL                              -> 1 (omission)
#   (3) S7 last current 0x99 (BAL claims 0x22)                           -> 1 (mismatch)
# Exercises last-write-wins, the read-no-op (current==original) exclusion, and the
# BAL(big-endian) <-> exec-log(stack-word) byte-order reconciliation.
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

echo "==> emit zisk_bal_storage_covers_exec_log ELF"
lake exe codegen --program zisk_bal_storage_covers_exec_log --halt linux93 -o gen-out/zisk_bal_storage_covers_exec_log

: > gen-out/zisk_bal_storage_covers_exec_log.input
"$ZISKEMU" -e gen-out/zisk_bal_storage_covers_exec_log.elf \
  -i gen-out/zisk_bal_storage_covers_exec_log.input -o gen-out/zisk_bal_storage_covers_exec_log.output -n 100000000 \
  >gen-out/zisk_bal_storage_covers_exec_log.emu.log 2>&1

python3 - <<'PY'
import struct, sys
data = open('gen-out/zisk_bal_storage_covers_exec_log.output', 'rb').read()
def u64(off): return struct.unpack('<Q', data[off:off+8])[0] if off + 8 <= len(data) else None
checks = [
    ('all net-changes claimed -> covered', u64(0),  0),
    ('omitted S5 -> reject',               u64(8),  1),
    ('wrong S7 value -> reject',           u64(16), 1),
]
failed = False
for label, got, exp in checks:
    ok = got == exp
    failed = failed or not ok
    print(f"  {'OK  ' if ok else 'FAIL'} {label:36s} got={got} exp={exp}")
sys.exit(1 if failed else 0)
PY

echo
echo "==> PASS: bal_storage_covers_exec_log accepts a BAL that claims every net change and"
echo "          rejects (omitted change / wrong claimed value)"
