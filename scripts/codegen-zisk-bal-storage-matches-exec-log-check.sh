#!/usr/bin/env bash
# codegen-zisk-bal-storage-matches-exec-log-check.sh -- bead bmvmx.1.6.2 (core).
#
# Checks bal_storage_matches_exec_log: verify a BAL account's storage_changes are
# all reproduced by the execution storage log with matching final values. The
# probe builds a 2-entry exec log (addr A: slot7=0x22, slot9=0x33) and a BAL
# AccountChanges claiming slot7->0x22, slot9->0x33, then:
#   (1) consistent BAL                 -> 0 (match)
#   (2) exec-log slot7 current -> 0x99 -> 1 (value mismatch)
#   (3) log shrunk to 1 entry          -> 1 (BAL slot9 absent from log)
# Exercises the BAL(big-endian) <-> exec-log(stack-word) byte-order reconciliation.
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

echo "==> emit zisk_bal_storage_matches_exec_log ELF"
lake exe codegen --program zisk_bal_storage_matches_exec_log --halt linux93 -o gen-out/zisk_bal_storage_matches_exec_log

: > gen-out/zisk_bal_storage_matches_exec_log.input
"$ZISKEMU" -e gen-out/zisk_bal_storage_matches_exec_log.elf \
  -i gen-out/zisk_bal_storage_matches_exec_log.input -o gen-out/zisk_bal_storage_matches_exec_log.output -n 100000000 \
  >gen-out/zisk_bal_storage_matches_exec_log.emu.log 2>&1

python3 - <<'PY'
import struct, sys
data = open('gen-out/zisk_bal_storage_matches_exec_log.output', 'rb').read()
def u64(off): return struct.unpack('<Q', data[off:off+8])[0] if off + 8 <= len(data) else None
checks = [
    ('consistent BAL -> match',     u64(0),  0),
    ('value mismatch -> reject',    u64(8),  1),
    ('claimed key absent -> reject',u64(16), 1),
]
failed = False
for label, got, exp in checks:
    ok = got == exp
    failed = failed or not ok
    print(f"  {'OK  ' if ok else 'FAIL'} {label:32s} got={got} exp={exp}")
sys.exit(1 if failed else 0)
PY

echo
echo "==> PASS: bal_storage_matches_exec_log accepts a BAL execution reproduces and"
echo "          rejects (value mismatch / claimed-but-absent change)"
