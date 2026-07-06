#!/usr/bin/env bash
# codegen-zisk-bal-addr-to-exec-log-key-check.sh -- bead bmvmx.1.6.4.2.
#
# Checks bal_addr_to_exec_log_key: a BAL account's 20-byte big-endian address -> the
# 32-byte key the exec log uses for that account as a nested CALLEE. The callee's
# env.ADDRESS is the CALL `to` stack word (4 LE u64 limbs), so the key is the address
# BYTE-REVERSED (LE), low-aligned, high 12 bytes zero. Probe: a[0]=0xAA(MSB),
# a[5]=0x33, a[19]=0xBB(LSB) -> key[0]=0xBB, key[19]=0xAA, key[14]=0x33, key[24..]=0.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi
mkdir -p gen-out
echo "==> lake build codegen"; lake build codegen
echo "==> emit zisk_bal_addr_to_exec_log_key ELF"
lake exe codegen --program zisk_bal_addr_to_exec_log_key --halt linux93 -o gen-out/zisk_bal_addr_to_exec_log_key
: > gen-out/zisk_bal_addr_to_exec_log_key.input
"$ZISKEMU" -e gen-out/zisk_bal_addr_to_exec_log_key.elf \
  -i gen-out/zisk_bal_addr_to_exec_log_key.input -o gen-out/zisk_bal_addr_to_exec_log_key.output -n 100000000 \
  >gen-out/zisk_bal_addr_to_exec_log_key.emu.log 2>&1
python3 - <<'PY'
import struct, sys
data = open('gen-out/zisk_bal_addr_to_exec_log_key.output', 'rb').read()
def u64(o): return struct.unpack('<Q', data[o:o+8])[0] if o+8<=len(data) else None
checks = [('out[0] LSB=a[19]', u64(0), 0xBB), ('out[19] MSB=a[0]', u64(8), 0xAA),
          ('out[14]=a[5]', u64(16), 0x33), ('out[24..32] pad', u64(24), 0)]
failed=False
for label, got, exp in checks:
    ok=got==exp; failed=failed or not ok
    print(f"  {'OK  ' if ok else 'FAIL'} {label:18s} got={got} exp={exp}")
sys.exit(1 if failed else 0)
PY
echo; echo "==> PASS: bal_addr_to_exec_log_key reverses a BE address to the LE stack-word exec-log key"
