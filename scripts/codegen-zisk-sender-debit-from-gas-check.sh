#!/usr/bin/env bash
# codegen-zisk-sender-debit-from-gas-check.sh -- bead bmvmx.1.6.3 (balance slice).
# Checks sender_debit_from_gas: the spec sender charge = receipt_inc * eff_gas_price +
# value, receipt_inc = tx_gas_result_increments.a2 (EIP-3529 refund + EIP-7623 floor).
# Known answer: gas_limit=100000, gas_left=78000, refund=5000, floor=21000 ->
# before_refund=22000, refund_cap=4400, after_refund=17600, receipt_inc=max(17600,21000)=21000;
# eff_gas_price=1, value=0 -> debit=21000 (0x5208).
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
echo "==> emit zisk_sender_debit_from_gas ELF"
lake exe codegen --program zisk_sender_debit_from_gas --halt linux93 -o gen-out/zisk_sdfg
: > gen-out/zisk_sdfg.input
"$ZISKEMU" -e gen-out/zisk_sdfg.elf -i gen-out/zisk_sdfg.input -o gen-out/zisk_sdfg.output -n 100000000 >gen-out/zisk_sdfg.emu.log 2>&1
python3 - <<'PY'
import struct, sys
d = open('gen-out/zisk_sdfg.output', 'rb').read()
def u(o): return struct.unpack('<Q', d[o:o+8])[0] if o+8 <= len(d) else None
ok = (u(0)==21000) and (u(8)==0x08) and (u(16)==0x52) and (u(24)==0)
print(f"  receipt_inc={u(0)} (exp 21000)  debit[31]={hex(u(8))} debit[30]={hex(u(16))} debit[0]={u(24)}")
sys.exit(0 if ok else 1)
PY
echo; echo "==> PASS: sender_debit_from_gas = receipt_inc*eff_gas_price + value"
