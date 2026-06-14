#!/usr/bin/env bash
# codegen-zisk-b3-coinbase-fee-credit-sum-check.sh -- bead bmvmx.5.5.2.3.2.
# Checks B3.2 coinbase fee aggregation over multiple transactions:
#   sum_i priority_fee_per_gas[i] * receipt_gas_increment[i]
# Known answer: 2*21000 + 3*100 + 0*999 = 42300 (0xa53c).
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
echo "==> emit zisk_b3_coinbase_fee_credit_sum ELF"
lake exe codegen --program zisk_b3_coinbase_fee_credit_sum --halt linux93 -o gen-out/zisk_b3_coinbase_fee_credit_sum
: > gen-out/zisk_b3_coinbase_fee_credit_sum.input
"$ZISKEMU" -e gen-out/zisk_b3_coinbase_fee_credit_sum.elf -i gen-out/zisk_b3_coinbase_fee_credit_sum.input -o gen-out/zisk_b3_coinbase_fee_credit_sum.output -n 100000000 >gen-out/zisk_b3_coinbase_fee_credit_sum.emu.log 2>&1
python3 - <<\PY
import struct, sys
path = "gen-out/zisk_b3_coinbase_fee_credit_sum.output"
d = open(path, "rb").read()
def u(o):
    return struct.unpack("<Q", d[o:o+8])[0] if o + 8 <= len(d) else None
ok = (
    u(0) == 0 and
    u(8) == 0x3c and
    u(16) == 0xa5 and
    u(24) == 0 and
    u(32) == 0 and
    u(40) == 0
)
print(f"  status={u(0)} total[31]={hex(u(8) or 0)} total[30]={hex(u(16) or 0)} total[0]={u(24)} zero_status={u(32)} zero_low={u(40)}")
sys.exit(0 if ok else 1)
PY
echo; echo "==> PASS: b3 coinbase fee credit sum aggregates multi-tx priority fees"
