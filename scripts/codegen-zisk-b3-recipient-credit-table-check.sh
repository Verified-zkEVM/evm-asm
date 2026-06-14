#!/usr/bin/env bash
# codegen-zisk-b3-recipient-credit-table-check.sh -- bead bmvmx.5.5.2.3.1.
# Checks B3.1 recipient credit aggregation by 20-byte recipient address.
# Known answer: A=5+7=12, B=0+1=1, C=2, preserving first-seen order.
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
echo "==> emit zisk_b3_recipient_credit_table ELF"
lake exe codegen --program zisk_b3_recipient_credit_table --halt linux93 -o gen-out/zisk_b3_recipient_credit_table
: > gen-out/zisk_b3_recipient_credit_table.input
"$ZISKEMU" -e gen-out/zisk_b3_recipient_credit_table.elf -i gen-out/zisk_b3_recipient_credit_table.input -o gen-out/zisk_b3_recipient_credit_table.output -n 100000000 >gen-out/zisk_b3_recipient_credit_table.emu.log 2>&1
python3 - <<\PY
import struct, sys
path = "gen-out/zisk_b3_recipient_credit_table.output"
d = open(path, "rb").read()
def u(o):
    return struct.unpack("<Q", d[o:o+8])[0] if o + 8 <= len(d) else None
expected = [0, 3, 0x11, 12, 0x22, 1, 0x33, 2]
actual = [u(i * 8) for i in range(len(expected))]
print("  " + " ".join(f"w{i}={actual[i]}" for i in range(len(actual))))
sys.exit(0 if actual == expected else 1)
PY
echo; echo "==> PASS: b3 recipient credit table aggregates duplicate and zero-value rows"
