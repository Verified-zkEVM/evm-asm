#!/usr/bin/env bash
# codegen-zisk-call-extra-gas-check.sh -- bead fhsxz.2.4.2.61.6.9.
#
# Focused check for call_extra_gas: the Amsterdam CALL/CALLCODE access +
# value-transfer extra gas (vm/instructions/system.py:444), excluding the
# EIP-8037 new-account state-gas and EIP-7702 delegation. Covers the four
# (is_cold, value_nonzero) cases against GasCosts WARM_ACCESS=100,
# COLD_ACCOUNT_ACCESS=2600, CALL_VALUE=9000.
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

echo "==> emit zisk_call_extra_gas ELF"
lake exe codegen --program zisk_call_extra_gas --halt linux93 -o gen-out/zisk_call_extra_gas

: > gen-out/zisk_call_extra_gas.input
"$ZISKEMU" -e gen-out/zisk_call_extra_gas.elf \
  -i gen-out/zisk_call_extra_gas.input -o gen-out/zisk_call_extra_gas.output -n 100000000 \
  >gen-out/zisk_call_extra_gas.emu.log 2>&1

python3 - <<'PY'
import struct, sys
data = open('gen-out/zisk_call_extra_gas.output', 'rb').read()
checks = [
    ('warm, no value (100)',      100),
    ('cold, no value (2600)',     2600),
    ('warm, value (100+9000)',    9100),
    ('cold, value (2600+9000)',   11600),
]
failed = False
for i, (label, exp) in enumerate(checks):
    off = i * 8
    got = struct.unpack('<Q', data[off:off+8])[0] if off + 8 <= len(data) else None
    ok = got == exp
    failed = failed or not ok
    print(f"  {'OK  ' if ok else 'FAIL'} {label:28s} got={got} exp={exp}")
sys.exit(1 if failed else 0)
PY

echo
echo "==> PASS: call_extra_gas matches access (warm/cold) + value-transfer gas"
