#!/usr/bin/env bash
# codegen-zisk-eip8037-tx-state-gas-net-array-check.sh
#
# Focused probe for block_verdict_eip8037_tx_state_gas_net_array. It checks the
# array form of the EIP-8037 tx_state_gas settlement used by the block verdict
# exact gas-used gate substrate.
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else
    echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2
    exit 1
  fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_eip8037_tx_state_gas_net_array ELF"
lake exe codegen --program zisk_eip8037_tx_state_gas_net_array --halt linux93 \
  -o gen-out/zisk_eip8037_tx_state_gas_net_array

: > gen-out/zisk_eip8037_tx_state_gas_net_array.input
rm -f gen-out/zisk_eip8037_tx_state_gas_net_array.output
"$ZISKEMU" -e gen-out/zisk_eip8037_tx_state_gas_net_array.elf \
  -i gen-out/zisk_eip8037_tx_state_gas_net_array.input \
  -o gen-out/zisk_eip8037_tx_state_gas_net_array.output -n 5000000 \
  >gen-out/zisk_eip8037_tx_state_gas_net_array.emu.log 2>&1 || true

python3 - <<'INNER'
from pathlib import Path
import struct
out = Path('gen-out/zisk_eip8037_tx_state_gas_net_array.output').read_bytes()
if len(out) < 48:
    raise SystemExit('FAIL: short output')
vals = list(struct.unpack('<6Q', out[:48]))
# v0.6 identity (fork.py:1174): tx_state_gas = intrinsic + executed, no refund.
expected = [0, 0, 183600, 281520, 97920, 0]
if vals != expected:
    print('FAIL: unexpected output')
    print('  actual  ', vals)
    print('  expected', expected)
    raise SystemExit(1)
print('  OK net-state-gas array values:', vals)
INNER

echo "==> PASS: EIP-8037 net per-tx state-gas array matches scalar settlement"
