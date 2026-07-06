#!/usr/bin/env bash
# codegen-zisk-creation-runtime-windows-check.sh
#
# Exercise the top-level creation runtime-window helper. The supported STOP
# constructor must fill receipt/gas/log windows, while unsupported constructor
# shapes must leave runtime_count at zero.
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

echo "==> emit zisk_creation_runtime_windows ELF"
lake exe codegen --program zisk_creation_runtime_windows --halt linux93 \
  -o gen-out/zisk_creation_runtime_windows

: > gen-out/zisk_creation_runtime_windows.input
rm -f gen-out/zisk_creation_runtime_windows.output
"$ZISKEMU" -e gen-out/zisk_creation_runtime_windows.elf \
  -i gen-out/zisk_creation_runtime_windows.input \
  -o gen-out/zisk_creation_runtime_windows.output -n 10000000 \
  >gen-out/zisk_creation_runtime_windows.emu.log 2>&1 || true

python3 - <<'PYCASE'
from pathlib import Path
import struct, sys
out_path = Path('gen-out/zisk_creation_runtime_windows.output')
if not out_path.exists():
    print('missing ziskemu output; tail log:', file=sys.stderr)
    print(Path('gen-out/zisk_creation_runtime_windows.emu.log').read_text()[-2000:], file=sys.stderr)
    sys.exit(1)
out = out_path.read_bytes()
if len(out) < 200:
    out += b'\x00' * (200 - len(out))
words = [struct.unpack_from('<Q', out, i * 8)[0] for i in range(25)]
expected = [
    0,      # supported helper status
    1,      # runtime_count after supported
    1,      # tx status
    53000,  # gas left
    0,      # refund
    0,      # calldata floor
    0,      # log window start
    0,      # log window count
    6,      # receipts completeness shape
    0,      # receipts enforcement disabled
    0,      # tx exec state gas
    4, 0,   # non-STOP unsupported, runtime_count remains 0
    1, 0,   # bad context status, runtime_count remains 0
    2, 0,   # non-creation status, runtime_count remains 0
    3, 0,   # null initcode status, runtime_count remains 0
    3, 0,   # long initcode status, runtime_count remains 0
    1,      # created-account nonstorage effect count
    0xA5,   # created effect address first byte
    0x42,   # copied post-balance first byte
    1,      # created account post nonce
]
labels = [
    'supported_status', 'supported_runtime_count', 'tx_status', 'gas_left',
    'refund', 'calldata_floor', 'log_start', 'log_count', 'receipt_shape',
    'receipt_enforce', 'exec_state_gas', 'non_stop_status', 'non_stop_count',
    'bad_context_status', 'bad_context_count', 'non_creation_status',
    'non_creation_count', 'null_initcode_status', 'null_initcode_count',
    'long_initcode_status', 'long_initcode_count', 'nse_effect_count',
    'nse_created_addr0', 'nse_created_post_balance0', 'nse_created_post_nonce',
]
failed = False
for label, got, exp in zip(labels, words, expected):
    if got == exp:
        print(f'  OK   {label:24s} got=0x{got:x}')
    else:
        print(f'  FAIL {label:24s} got=0x{got:x} exp=0x{exp:x}')
        failed = True
if failed:
    sys.exit(1)
print('\n==> PASS: creation runtime windows fill supported STOP and keep unsupported shapes conservative')
PYCASE
