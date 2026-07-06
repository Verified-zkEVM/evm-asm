#!/usr/bin/env bash
# codegen-zisk-capture-exec-state-gas-check.sh
#
# Unit-check dispatcher_capture_exec_state_gas: persist the EXECUTED state gas
# (evm_state_gas_used global) into the per-tx strided bvgr_tx_exec_state_gas
# array at a caller-supplied transaction index. The probe captures three
# distinct values at distinct indices (0, 17, 1023 = last entry) and asserts the
# value landed, the 8-byte stride is correct, and an untouched entry stays 0.
#
# Substrate half of the EIP-7778 2D state-dimension gate (fork.py:584-598): the
# verdict gate (c1's lane) consumes this array as the EXECUTION-derived state
# term `tx_output.state_gas_used` per fork.py:1194-1202, replacing the
# intrinsic-only (too-lenient) state budget.
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

mkdir -p gen-out
echo "==> lake build codegen"
lake build codegen >/dev/null
echo "==> emit zisk_capture_exec_state_gas ELF"
lake exe codegen --program zisk_capture_exec_state_gas --halt linux93 \
  -o gen-out/zisk_capture_exec_state_gas

: > gen-out/zisk_capture_exec_state_gas.input
"$ZISKEMU" -e gen-out/zisk_capture_exec_state_gas.elf \
  -i gen-out/zisk_capture_exec_state_gas.input \
  -o gen-out/zisk_capture_exec_state_gas.output -n 2000000 \
  >gen-out/zisk_capture_exec_state_gas.emu.log 2>&1 || true

python3 - <<'PY'
import struct, sys
d = open('gen-out/zisk_capture_exec_state_gas.output', 'rb').read()
def u(o): return struct.unpack('<Q', d[o:o+8])[0] if o + 8 <= len(d) else None
checks = [
    ('bvgr_tx_exec_state_gas[0]',         0x1111),
    ('bvgr_tx_exec_state_gas[17] (>16)',  0x2222),
    ('bvgr_tx_exec_state_gas[1023] (last)', 0x3333),
    ('bvgr_tx_exec_state_gas[1] (untouched)', 0),
]
failed = False
for i, (label, exp) in enumerate(checks):
    got = u(i * 8)
    ok = got == exp
    failed = failed or not ok
    gs = 'None' if got is None else hex(got)
    print(f"  {'OK  ' if ok else 'FAIL'} {label:38s} got={gs} exp={hex(exp)}")
sys.exit(1 if failed else 0)
PY

echo
echo "==> PASS: dispatcher_capture_exec_state_gas persists evm_state_gas_used into"
echo "          bvgr_tx_exec_state_gas[i] (correct value, stride, untouched-zero)"
