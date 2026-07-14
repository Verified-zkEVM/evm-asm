#!/usr/bin/env bash
# codegen-zisk-dispatcher-tx-gas-settle-check.sh
#
# Focused coverage for dispatcher_tx_gas_settle, the EIP-8037 fold used by
# dispatch_tx_runtime_code before block-verdict gas-result consumers compute
# tx.gas - effective_gas_left.
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

echo "==> emit zisk_dispatcher_tx_gas_settle ELF"
lake exe codegen --program zisk_dispatcher_tx_gas_settle --halt linux93 \
  -o gen-out/zisk_dispatcher_tx_gas_settle

REPO_ROOT="$(pwd)"

# run_case <name> <halt_kind> <gas_left> <state_left> <refund> <state_used> <state_spilled>
run_case() {
  local name="$1" halt="$2" gas="$3" state_left="$4" refund="$5" state_used="$6" state_spilled="$7"
  local in_file="$REPO_ROOT/gen-out/zisk_dispatcher_tx_gas_settle_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_dispatcher_tx_gas_settle_${name}.output"

  python3 -c "
import struct, sys
vals = [$halt, $gas, $state_left, $refund, $state_used, $state_spilled]
with open(sys.argv[1], 'wb') as f:
    for v in vals:
        f.write(struct.pack('<Q', v))
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_dispatcher_tx_gas_settle.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_dispatcher_tx_gas_settle_${name}.emu.log" 2>&1 || true

  if [[ ! -s "$out_file" ]]; then
    printf "  %-24s FAIL missing output\n" "$name"
    return 1
  fi

  python3 - "$out_file" "$name" "$halt" "$gas" "$state_left" "$refund" "$state_used" "$state_spilled" <<'PY'
import struct, sys
out_file, name = sys.argv[1], sys.argv[2]
halt, gas, state_left, refund, state_used, state_spilled = map(int, sys.argv[3:])
data = open(out_file, "rb").read()
actual = struct.unpack("<QQQ", data[:24])
if halt in (0, 1, 5):
    expected = (gas + state_left, refund, 1)
else:
    non_spilled_used = max(0, state_used - state_spilled)
    if halt == 2:
        expected = (gas + state_spilled + state_left + non_spilled_used, 0, 0)
    else:
        expected = (state_left, 0, 0)
ok = actual == expected
print(
    f"  {name:24s} {'OK  ' if ok else 'FAIL'} "
    f"got={actual} exp={expected}"
)
raise SystemExit(0 if ok else 1)
PY
}

FAILED=0
run_case "stop_success"        0 1000 70 9 555    0 || FAILED=1
run_case "return_success"      1 2222 33 4 777    0 || FAILED=1
run_case "selfdestruct_ok"     5 1234 66 8 111    0 || FAILED=1
run_case "revert_restores"     2 1000 70 9 55     0 || FAILED=1
run_case "revert_spilled"      2 1000  0 9 183600 183600 || FAILED=1
run_case "invalid_burns_gas"   3 1000 70 9 55     0 || FAILED=1
run_case "outofgas_burns"      6 4444 12 3 34     0 || FAILED=1
run_case "outofgas_spilled"    6 1000  0 3 183600 183600 || FAILED=1
run_case "outofgas_mixed_used" 6 1000 11 3 183600 180000 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: dispatcher_tx_gas_settle folds EIP-8037 state gas and tx errors"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
