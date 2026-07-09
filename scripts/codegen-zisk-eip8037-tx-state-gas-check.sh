#!/usr/bin/env bash
# codegen-zisk-eip8037-tx-state-gas-check.sh
#
# Focused EIP-8037 Amsterdam per-tx state-gas settlement probe. Mirrors
# execution-specs fork.py process_transaction (~1122-1130, 1194-1202):
#   if creation and (tx_output.error is not None or tx_output.created_target_alive):
#           state_refund += STATE_BYTES_PER_NEW_ACCOUNT * COST_PER_STATE_BYTE
#   tx_state_gas = intrinsic_state_gas + state_gas_used - state_refund
#
# The guest is BAL-replay-only, so state_gas_used / state_refund are supplied
# by the caller's conservative model (zero in the common BAL-replay path).
# This probe exercises the BAL-derivable subset: intrinsic_state_gas plus the
# error-path restore and new-account refund.
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

echo "==> emit zisk_eip8037_tx_state_gas ELF"
lake exe codegen --program zisk_eip8037_tx_state_gas --halt linux93 \
  -o gen-out/zisk_eip8037_tx_state_gas

REPO_ROOT="$(pwd)"
NEW_ACCOUNT_REFUND=183600   # STATE_BYTES_PER_NEW_ACCOUNT(120) * COST_PER_STATE_BYTE(1530)

# run_case <name> <intrinsic_state_gas> <state_gas_used> <state_refund> \
#          <error_flag> <is_creation> <expected_status>
run_case() {
  local name="$1" isg="$2" sgu="$3" srf="$4" err="$5" crt="$6" expected_status="$7"
  local in_file="$REPO_ROOT/gen-out/zisk_eip8037_tx_state_gas_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_eip8037_tx_state_gas_${name}.output"

  python3 -c "
import struct, sys
with open(sys.argv[1], 'wb') as f:
    for x in ($isg, $sgu, $srf, $err, $crt):
        f.write(struct.pack('<Q', x))
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_eip8037_tx_state_gas.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_eip8037_tx_state_gas_${name}.emu.log" 2>&1 || true

  if [[ ! -s "$out_file" ]]; then
    printf "  %-36s FAIL missing output\n" "$name"
    return 1
  fi

  local actual
  actual="$(python3 -c "
import struct, sys
with open(sys.argv[1], 'rb') as f:
    data = f.read(16)
if len(data) < 16:
    raise SystemExit('short output')
print(*struct.unpack('<QQ', data))
" "$out_file")"

  local expected
  expected="$(python3 -c "
NEW_ACCOUNT_REFUND = $NEW_ACCOUNT_REFUND
isg = $isg
sgu = $sgu
srf = $srf
err = $err
crt = $crt
if err != 0 and crt != 0:
    srf += NEW_ACCOUNT_REFUND
total = isg + sgu
if total < srf:
    print(1, 0)
else:
    print(0, total - srf)
")"

  local actual_status actual_tsg expected_calc_status expected_tsg
  read -r actual_status actual_tsg <<<"$actual"
  read -r expected_calc_status expected_tsg <<<"$expected"

  if [[ "$expected_calc_status" != "$expected_status" ]]; then
    printf "  %-36s FAIL script expected-status mismatch calc=%s arg=%s\n" \
      "$name" "$expected_calc_status" "$expected_status"
    return 1
  fi

  if [[ "$actual_status" == "$expected_calc_status" && "$actual_tsg" == "$expected_tsg" ]]; then
    printf "  %-36s OK   status=%s tx_state_gas=%s\n" "$name" "$actual_status" "$actual_tsg"
    return 0
  else
    printf "  %-36s FAIL status=%s/%s tx_state_gas=%s/%s\n" \
      "$name" "$actual_status" "$expected_calc_status" "$actual_tsg" "$expected_tsg"
    return 1
  fi
}

FAILED=0
# success-path tx (error_flag=0): tx_state_gas = intrinsic_state_gas + state_gas_used - state_refund
run_case "success_intrinsic_only"        183600 0 0 0 0 0 || FAILED=1
run_case "success_zero_all"              0 0 0 0 0 0 || FAILED=1
run_case "success_with_runtime_used"     183600 97920 0 0 0 0 || FAILED=1
run_case "success_with_refund"           183600 97920 64000 0 0 0 || FAILED=1
# error path, non-creation: state_gas_used is still counted, no new-account refund
run_case "error_call_keeps_used"        183600 97920 0 1 0 0 || FAILED=1
# error path, creation: state_gas_used kept, refund += 183600
run_case "error_create_refund"           183600 97920 0 1 1 0 || FAILED=1
# error creation where refund cancels intrinsic exactly
run_case "error_create_cancel"           183600 0 0 1 1 0 || FAILED=1
# refund exceeds available -> underflow status 1
run_case "underflow_refund_over"         100 0 5000 0 0 1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: EIP-8037 tx state-gas settlement matches execution-spec arithmetic"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
