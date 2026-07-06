#!/usr/bin/env bash
# codegen-zisk-multi-tx-actual-sender-debit-check.sh -- B2.1 actual sender debit.
#
# For one multi-tx context row, compute the actual post-exec sender debit from
# the dispatcher-settled runtime gas tuple:
#
#   debit = receipt_inc * effective_gas_price + value
#
# where receipt_inc is EIP-3529-refunded and EIP-7623-floored. The gas_left
# input is already the dispatcher-settled value, so EIP-8037 state-gas reservoir
# effects are represented by reducing that value before this helper runs.
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

echo "==> emit zisk_multi_tx_actual_sender_debit ELF"
lake exe codegen --program zisk_multi_tx_actual_sender_debit --halt linux93 \
  -o gen-out/zisk_multi_tx_actual_sender_debit

REPO_ROOT="$(pwd)"

# run_case <name> <gas_limit> <settled_gas_left> <refund_counter> <floor> <egp> <value>
run_case() {
  local name="$1" gas_limit="$2" gas_left="$3" refund_counter="$4" floor="$5" egp="$6" value="$7"

  local in_file="$REPO_ROOT/gen-out/zisk_multi_tx_actual_sender_debit_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_multi_tx_actual_sender_debit_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_multi_tx_actual_sender_debit_${name}.expected"

  python3 - "$in_file" "$exp_file" <<PY
import struct, sys

gas_limit = int(${gas_limit})
gas_left = int(${gas_left})
refund_counter = int(${refund_counter})
floor = int(${floor})
egp = int(${egp})
value = int(${value})
MOD = 1 << 256

with open(sys.argv[1], "wb") as f:
    for x in (gas_limit, gas_left, refund_counter, floor):
        f.write(struct.pack("<Q", x))
    f.write(egp.to_bytes(32, "big"))
    f.write(value.to_bytes(32, "big"))

if gas_left > gas_limit:
    status = 1
    receipt_inc = 0
    debit = 0
else:
    before = gas_limit - gas_left
    refund = min(before // 5, refund_counter)
    after = before - refund
    receipt_inc = max(after, floor)
    debit = (receipt_inc * egp + value) % MOD
    status = 0

with open(sys.argv[2], "wb") as f:
    f.write(struct.pack("<Q", status))
    f.write(struct.pack("<Q", receipt_inc))
    f.write(debit.to_bytes(32, "big"))
PY

  "$ZISKEMU" -e gen-out/zisk_multi_tx_actual_sender_debit.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_multi_tx_actual_sender_debit_${name}.emu.log" 2>&1 || true

  local actual expected
  actual="$(xxd -p -l 48 "$out_file" | tr -d '\n')"
  expected="$(xxd -p -l 48 "$exp_file" | tr -d '\n')"
  if [[ "$actual" != "$expected" ]]; then
    printf "  %-30s FAIL\n" "$name"
    printf "    expected: %s\n    actual:   %s\n" "$expected" "$actual"
    printf "    emulator log: %s\n" "$REPO_ROOT/gen-out/zisk_multi_tx_actual_sender_debit_${name}.emu.log"
    return 1
  fi

  local status receipt
  status="$(od -An -tu8 -j 0 -N 8 "$out_file" | tr -d ' \n')"
  receipt="$(od -An -tu8 -j 8 -N 8 "$out_file" | tr -d ' \n')"
  printf "  %-30s OK   status=%s receipt_inc=%s\n" "$name" "$status" "$receipt"
  return 0
}

GWEI=$(python3 -c "print(10**9)")

FAILED=0
run_case "partial_refund" 100000 40000 5000 21000 $((2 * GWEI)) 0 || FAILED=1
run_case "calldata_floor" 50000 42000 1000 21000 $GWEI 7 || FAILED=1
run_case "zero_priority_fee" 80000 20000 10000 21000 0 12345 || FAILED=1
run_case "value_transfer" 100000 50000 0 21000 $((3 * GWEI)) 987654321 || FAILED=1
# State-gas-shaped: regular gas_left would be 70000, but dispatcher settlement
# has already folded 20000 state gas into the consumed amount, so the helper sees
# settled gas_left=50000 and charges the corresponding actual debit.
run_case "state_gas_settled" 100000 50000 0 21000 $GWEI 0 || FAILED=1
run_case "gas_left_gt_limit" 21000 21001 0 21000 $GWEI 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: multi_tx_actual_sender_debit derives actual post-exec sender debit"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
