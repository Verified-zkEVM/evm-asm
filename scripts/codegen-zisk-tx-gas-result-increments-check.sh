#!/usr/bin/env bash
# codegen-zisk-tx-gas-result-increments-check.sh -- verify EIP-7623/EIP-7778
# post-execution transaction gas increments.
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

echo "==> emit zisk_tx_gas_result_increments ELF"
lake exe codegen --program zisk_tx_gas_result_increments --halt linux93 \
  -o gen-out/zisk_tx_gas_result_increments

REPO_ROOT="$(pwd)"

# run_case <name> <tx_gas_limit> <gas_left> <refund_counter> <calldata_floor>
run_case() {
  local name="$1" gas_limit="$2" gas_left="$3" refund_counter="$4" calldata_floor="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_gas_result_increments_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_gas_result_increments_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_tx_gas_result_increments_${name}.expected"

  python3 - "$in_file" "$exp_file" <<PY
import struct, sys

gas_limit = int(${gas_limit})
gas_left = int(${gas_left})
refund_counter = int(${refund_counter})
calldata_floor = int(${calldata_floor})

with open(sys.argv[1], "wb") as f:
    for value in (gas_limit, gas_left, refund_counter, calldata_floor):
        f.write(struct.pack("<Q", value))

if gas_left > gas_limit:
    fields = (1, 0, 0, 0, 0)
else:
    before = gas_limit - gas_left
    refund = min(before // 5, refund_counter)
    after = before - refund
    block_inc = max(before, calldata_floor)
    receipt_inc = max(after, calldata_floor)
    fields = (0, block_inc, receipt_inc, before, refund)

with open(sys.argv[2], "wb") as f:
    for value in fields:
        f.write(struct.pack("<Q", value))
PY

  "$ZISKEMU" -e gen-out/zisk_tx_gas_result_increments.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_tx_gas_result_increments_${name}.emu.log" 2>&1 || true

  local actual expected
  actual="$(xxd -p -l 40 "$out_file" | tr -d '\n')"
  expected="$(xxd -p -l 40 "$exp_file" | tr -d '\n')"
  if [[ "$actual" != "$expected" ]]; then
    printf "  %-28s FAIL\n" "$name"
    printf "    expected: %s\n    actual:   %s\n" "$expected" "$actual"
    printf "    emulator log: %s\n" "$REPO_ROOT/gen-out/zisk_tx_gas_result_increments_${name}.emu.log"
    return 1
  fi

  local status block_inc receipt_inc before refund
  status="$(od -An -tu8 -j 0 -N 8 "$out_file" | tr -d ' \n')"
  block_inc="$(od -An -tu8 -j 8 -N 8 "$out_file" | tr -d ' \n')"
  receipt_inc="$(od -An -tu8 -j 16 -N 8 "$out_file" | tr -d ' \n')"
  before="$(od -An -tu8 -j 24 -N 8 "$out_file" | tr -d ' \n')"
  refund="$(od -An -tu8 -j 32 -N 8 "$out_file" | tr -d ' \n')"
  printf "  %-28s OK   status=%s block=%s receipt=%s before=%s refund=%s\n" \
    "$name" "$status" "$block_inc" "$receipt_inc" "$before" "$refund"
  return 0
}

FAILED=0

run_case "no_refund_above_floor"      100000 70000 0     21000 || FAILED=1
run_case "refund_cap_applied"         100000 70000 10000 21000 || FAILED=1
run_case "refund_counter_below_cap"   100000 50000 3000  21000 || FAILED=1
run_case "floor_dominates_both"        50000 40000 5000  21000 || FAILED=1
run_case "floor_dominates_receipt"    100000 76000 10000 21000 || FAILED=1
run_case "zero_execution_floor"        50000 50000 0     21000 || FAILED=1
run_case "gas_left_gt_limit"           21000 21001 0     21000 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_gas_result_increments matches execution-spec gas increments"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
