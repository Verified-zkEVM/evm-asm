#!/usr/bin/env bash
# codegen-zisk-eip8037-reservoir-split-check.sh
#
# Focused EIP-8037 Amsterdam reservoir split probe. Mirrors execution-specs
# fork.py process_transaction after validate_transaction:
#   execution_gas = tx.gas - (intrinsic.regular + intrinsic.state)
#   regular_gas_budget = TX_MAX_GAS_LIMIT - intrinsic.regular
#   gas = min(regular_gas_budget, execution_gas)
#   state_gas_reservoir = execution_gas - gas
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

echo "==> emit zisk_eip8037_reservoir_split ELF"
lake exe codegen --program zisk_eip8037_reservoir_split --halt linux93 \
  -o gen-out/zisk_eip8037_reservoir_split

REPO_ROOT="$(pwd)"
TX_MAX_GAS_LIMIT=16777216

# run_case <name> <tx_gas> <intrinsic_total> <intrinsic_regular> <expected_status>
run_case() {
  local name="$1" tx_gas="$2" intrinsic_total="$3" intrinsic_regular="$4" expected_status="$5"
  local in_file="$REPO_ROOT/gen-out/zisk_eip8037_reservoir_split_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_eip8037_reservoir_split_${name}.output"

  python3 -c "
import struct, sys
with open(sys.argv[1], 'wb') as f:
    for x in ($tx_gas, $intrinsic_total, $intrinsic_regular):
        f.write(struct.pack('<Q', x))
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_eip8037_reservoir_split.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_eip8037_reservoir_split_${name}.emu.log" 2>&1 || true

  if [[ ! -s "$out_file" ]]; then
    printf "  %-34s FAIL missing output\n" "$name"
    return 1
  fi

  local actual
  actual="$(python3 -c "
import struct, sys
with open(sys.argv[1], 'rb') as f:
    data = f.read(24)
if len(data) < 24:
    raise SystemExit('short output')
print(*struct.unpack('<QQQ', data))
" "$out_file")"

  local expected
  expected="$(python3 -c "
TX_MAX = $TX_MAX_GAS_LIMIT
tx_gas = $tx_gas
intrinsic_total = $intrinsic_total
intrinsic_regular = $intrinsic_regular
if tx_gas < intrinsic_total:
    print(1, 0, 0)
elif intrinsic_regular > TX_MAX:
    print(2, 0, 0)
else:
    execution_gas = tx_gas - intrinsic_total
    regular_budget = TX_MAX - intrinsic_regular
    gas = min(regular_budget, execution_gas)
    print(0, gas, execution_gas - gas)
")"

  local actual_status actual_gas actual_reservoir expected_calc_status expected_gas expected_reservoir
  read -r actual_status actual_gas actual_reservoir <<<"$actual"
  read -r expected_calc_status expected_gas expected_reservoir <<<"$expected"

  if [[ "$expected_calc_status" != "$expected_status" ]]; then
    printf "  %-34s FAIL script expected-status mismatch calc=%s arg=%s\n" "$name" "$expected_calc_status" "$expected_status"
    return 1
  fi

  if [[ "$actual_status" == "$expected_calc_status" && "$actual_gas" == "$expected_gas" && "$actual_reservoir" == "$expected_reservoir" ]]; then
    printf "  %-34s OK   status=%s gas=%s reservoir=%s\n" "$name" "$actual_status" "$actual_gas" "$actual_reservoir"
    return 0
  else
    printf "  %-34s FAIL status=%s/%s gas=%s/%s reservoir=%s/%s\n" \
      "$name" "$actual_status" "$expected_calc_status" "$actual_gas" "$expected_gas" "$actual_reservoir" "$expected_reservoir"
    return 1
  fi
}

FAILED=0
run_case "simple_zero_reservoir"        100000 21000 21000 0 || FAILED=1
run_case "exact_regular_budget"         16777216 21000 21000 0 || FAILED=1
run_case "reservoir_nonzero"            20000000 21000 21000 0 || FAILED=1
run_case "state_intrinsic_subtracted"   20000000 204600 21000 0 || FAILED=1
run_case "floor_like_total_subtracted"  20000000 30000 21000 0 || FAILED=1
run_case "tx_gas_under_intrinsic_total" 20000 21000 21000 1 || FAILED=1
run_case "regular_intrinsic_over_cap"   20000000 17000000 17000000 2 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: EIP-8037 reservoir split matches execution-spec arithmetic"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
