#!/usr/bin/env bash
# codegen-zisk-eip8037-block-gas-used-check.sh
#
# Focused EIP-8037 Amsterdam block gas_used probe. Mirrors execution-specs
# fork.py block gas accounting:
#   per tx: block_gas_used       += max(tx_regular_gas, intrinsic.calldata_floor)
#           block_state_gas_used += tx_state_gas
#   final:  block_gas_used = max(block_regular, block_state)
#           if block_gas_used != header.gas_used: raise InvalidBlock
#
# The helper accepts the already-resolved per-tx regular increment
# (max(tx_regular_gas, intrinsic.calldata_floor)) and tx_state_gas arrays, since
# the BAL-replay-only guest does not meter opcode execution; this probe checks
# the pure block-level accumulate/max/compare arithmetic.
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

echo "==> emit zisk_eip8037_block_gas_used ELF"
lake exe codegen --program zisk_eip8037_block_gas_used --halt linux93 \
  -o gen-out/zisk_eip8037_block_gas_used

REPO_ROOT="$(pwd)"

# run_case <name> <header_gas_used> <expected_status> <regular_csv> <state_csv>
run_case() {
  local name="$1" header="$2" expected_status="$3" regular_csv="$4" state_csv="$5"
  local in_file="$REPO_ROOT/gen-out/zisk_eip8037_block_gas_used_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_eip8037_block_gas_used_${name}.output"

  python3 -c "
import struct, sys
header = $header
regular = [int(x) for x in '$regular_csv'.split(',') if x != '']
state   = [int(x) for x in '$state_csv'.split(',') if x != '']
assert len(regular) == len(state)
count = len(regular)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', count))
    f.write(struct.pack('<Q', header))
    for x in regular:
        f.write(struct.pack('<Q', x))
    for x in state:
        f.write(struct.pack('<Q', x))
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_eip8037_block_gas_used.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_eip8037_block_gas_used_${name}.emu.log" 2>&1 || true

  if [[ ! -s "$out_file" ]]; then
    printf "  %-34s FAIL missing output\n" "$name"
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
U64 = 1 << 64
header = $header
regular = [int(x) for x in '$regular_csv'.split(',') if x != '']
state   = [int(x) for x in '$state_csv'.split(',') if x != '']
block_regular = 0
block_state = 0
overflow = False
for r, s in zip(regular, state):
    block_regular += r
    block_state += s
    if block_regular >= U64 or block_state >= U64:
        overflow = True
        break
if overflow:
    print(2, 0)
else:
    bgu = max(block_regular, block_state)
    if bgu != header:
        print(1, bgu)
    else:
        print(0, bgu)
")"

  local actual_status actual_bgu expected_calc_status expected_bgu
  read -r actual_status actual_bgu <<<"$actual"
  read -r expected_calc_status expected_bgu <<<"$expected"

  if [[ "$expected_calc_status" != "$expected_status" ]]; then
    printf "  %-34s FAIL script expected-status mismatch calc=%s arg=%s\n" "$name" "$expected_calc_status" "$expected_status"
    return 1
  fi

  if [[ "$actual_status" == "$expected_calc_status" && "$actual_bgu" == "$expected_bgu" ]]; then
    printf "  %-34s OK   status=%s block_gas_used=%s\n" "$name" "$actual_status" "$actual_bgu"
    return 0
  else
    printf "  %-34s FAIL status=%s/%s block_gas_used=%s/%s\n" \
      "$name" "$actual_status" "$expected_calc_status" "$actual_bgu" "$expected_bgu"
    return 1
  fi
}

FAILED=0
# Single tx, regular dominates, header matches.
run_case "single_regular_match"   21000 0 "21000" "0" || FAILED=1
# Single tx, state dominates, header matches.
run_case "single_state_dominates" 204600 0 "21000" "204600" || FAILED=1
# Two txs, regular sum dominates.
run_case "two_tx_regular_sum"     50000 0 "21000,29000" "0,0" || FAILED=1
# Two txs, state sum dominates.
run_case "two_tx_state_sum"       300000 0 "21000,21000" "150000,150000" || FAILED=1
# Header mismatch -> status 1.
run_case "header_mismatch"        99999 1 "21000" "0" || FAILED=1
# Equal regular/state totals, header matches the common value.
run_case "equal_totals"           100000 0 "100000" "100000" || FAILED=1
# Zero transactions: both totals zero, header must be zero.
run_case "empty_block_zero"       0 0 "" "" || FAILED=1
# Overflow accumulating regular -> status 2.
run_case "regular_overflow"       0 2 "18446744073709551615,1" "0,0" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: EIP-8037 block gas_used matches execution-spec arithmetic"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
