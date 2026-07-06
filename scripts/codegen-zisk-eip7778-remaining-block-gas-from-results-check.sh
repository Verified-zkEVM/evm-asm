#!/usr/bin/env bash
# codegen-zisk-eip7778-remaining-block-gas-from-results-check.sh -- derive
# EIP-7778 block-gas availability inputs from runtime transaction gas results.
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

echo "==> emit zisk_eip7778_remaining_block_gas_from_results ELF"
lake exe codegen --program zisk_eip7778_remaining_block_gas_from_results --halt linux93 \
  -o gen-out/zisk_eip7778_remaining_block_gas_from_results

REPO_ROOT="$(pwd)"

# run_case <name> <block_gas_limit> <tx_gases_csv> <gas_left_csv> <refunds_csv> <floors_csv>
run_case() {
  local name="$1" limit="$2" tx_gases="$3" gas_left="$4" refunds="$5" floors="$6"
  local in_file="$REPO_ROOT/gen-out/zisk_eip7778_from_results_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_eip7778_from_results_${name}.output"
  local expected_file="$REPO_ROOT/gen-out/zisk_eip7778_from_results_${name}.expected.hex"

  python3 - "$in_file" "$expected_file" "$limit" "$tx_gases" "$gas_left" "$refunds" "$floors" <<'EOF_PY'
import struct
import sys

(
    in_file,
    expected_file,
    limit_s,
    tx_gases_s,
    gas_left_s,
    refunds_s,
    floors_s,
) = sys.argv[1:]

U64_MASK = (1 << 64) - 1

def parse_csv(s: str) -> list[int]:
    if not s:
        return []
    return [int(x, 0) for x in s.split(",")]

limit = int(limit_s, 0)
tx_gases = parse_csv(tx_gases_s)
gas_left = parse_csv(gas_left_s)
refunds = parse_csv(refunds_s)
floors = parse_csv(floors_s)
assert len(tx_gases) == len(gas_left) == len(refunds) == len(floors)

payload = bytearray()
payload += struct.pack("<Q", limit)
payload += struct.pack("<Q", len(tx_gases))
for array in (tx_gases, gas_left, refunds, floors):
    for value in array:
        payload += struct.pack("<Q", value)

with open(in_file, "wb") as f:
    f.write(payload)

block_increments = []
expected = None
for index, (tx_gas, remaining, refund_counter, floor) in enumerate(
    zip(tx_gases, gas_left, refunds, floors), start=1
):
    if remaining > tx_gas:
        expected = (3, index, 0)
        break
    before_refund = tx_gas - remaining
    block_increments.append(max(before_refund, floor))

if expected is None:
    used = 0
    expected = (0, 0, 0)
    for index, (tx_gas, inc) in enumerate(zip(tx_gases, block_increments), start=1):
        if tx_gas > limit - used:
            expected = (1, index, used)
            break
        new_used = used + inc
        if new_used > U64_MASK:
            expected = (2, index, used)
            break
        used = new_used
    else:
        expected = (0, 0, used)

with open(expected_file, "w") as f:
    f.write(struct.pack("<QQQ", *expected).hex())
EOF_PY

  "$ZISKEMU" -e gen-out/zisk_eip7778_remaining_block_gas_from_results.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_eip7778_from_results_${name}.emu.log" 2>&1 || true

  local actual expected status index used
  actual="$(dd if="$out_file" bs=1 count=24 2>/dev/null | xxd -p | tr -d '\n')"
  expected="$(cat "$expected_file")"
  status="$(od -An -tu8 -j 0 -N 8 "$out_file" | tr -d ' \n')"
  index="$(od -An -tu8 -j 8 -N 8 "$out_file" | tr -d ' \n')"
  used="$(od -An -tu8 -j 16 -N 8 "$out_file" | tr -d ' \n')"
  if [[ "$actual" == "$expected" ]]; then
    printf "  %-28s OK   status=%s index=%s used=%s\n" "$name" "$status" "$index" "$used"
    return 0
  fi
  printf "  %-28s FAIL status=%s index=%s used=%s\n" "$name" "$status" "$index" "$used"
  printf "      actual:   %s\n" "$actual"
  printf "      expected: %s\n" "$expected"
  printf "      emulator log: %s\n" "$REPO_ROOT/gen-out/zisk_eip7778_from_results_${name}.emu.log"
  return 1
}

FAILED=0
run_case "empty_block" 100000 "" "" "" "" || FAILED=1
run_case "multi_ok" 100000 "60000,40000" "10000,10000" "0,0" "21000,21000" || FAILED=1
run_case "second_tx_exceeds" 100000 "60000,50001" "0,10000" "0,0" "21000,21000" || FAILED=1
run_case "floor_drives_increment" 50000 "30000,20000" "25000,15000" "0,0" "21000,21000" || FAILED=1
run_case "gas_left_gt_limit" 21000 "21000" "21001" "0" "21000" || FAILED=1
run_case "increment_overflow" 18446744073709551615 "1,0" "1,0" "0,0" "18446744073709551615,1" || FAILED=1

if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: EIP-7778 runtime-result block-gas gate"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
