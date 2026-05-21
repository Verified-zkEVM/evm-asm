#!/usr/bin/env bash
# codegen-zisk-u256-mul-u64-be-check.sh -- PR-K54.
#
# u256 × u64 → u256 modular multiplication with overflow flag.
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

echo "==> emit zisk_u256_mul_u64_be ELF"
lake exe codegen --program zisk_u256_mul_u64_be --halt linux93 \
  -o gen-out/zisk_u256_mul_u64_be

REPO_ROOT="$(pwd)"

# run_case <name> <a_dec> <b_dec>
run_case() {
  local name="$1" a="$2" b="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_u256_mul_u64_be_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_u256_mul_u64_be_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_u256_mul_u64_be_${name}.expected"

  python3 -c "
import struct, sys
a = $a
b = $b
MOD = 1 << 256
total = a * b
overflow = 1 if total >= MOD else 0
result = total % MOD

with open(sys.argv[1], 'wb') as f:
    f.write(a.to_bytes(32, 'big'))
    f.write(struct.pack('<Q', b))

with open(sys.argv[2], 'wb') as f:
    f.write(struct.pack('<Q', overflow))
    f.write(result.to_bytes(32, 'big'))
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_u256_mul_u64_be.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_u256_mul_u64_be_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    local of; of="$(python3 -c "print(1 if ($a * $b) >= (1<<256) else 0)")"
    printf "  %-30s OK   overflow=%d\n" "$name" "$of"
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

MAX256=115792089237316195423570985008687907853269984665640564039457584007913129639935
MAX64=18446744073709551615
H64=$(python3 -c "print(1 << 64)")
H128=$(python3 -c "print(1 << 128)")
H192=$(python3 -c "print(1 << 192)")
H255=$(python3 -c "print(1 << 255)")
ONE_GWEI=$(python3 -c "print(10**9)")
ONE_ETH=$(python3 -c "print(10**18)")
GAS_30M=30000000
GAS_21K=21000

FAILED=0
# Identities
run_case "zero_x_zero"           0          0          || FAILED=1
run_case "zero_x_one"            0          1          || FAILED=1
run_case "one_x_zero"            1          0          || FAILED=1
run_case "x_x_one"               "$MAX256"  1          || FAILED=1
run_case "one_x_x"               1          "$MAX64"   || FAILED=1
# Small × small
run_case "two_x_three"           2          3          || FAILED=1
run_case "100_x_200"             100        200        || FAILED=1
# Limb-boundary tests
run_case "h64_x_one"             "$H64"     1          || FAILED=1
run_case "h64_x_2"               "$H64"     2          || FAILED=1
run_case "h128_x_2"              "$H128"    2          || FAILED=1
run_case "h192_x_2"              "$H192"    2          || FAILED=1
# Tx-cost-like: max_fee × gas_limit
run_case "1gwei_x_21k_gas"       "$ONE_GWEI" "$GAS_21K" || FAILED=1
run_case "1gwei_x_30M_gas"       "$ONE_GWEI" "$GAS_30M" || FAILED=1
run_case "100gwei_x_30M"         $(python3 -c "print(100 * 10**9)") "$GAS_30M" || FAILED=1
# Realistic mainnet shape: max_fee (in wei, can be u256) * gas_limit (u64)
run_case "1eth_x_2"              "$ONE_ETH" 2          || FAILED=1
# Overflow paths
run_case "max256_x_2"            "$MAX256"  2          || FAILED=1
run_case "max256_x_max64"        "$MAX256"  "$MAX64"   || FAILED=1
run_case "h255_x_2"              "$H255"    2          || FAILED=1
run_case "h255_x_3"              "$H255"    3          || FAILED=1
# Just-below overflow
run_case "max256_div2_x_2"       $(python3 -c "print((1<<256)//2)") 2  || FAILED=1
# Pattern that exercises long carry propagation
ALT_PATTERN=$(python3 -c "print(int.from_bytes(b'\\xff' * 32, 'big'))")
run_case "all_ff_x_2"            "$ALT_PATTERN" 2      || FAILED=1
# Random-looking value
PSEUDO=$(python3 -c "print(int.from_bytes(bytes((i*7+3) & 0xff for i in range(32)), 'big'))")
run_case "pseudo_x_max64"        "$PSEUDO"  "$MAX64"   || FAILED=1
run_case "pseudo_x_31337"        "$PSEUDO"  31337      || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: u256_mul_u64_be matches Python's (a * b) mod 2^256 across 23 fixtures"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
