#!/usr/bin/env bash
# codegen-zisk-u256-from-u64-be-check.sh -- PR-K56.
#
# Zero-extend a u64 value into a 32-byte BE u256 buffer.
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

echo "==> emit zisk_u256_from_u64_be ELF"
lake exe codegen --program zisk_u256_from_u64_be --halt linux93 \
  -o gen-out/zisk_u256_from_u64_be

REPO_ROOT="$(pwd)"

# run_case <name> <value_dec>
run_case() {
  local name="$1" value="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_u256_from_u64_be_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_u256_from_u64_be_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_u256_from_u64_be_${name}.expected"

  python3 -c "
import struct, sys
v = $value
out = struct.pack('<Q', v)  # u64 LE, since asm uses ld
sys.stdout.buffer.write(out)
" > "$in_file"

  python3 -c "
import sys
v = $value
sys.stdout.buffer.write(v.to_bytes(32, 'big'))
" > "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_u256_from_u64_be.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_u256_from_u64_be_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 32 "$out_file" | tr -d '\n')"
  local expected; expected="$(xxd -p -l 32 "$exp_file" | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-30s OK   value=%s\n" "$name" "$value"
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

MAX64=18446744073709551615
GAS_30M=30000000

FAILED=0
# Edge values
run_case "zero"                   0          || FAILED=1
run_case "one"                    1          || FAILED=1
run_case "255"                    255        || FAILED=1
run_case "256"                    256        || FAILED=1
run_case "two_to_15"              32768      || FAILED=1
run_case "two_to_16"              65536      || FAILED=1
run_case "two_to_24"              16777216   || FAILED=1
run_case "two_to_31"              2147483648 || FAILED=1
run_case "two_to_32"              4294967296 || FAILED=1
run_case "max_u32"                4294967295 || FAILED=1
# Realistic Ethereum values
run_case "gas_21k"                21000      || FAILED=1
run_case "gas_30M"                "$GAS_30M" || FAILED=1
run_case "typical_nonce"          12345      || FAILED=1
run_case "block_number_19M"       19000000   || FAILED=1
run_case "timestamp_2026"         1779580800 || FAILED=1
# Limb-boundary values
run_case "two_to_56"              $(python3 -c "print(1 << 56)") || FAILED=1
run_case "max_u64_minus_1"        $(python3 -c "print((1 << 64) - 2)") || FAILED=1
run_case "max_u64"                "$MAX64"   || FAILED=1
# Pseudo-random values
run_case "0xdeadbeef_cafebabe"    $(python3 -c "print(0xdeadbeef_cafebabe)") || FAILED=1
run_case "all_alternating_bits"   $(python3 -c "print(0xaaaaaaaaaaaaaaaa)") || FAILED=1
run_case "byte_pattern"           $(python3 -c "print(0x0123456789abcdef)") || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: u256_from_u64_be matches Python's int.to_bytes(32, 'big') for 21 fixtures"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
