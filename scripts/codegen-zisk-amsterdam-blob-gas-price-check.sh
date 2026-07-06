#!/usr/bin/env bash
# codegen-zisk-amsterdam-blob-gas-price-check.sh -- Amsterdam blob gas price.
#
# Mirrors execution-specs:
#   calculate_blob_gas_price(excess_blob_gas)
#     = taylor_exponential(1, excess_blob_gas, 11684671)
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

echo "==> emit zisk_amsterdam_blob_gas_price ELF"
lake exe codegen --program zisk_amsterdam_blob_gas_price --halt linux93 \
  -o gen-out/zisk_amsterdam_blob_gas_price

REPO_ROOT="$(pwd)"

# run_case <name> <excess_blob_gas>
run_case() {
  local name="$1" excess_blob_gas="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_amsterdam_blob_gas_price_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_amsterdam_blob_gas_price_${name}.output"

  python3 -c "
import struct, sys
sys.stdout.buffer.write(struct.pack('<Q', $excess_blob_gas))
" > "$in_file"

  "$ZISKEMU" -e gen-out/zisk_amsterdam_blob_gas_price.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_amsterdam_blob_gas_price_${name}.emu.log" 2>&1 || true

  local expected; expected="$(python3 -c "
D = 11684671
n = $excess_blob_gas
i = 1
output = 0
acc = D
while acc > 0:
    output += acc
    acc = (acc * n) // (D * i)
    i += 1
print(output // D)
")"
  local actual_status actual_price
  actual_status="$(python3 -c "
with open('$out_file', 'rb') as f:
    raw = f.read(8)
print(int.from_bytes(raw, 'little'))
")"
  actual_price="$(python3 -c "
with open('$out_file', 'rb') as f:
    f.seek(8)
    raw = f.read(8)
print(int.from_bytes(raw, 'little'))
")"

  if [[ "$actual_status" == "0" && "$actual_price" == "$expected" ]]; then
    printf "  %-28s OK   excess=%s price=%s\n" "$name" "$excess_blob_gas" "$expected"
    return 0
  else
    printf "  %-28s FAIL excess=%s status=%s expected=%s got=%s\n" \
      "$name" "$excess_blob_gas" "$actual_status" "$expected" "$actual_price"
    return 1
  fi
}

GAS_PER_BLOB=131072
AMSTERDAM_TARGET=$((14 * GAS_PER_BLOB))
AMSTERDAM_MAX=$((21 * GAS_PER_BLOB))

FAILED=0
run_case "zero"                     0 || FAILED=1
run_case "one"                      1 || FAILED=1
run_case "one_blob"                 "$GAS_PER_BLOB" || FAILED=1
run_case "target"                   "$AMSTERDAM_TARGET" || FAILED=1
run_case "max_block_blob_gas"       "$AMSTERDAM_MAX" || FAILED=1
run_case "four_times_target"        $((4 * AMSTERDAM_TARGET)) || FAILED=1
run_case "ten_million"              10000000 || FAILED=1
run_case "hundred_million"          100000000 || FAILED=1
# Regression for evm-asm-7uitv: the old u64-product gate false-rejected these
# (mulhu of accum*numerator exceeded 2**64) even though the spec price fits u64.
# 128-bit-product divide keeps full correctness up to the genuine output-envelope
# overflow near ~3.28e8.
run_case "blob_taylor_134_5m"       134500000 || FAILED=1
run_case "blob_taylor_200m"         200000000 || FAILED=1
run_case "blob_taylor_328m"         328000000 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: Amsterdam blob gas price matches execution-specs taylor_exponential"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
