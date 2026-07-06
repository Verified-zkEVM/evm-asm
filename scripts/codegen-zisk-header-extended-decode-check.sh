#!/usr/bin/env bash
# codegen-zisk-header-extended-decode-check.sh -- PR-K39.
#
# Decode 9 header fields: parent_hash, state_root, number,
# timestamp, gas_limit, gas_used, base_fee_per_gas, blob_gas_used,
# excess_blob_gas.
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

echo "==> emit zisk_header_extended_decode ELF"
lake exe codegen --program zisk_header_extended_decode --halt linux93 \
  -o gen-out/zisk_header_extended_decode

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" parent_hex="$2" state_root_hex="$3" number="$4" timestamp="$5" gas_limit="$6" gas_used="$7" base_fee="$8" blob_gas_used="$9" excess_blob_gas="${10}"

  local in_file="$REPO_ROOT/gen-out/zisk_header_extended_decode_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_header_extended_decode_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_header_extended_decode_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp

parent_hash = bytes.fromhex('$parent_hex')
state_root = bytes.fromhex('$state_root_hex')
number = $number
timestamp = $timestamp
gas_limit = $gas_limit
gas_used = $gas_used
base_fee = $base_fee
blob_gas_used = $blob_gas_used
excess_blob_gas = $excess_blob_gas

# Synthetic Amsterdam header with blob-gas fields populated.
fields = [
    parent_hash,    # 0: parent_hash
    b'\x22' * 32,   # 1: ommers_hash
    b'\x33' * 20,   # 2: coinbase
    state_root,     # 3: state_root
    b'\x55' * 32,   # 4: transactions_root
    b'\x66' * 32,   # 5: receipts_root
    b'\x00' * 256,  # 6: bloom
    0,              # 7: difficulty
    number,         # 8: number
    gas_limit,      # 9: gas_limit
    gas_used,       # 10: gas_used
    timestamp,      # 11: timestamp
    b'',            # 12: extra_data
    b'\x77' * 32,   # 13: prev_randao
    b'\x00' * 8,    # 14: nonce
    base_fee,       # 15: base_fee_per_gas
    b'\x88' * 32,   # 16: withdrawals_root
    blob_gas_used,  # 17: blob_gas_used
    excess_blob_gas,# 18: excess_blob_gas
    b'\x99' * 32,   # 19: parent_beacon_block_root
]
header_rlp = rlp.encode(fields)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(header_rlp)))
    f.write(header_rlp)
    pad = (-(8 + len(header_rlp))) % 8
    if pad:
        f.write(b'\x00' * pad)

expected = struct.pack('<Q', 0)
expected += parent_hash
expected += state_root
expected += struct.pack('<Q', number)
expected += struct.pack('<Q', timestamp)
expected += struct.pack('<Q', gas_limit)
expected += struct.pack('<Q', gas_used)
expected += base_fee.to_bytes(32, 'big')
expected += struct.pack('<Q', blob_gas_used)
expected += struct.pack('<Q', excess_blob_gas)
with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_header_extended_decode.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_header_extended_decode_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-26s OK   #%s gas=%s/%s basefee=%s blob=%s excess=%s\n" "$name" "$number" "$gas_used" "$gas_limit" "$base_fee" "$blob_gas_used" "$excess_blob_gas"
    return 0
  else
    printf "  %-26s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected" "$actual"
    return 1
  fi
}

PARENT="$(printf '11%.0s' $(seq 1 32))"
STATE_ROOT="$(printf '44%.0s' $(seq 1 32))"

FAILED=0
run_case "amsterdam_typical"    "$PARENT" "$STATE_ROOT" 1234567 1700000000 30000000  15000000  1000000000  1835008 0       || FAILED=1
run_case "low_base_fee"         "$PARENT" "$STATE_ROOT" 1       1000       30000000  0         7           0       0       || FAILED=1
run_case "high_base_fee"        "$PARENT" "$STATE_ROOT" 999999  1700000000 30000000  29999999  115792089237316195423570985008687907853269984665640564039457584007913129639935 2752512 131072 || FAILED=1
run_case "min_gas_used"         "$PARENT" "$STATE_ROOT" 5000    1500000000 8000000   21000     500000000   131072  42      || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: header_extended_decode extracts Amsterdam header fields"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
