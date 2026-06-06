#!/usr/bin/env bash
# codegen-zisk-tx-extract-nonce-and-gas-check.sh -- PR-K102.
#
# Extract (nonce, gas_limit) from any tx type.
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

echo "==> emit zisk_tx_extract_nonce_and_gas ELF"
lake exe codegen --program zisk_tx_extract_nonce_and_gas --halt linux93 \
  -o gen-out/zisk_tx_extract_nonce_and_gas

REPO_ROOT="$(pwd)"

# run_case <name> <tx_type> <nonce> <gas_limit> <expected_status>
run_case() {
  local name="$1" t="$2" nonce="$3" gas="$4" exp="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_extract_nonce_and_gas_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_extract_nonce_and_gas_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
tx_type = '$t'
nonce = $nonce
gas = $gas
ALICE = bytes([0xaa]*20)
R = int.from_bytes(bytes([0x11]*32), 'big')
S = int.from_bytes(bytes([0x22]*32), 'big')

if tx_type == 'legacy':
    tx = [nonce, 10**9, gas, ALICE, 10**18, b'', 27, R, S]
    tx_bytes = rlp.encode(tx)
elif tx_type == 'eip2930':
    inner = [1, nonce, 10**9, gas, ALICE, 10**18, b'', [], 1, R, S]
    tx_bytes = b'\x01' + rlp.encode(inner)
elif tx_type == 'eip1559':
    inner = [1, nonce, 10**9, 2*10**9, gas, ALICE, 10**18, b'', [], 1, R, S]
    tx_bytes = b'\x02' + rlp.encode(inner)
elif tx_type == 'eip4844':
    H = bytes([0x01] + [0xab]*31)
    inner = [
        1, nonce, 10**9, 2*10**9, gas,
        ALICE, 10**18, b'', [],
        1, [H], 0, R, S,
    ]
    tx_bytes = b'\x03' + rlp.encode(inner)
elif tx_type == 'eip7702':
    auth_list = [[1, ALICE, 0, 27, R, S]]
    inner = [1, nonce, 10**9, 2*10**9, gas, ALICE, 10**18, b'', [], auth_list, 1, R, S]
    tx_bytes = b'\x04' + rlp.encode(inner)
else:
    raise ValueError(tx_type)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(tx_bytes)))
    f.write(tx_bytes)
    pad = (-(8 + len(tx_bytes))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_tx_extract_nonce_and_gas.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_tx_extract_nonce_and_gas_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_nonce; actual_nonce="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_gas; actual_gas="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$exp').to_bytes(8, 'little').hex())")"
  local exp_nonce="$nonce" exp_gas="$gas"
  if [[ "$exp" != "0" ]]; then
    exp_nonce=0
    exp_gas=0
  fi
  local exp_nonce_le; exp_nonce_le="$(python3 -c "print(int('$exp_nonce').to_bytes(8, 'little').hex())")"
  local exp_gas_le; exp_gas_le="$(python3 -c "print(int('$exp_gas').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" && "$actual_nonce" == "$exp_nonce_le" && "$actual_gas" == "$exp_gas_le" ]]; then
    printf "  %-32s OK   status=%s nonce=%s gas=%s\n" "$name" "$exp" "$exp_nonce" "$exp_gas"
    return 0
  else
    printf "  %-32s FAIL status=0x%s nonce=0x%s gas=0x%s\n" "$name" "$actual_status" "$actual_nonce" "$actual_gas"
    return 1
  fi
}

FAILED=0
run_case "legacy_small"   legacy   42      21000      0 || FAILED=1
run_case "legacy_large"   legacy   999999  30000000   0 || FAILED=1
run_case "eip2930"        eip2930  7       50000      0 || FAILED=1
run_case "eip1559"        eip1559  100     200000     0 || FAILED=1
run_case "eip4844"        eip4844  5       100000     0 || FAILED=1
run_case "eip7702"        eip7702  1       150000     0 || FAILED=1
# Edge: nonce 0 and gas at u32 max — valid u64
run_case "legacy_zero_nonce" legacy 0      0          0 || FAILED=1
# EIP-2681: nonce must be strictly below u64 max.
run_case "legacy_nonce_max_minus_one" legacy 18446744073709551614 21000 0 || FAILED=1
run_case "legacy_nonce_max_reject"    legacy 18446744073709551615 21000 4 || FAILED=1
run_case "eip7702_nonce_max_reject"   eip7702 18446744073709551615 150000 4 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_extract_nonce_and_gas returns correct fields across all tx types"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
