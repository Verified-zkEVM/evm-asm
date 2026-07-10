#!/usr/bin/env bash
# Validate the runtime payload staged from a one-transaction simple-transfer
# context. Stages a pack-bytecode-compatible payload and checks the bytecode
# length, calldata length, gas flag, is_creation flag, witness pointer fields,
# and gas_limit before any dispatch happens.
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

echo "==> emit zisk_stage_runtime_payload ELF"
lake exe codegen --program zisk_stage_runtime_payload --halt linux93 \
  -o gen-out/zisk_stage_runtime_payload

REPO_ROOT="$(pwd)"

le64_hex() {
  python3 -c "print(int('$1').to_bytes(8, 'little').hex())"
}

# make_input <tx_kind> <tx_count> <pubkeys_len> <input_file>
make_input() {
  local tx_kind="$1" tx_count="$2" pubkeys_len="$3" input_file="$4"
  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp

tx_kind = '$tx_kind'
tx_count = int('$tx_count')
pubkeys_len = int('$pubkeys_len')
ALICE = bytes.fromhex('00112233445566778899aabbccddeeff00112233')
R = int.from_bytes(bytes([0x11]) * 32, 'big')
S = int.from_bytes(bytes([0x22]) * 32, 'big')

if tx_kind == 'legacy':
    tx = [1, 10**9, 21000, ALICE, 7, b'', 27, R, S]
    tx_bytes = rlp.encode(tx)
elif tx_kind == 'eip1559':
    inner = [1, 7, 10**9, 2 * 10**9, 21000, ALICE, 7, b'', [], 1, R, S]
    tx_bytes = b'\x02' + rlp.encode(inner)
elif tx_kind == 'legacy_data':
    tx = [1, 10**9, 21000, ALICE, 7, b'\xde\xad', 27, R, S]
    tx_bytes = rlp.encode(tx)
else:
    raise ValueError(tx_kind)

# ziskemu maps file byte 0 to guest INPUT+8; probe offsets are guest offsets,
# so each file offset is guest_offset - 8.
payload = bytearray(632)
struct.pack_into('<Q', payload, 0, len(tx_bytes))
struct.pack_into('<Q', payload, 8, 0)
struct.pack_into('<Q', payload, 16, tx_count)
struct.pack_into('<Q', payload, 24, pubkeys_len)

# base_fee word in the exec payload (@guest +64 + 440 -> file +496).
for i in range(32):
    payload[64 - 8 + 440 + i] = 0x33
# coinbase 20-byte address in exec payload (@guest +64 + 32 -> file +88).
for i in range(20):
    payload[64 - 8 + 32 + i] = (0xa0 + i) & 0xff
# block number u64 (@guest +64 + 404 -> file +460).
struct.pack_into('<Q', payload, 64 - 8 + 404, 0x1234)
# gas_limit u64 (@guest +64 + 412 -> file +468).
struct.pack_into('<Q', payload, 64 - 8 + 412, 0x55aa)
# timestamp u64 (@guest +64 + 428 -> file +484).
struct.pack_into('<Q', payload, 64 - 8 + 428, 0x99)
# prev_randao Bytes32 (@guest +64 + 372 -> file +428), with distinct
# canonical high/low byte markers so the EVM-word reversal is exercised.
payload[64 - 8 + 372] = 0x44
payload[64 - 8 + 403] = 0x55

for i in range(pubkeys_len):
    payload[320 - 8 + i] = (i + 1) & 0xff
payload.extend(tx_bytes)
pad = (-len(payload)) % 8
if pad:
    payload.extend(b'\x00' * pad)

with open(sys.argv[1], 'wb') as f:
    f.write(payload)
" "$input_file"
}

# run_case <name> <kind> <tx_count> <pubkeys_len> \
#          <exp_status> <exp_bc_len> <exp_cd_len> <exp_gas_flag> \
#          <exp_is_creation> <exp_gas_limit>
run_case() {
  local name="$1" kind="$2" tx_count="$3" pubkeys_len="$4"
  local exp_status="$5" exp_bc_len="$6" exp_cd_len="$7" exp_gas_flag="$8"
  local exp_is_creation="$9" exp_gas_limit="${10}"
  local in_file="$REPO_ROOT/gen-out/zisk_stage_runtime_payload_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_stage_runtime_payload_${name}.output"
  local log_file="$REPO_ROOT/gen-out/zisk_stage_runtime_payload_${name}.emu.log"

  make_input "$kind" "$tx_count" "$pubkeys_len" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_stage_runtime_payload.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$log_file" 2>&1 || true

  local a_status a_bc a_cd a_gf a_ic a_hl a_ws a_wc a_gl a_pr
  a_status="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  a_bc="$(dd if="$out_file" bs=1 skip=8  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  a_cd="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  a_gf="$(dd if="$out_file" bs=1 skip=24 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  a_ic="$(dd if="$out_file" bs=1 skip=32 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  a_hl="$(dd if="$out_file" bs=1 skip=40 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  a_ws="$(dd if="$out_file" bs=1 skip=48 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  a_wc="$(dd if="$out_file" bs=1 skip=56 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  a_gl="$(dd if="$out_file" bs=1 skip=64 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  a_pr="$(dd if="$out_file" bs=1 skip=80 count=8 2>/dev/null | xxd -p | tr -d '\n')"

  local e_status e_bc e_cd e_gf e_ic e_gl e_pr e_zero
  e_status="$(le64_hex "$exp_status")"
  e_bc="$(le64_hex "$exp_bc_len")"
  e_cd="$(le64_hex "$exp_cd_len")"
  e_gf="$(le64_hex "$exp_gas_flag")"
  e_ic="$(le64_hex "$exp_is_creation")"
  e_gl="$(le64_hex "$exp_gas_limit")"
  if [[ "$exp_status" == "0" ]]; then
    e_pr="$(le64_hex 85)"
  else
    e_pr="$(le64_hex 0)"
  fi
  e_zero="$(le64_hex 0)"

  if [[ "$a_status" == "$e_status" && "$a_bc" == "$e_bc" && \
        "$a_cd" == "$e_cd" && "$a_gf" == "$e_gf" && \
        "$a_ic" == "$e_ic" && "$a_gl" == "$e_gl" && \
        "$a_pr" == "$e_pr" && "$a_hl" == "$e_zero" && \
        "$a_ws" == "$e_zero" && "$a_wc" == "$e_zero" ]]; then
    printf "  %-22s OK   status=%s bc=%s cd=%s gas_flag=%s creation=%s gas=%s prev_randao=%s\n" \
      "$name" "$exp_status" "$exp_bc_len" "$exp_cd_len" "$exp_gas_flag" \
      "$exp_is_creation" "$exp_gas_limit" "$([[ "$exp_status" == "0" ]] && echo 0x55 || echo 0x00)"
    return 0
  fi

  printf "  %-22s FAIL\n" "$name"
  printf "    expected status=%s bc=%s cd=%s gf=%s ic=%s gl=%s pr=%s witness=0/0/0\n" \
    "$e_status" "$e_bc" "$e_cd" "$e_gf" "$e_ic" "$e_gl" "$e_pr"
  printf "    actual   status=%s bc=%s cd=%s gf=%s ic=%s gl=%s pr=%s witness=%s/%s/%s\n" \
    "$a_status" "$a_bc" "$a_cd" "$a_gf" "$a_ic" "$a_gl" "$a_pr" "$a_hl" "$a_ws" "$a_wc"
  printf "    emulator log: %s\n" "$log_file"
  return 1
}

FAILED=0
# Supported simple transfers: STOP body (bc_len 1), empty calldata, gas flag 1,
# non-creation, gas_limit 21000 (0x5208), zero witness pointers.
run_case "legacy_ok"      legacy      1 65 0 1 0 1 0 21000 || FAILED=1
run_case "eip1559_ok"     eip1559     1 65 0 1 0 1 0 21000 || FAILED=1
# Unsupported context (count != 1) -> stage status 1, no payload staged.
run_case "zero_tx"        legacy      0 65 1 0 0 0 0 0 || FAILED=1
# Non-empty calldata to an EOA is staged with the calldata length preserved; later
# gas/account gates decide whether the transaction is executable.
run_case "nonempty_data"  legacy_data 1 65 0 1 2 1 0 21000 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: stage_runtime_payload stages one tx into the runtime payload ABI"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
