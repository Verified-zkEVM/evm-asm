#!/usr/bin/env bash
# Validate the first-transaction context extracted for block_verdict.
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

echo "==> emit zisk_simple_transfer_tx_context ELF"
lake exe codegen --program zisk_simple_transfer_tx_context --halt linux93 \
  -o gen-out/zisk_simple_transfer_tx_context

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
elif tx_kind == 'empty':
    tx_bytes = b''
else:
    raise ValueError(tx_kind)

# ziskemu maps file byte 0 to guest INPUT+8.  The probe's documented
# offsets are guest offsets, so each file offset is guest_offset - 8.
payload = bytearray(440)
struct.pack_into('<Q', payload, 0, len(tx_bytes))
struct.pack_into('<Q', payload, 8, 0)
struct.pack_into('<Q', payload, 16, tx_count)
struct.pack_into('<Q', payload, 24, pubkeys_len)

for i in range(32):
    payload[64 - 8 + 160 + i] = 0x33
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

# run_case <name> <kind> <tx_count> <pubkeys_len> <expected_status> <expected_type> <expected_inner_off>
run_case() {
  local name="$1" kind="$2" tx_count="$3" pubkeys_len="$4" expected_status="$5" expected_type="$6" expected_inner_off="$7"
  local in_file="$REPO_ROOT/gen-out/zisk_simple_transfer_tx_context_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_simple_transfer_tx_context_${name}.output"
  local log_file="$REPO_ROOT/gen-out/zisk_simple_transfer_tx_context_${name}.emu.log"

  make_input "$kind" "$tx_count" "$pubkeys_len" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_simple_transfer_tx_context.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$log_file" 2>&1 || true

  local actual_status actual_type actual_inner_off actual_inner_len
  actual_status="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  actual_type="$(dd if="$out_file" bs=1 skip=160 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  actual_inner_off="$(dd if="$out_file" bs=1 skip=168 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  actual_inner_len="$(dd if="$out_file" bs=1 skip=184 count=8 2>/dev/null | xxd -p | tr -d '\n')"

  local exp_status_le exp_type_le exp_inner_off_le
  exp_status_le="$(le64_hex "$expected_status")"
  exp_type_le="$(le64_hex "$expected_type")"
  exp_inner_off_le="$(le64_hex "$expected_inner_off")"

  if [[ "$actual_status" == "$exp_status_le" && \
        "$actual_type" == "$exp_type_le" && \
        "$actual_inner_off" == "$exp_inner_off_le" ]]; then
    printf "  %-24s OK   status=%s type=%s inner_off=%s inner_len_le=%s\n" \
      "$name" "$expected_status" "$expected_type" "$expected_inner_off" "$actual_inner_len"
    return 0
  fi

  printf "  %-24s FAIL\n" "$name"
  printf "    expected status=%s type=%s inner_off=%s\n" \
    "$expected_status" "$expected_type" "$expected_inner_off"
  printf "    actual   status_le=%s type_le=%s inner_off_le=%s\n" \
    "$actual_status" "$actual_type" "$actual_inner_off"
  printf "    emulator log: %s\n" "$log_file"
  return 1
}

FAILED=0
run_case "legacy_ok"       legacy      1 65 0  0 0 || FAILED=1
run_case "eip1559_ok"      eip1559     1 65 0  2 1 || FAILED=1
run_case "zero_tx"         legacy      0 65 1  0 0 || FAILED=1
run_case "bad_pubkeys_len" legacy      1 64 2  0 0 || FAILED=1
run_case "nonempty_data"   legacy_data 1 65 61 0 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: simple_transfer_tx_context exposes first tx runtime context fields"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
