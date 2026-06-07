#!/usr/bin/env bash
# codegen-zisk-intrinsic-gas-amsterdam-counts-check.sh
#
# Amsterdam intrinsic gas over decoded transaction counts:
# data tokens, creation init-code cost, access-list counts, EIP-7702
# authorization count, EIP-7976 calldata floor, and EIP-7981
# access-list floor tokens.
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

echo "==> emit zisk_intrinsic_gas_amsterdam_counts ELF"
lake exe codegen --program zisk_intrinsic_gas_amsterdam_counts --halt linux93 \
  -o gen-out/zisk_intrinsic_gas_amsterdam_counts

REPO_ROOT="$(pwd)"

# run_case <name> <gas_limit> <is_creation> <access_addrs> <access_slots> <auths> <data_hex>
run_case() {
  local name="$1" gas_limit="$2" is_creation="$3" access_addrs="$4" access_slots="$5" auths="$6" data_hex="$7"

  local in_file="$REPO_ROOT/gen-out/zisk_intrinsic_gas_amsterdam_counts_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_intrinsic_gas_amsterdam_counts_${name}.output"

  python3 -c "
import struct, sys
spec = '$data_hex'
if spec.startswith('repeat:'):
    _, byte_hex, count = spec.split(':')
    b = bytes.fromhex(byte_hex) * int(count)
else:
    b = bytes.fromhex(spec)
with open(sys.argv[1], 'wb') as f:
    for x in (len(b), $is_creation, $gas_limit, $access_addrs, $access_slots, $auths):
        f.write(struct.pack('<Q', x))
    f.write(b)
    pad = (-(48 + len(b))) % 8
    if pad:
        f.write(b'\\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_intrinsic_gas_amsterdam_counts.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_intrinsic_gas_amsterdam_counts_${name}.emu.log" 2>&1 || true

  if [[ ! -s "$out_file" ]]; then
    printf "  %-32s FAIL missing output\n" "$name"
    return 1
  fi

  local actual_status_le actual_intrinsic_le actual_floor_le actual_state_le
  actual_status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  actual_intrinsic_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  actual_floor_le="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  actual_state_le="$(dd if="$out_file" bs=1 skip=24 count=8 2>/dev/null | xxd -p | tr -d '\n')"

  local actual_status actual_intrinsic actual_floor actual_state
  actual_status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_status_le'))[0])")"
  actual_intrinsic="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_intrinsic_le'))[0])")"
  actual_floor="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_floor_le'))[0])")"
  actual_state="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_state_le'))[0])")"

  local expected
  expected="$(python3 -c "
spec = '$data_hex'
if spec.startswith('repeat:'):
    _, byte_hex, count = spec.split(':')
    b = bytes.fromhex(byte_hex) * int(count)
else:
    b = bytes.fromhex(spec)
zeros = b.count(0)
nz = len(b) - zeros
calldata_tokens = zeros + 4 * nz
access_tokens = 80 * $access_addrs + 128 * $access_slots
intrinsic = 21000 + 4 * calldata_tokens
if $is_creation:
    intrinsic += 9000 + 2 * ((len(b) + 31) // 32)
intrinsic += 2400 * $access_addrs + 1900 * $access_slots
intrinsic += 16 * access_tokens
intrinsic += 7500 * $auths
floor = 21000 + 16 * (4 * len(b) + access_tokens)
required = max(intrinsic, floor)
status = 0 if required <= $gas_limit and required <= 16777216 else 1
# EIP-8037 intrinsic state gas: create_state_gas + auth_state_gas
create_state_gas = (120 * 1530) if $is_creation else 0
auth_state_gas = (120 + 23) * 1530 * $auths
state = create_state_gas + auth_state_gas
print(status, intrinsic, floor, state)
")"
  local expected_status expected_intrinsic expected_floor expected_state
  read -r expected_status expected_intrinsic expected_floor expected_state <<<"$expected"

  if [[ "$actual_status" == "$expected_status" && "$actual_intrinsic" == "$expected_intrinsic" && "$actual_floor" == "$expected_floor" && "$actual_state" == "$expected_state" ]]; then
    printf "  %-32s OK   status=%d intrinsic=%d floor=%d state=%d\n" "$name" "$expected_status" "$expected_intrinsic" "$expected_floor" "$expected_state"
    return 0
  else
    printf "  %-32s FAIL status=%s/%s intrinsic=%s/%s floor=%s/%s state=%s/%s\n" \
      "$name" "$actual_status" "$expected_status" "$actual_intrinsic" "$expected_intrinsic" "$actual_floor" "$expected_floor" "$actual_state" "$expected_state"
    return 1
  fi
}

FAILED=0
run_case "empty_call"             21000 0 0 0 0 "" || FAILED=1
run_case "mixed_calldata"         22000 0 0 0 0 "00ff00ff" || FAILED=1
run_case "creation_len33"         60000 1 0 0 0 "$(python3 -c "print('ab' * 33)")" || FAILED=1
run_case "access_list_one_slot"   30000 0 1 1 0 "" || FAILED=1
run_case "access_list_many_slots" 50000 0 2 5 0 "0001" || FAILED=1
run_case "authorization_one"      50000 0 0 0 1 "" || FAILED=1
run_case "authorization_two"      80000 0 0 0 2 "ff" || FAILED=1
run_case "creation_and_auth"      90000 1 0 0 1 "00ab" || FAILED=1
run_case "floor_dominates"        26000 0 0 0 0 "$(python3 -c "print('ff' * 200)")" || FAILED=1
run_case "txmax_floor_cap"        20000000 0 0 0 0 "repeat:ff:262000" || FAILED=1
run_case "one_gas_short"          20999 0 0 0 0 "" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: Amsterdam intrinsic gas/counts and calldata floor match execution-spec arithmetic"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
