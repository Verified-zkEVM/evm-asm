#!/usr/bin/env bash
# codegen-zisk-validate-header-basic-check.sh -- PR-K43.
#
# Per-header u64 semantic invariants from validate_header():
#   1. gas_used <= gas_limit
#   2. number >= 1 and number == parent.number + 1
#   3. timestamp > parent.timestamp
#
# Both inputs are 128-byte extended-header structs as produced
# by PR-K39 header_extended_decode.
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

echo "==> emit zisk_validate_header_basic ELF"
lake exe codegen --program zisk_validate_header_basic --halt linux93 \
  -o gen-out/zisk_validate_header_basic

REPO_ROOT="$(pwd)"

# pack_header writes a 128-byte struct:
#   0..32: parent_hash (zeros)
#  32..64: state_root  (zeros)
#  64..72: number      (u64 LE)
#  72..80: timestamp   (u64 LE)
#  80..88: gas_limit   (u64 LE)
#  88..96: gas_used    (u64 LE)
#  96..128: base_fee_per_gas (zeros - not checked here)
pack_header() {
  local number="$1" timestamp="$2" gas_limit="$3" gas_used="$4"
  python3 -c "
import struct, sys
out  = b'\x00' * 32                     # parent_hash
out += b'\x00' * 32                     # state_root
out += struct.pack('<Q', $number)
out += struct.pack('<Q', $timestamp)
out += struct.pack('<Q', $gas_limit)
out += struct.pack('<Q', $gas_used)
out += b'\x00' * 32                     # base_fee_per_gas
sys.stdout.buffer.write(out)
"
}

run_case() {
  local name="$1" expected_status="$2"
  local p_number="$3" p_ts="$4" p_gas_limit="$5" p_gas_used="$6"
  local h_number="$7" h_ts="$8" h_gas_limit="$9" h_gas_used="${10}"

  local in_file="$REPO_ROOT/gen-out/zisk_validate_header_basic_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_validate_header_basic_${name}.output"

  # Input file maps to INPUT_ADDR + 8 onward, so the file starts
  # directly with the this-header bytes (no leading pad).
  : > "$in_file"
  pack_header "$h_number" "$h_ts" "$h_gas_limit" "$h_gas_used" >> "$in_file"
  pack_header "$p_number" "$p_ts" "$p_gas_limit" "$p_gas_used" >> "$in_file"

  "$ZISKEMU" -e gen-out/zisk_validate_header_basic.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_validate_header_basic_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  local exp_le; exp_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"

  if [[ "$actual" == "$exp_le" ]]; then
    printf "  %-30s OK   status=%d\n" "$name" "$expected_status"
    return 0
  else
    printf "  %-30s FAIL  expected status=%d got 0x%s\n" "$name" "$expected_status" "$actual"
    return 1
  fi
}

FAILED=0
# pass cases
run_case "ok_zero_gas"          0  100 1000  30000000 0          101 2000  30000000 0          || FAILED=1
run_case "ok_full_gas"          0  100 1000  30000000 0          101 2000  30000000 30000000   || FAILED=1
run_case "ok_min_timestamp_gap" 0  100 1000  30000000 0          101 1001  30000000 21000      || FAILED=1
run_case "ok_genesis_to_1"      0  0   0     30000000 0          1   1     30000000 21000      || FAILED=1
# fail: gas_used > gas_limit
run_case "fail_gas_overshoot"   1  100 1000  30000000 0          101 2000  30000000 30000001   || FAILED=1
run_case "fail_gas_overshoot2"  1  100 1000  21000    0          101 2000  21000    21001      || FAILED=1
# fail: number mismatch
run_case "fail_number_same"     2  100 1000  30000000 0          100 2000  30000000 100        || FAILED=1
run_case "fail_number_skip"     2  100 1000  30000000 0          102 2000  30000000 100        || FAILED=1
run_case "fail_number_behind"   2  100 1000  30000000 0          99  2000  30000000 100        || FAILED=1
run_case "fail_number_zero_wrap" 2  18446744073709551615 1000 30000000 0 0 2000 30000000 100   || FAILED=1
# fail: timestamp not increasing
run_case "fail_timestamp_same"  3  100 1000  30000000 0          101 1000  30000000 100        || FAILED=1
run_case "fail_timestamp_back"  3  100 1000  30000000 0          101 999   30000000 100        || FAILED=1
# Multi-failure: gas check fires FIRST per asm order.
run_case "first_failure_gas"    1  100 1000  30000000 0          50  500   30000000 30000001   || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: validate_header_basic enforces gas_used/number/timestamp invariants"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
