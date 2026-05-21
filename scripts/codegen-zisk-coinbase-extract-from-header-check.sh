#!/usr/bin/env bash
# codegen-zisk-coinbase-extract-from-header-check.sh -- PR-K55.
#
# Extract the 20-byte beneficiary (field 2) of an RLP-encoded
# block header.
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

echo "==> emit zisk_coinbase_extract_from_header ELF"
lake exe codegen --program zisk_coinbase_extract_from_header --halt linux93 \
  -o gen-out/zisk_coinbase_extract_from_header

REPO_ROOT="$(pwd)"

# build_header writes a synthetic 12-field header RLP, with the
# given coinbase. Other fields are stable placeholders.
build_header() {
  local coinbase_hex="$1"
  uv run --directory execution-specs --quiet python3 -c "
import sys
import rlp
coinbase = bytes.fromhex('$coinbase_hex')
fields = [
    b'\x11' * 32,       # 0: parent_hash
    b'\x22' * 32,       # 1: ommers_hash
    coinbase,           # 2: coinbase (variable)
    b'\x44' * 32,       # 3: state_root
    b'\x55' * 32,       # 4: transactions_root
    b'\x66' * 32,       # 5: receipts_root
    b'\x00' * 256,      # 6: bloom
    0,                  # 7: difficulty
    100,                # 8: number
    0x1c9c380,          # 9: gas_limit
    0x100,              # 10: gas_used
    1700000000,         # 11: timestamp
]
sys.stdout.buffer.write(rlp.encode(fields))
"
}

# run_case <name> <expected_status> <coinbase_hex>
run_case() {
  local name="$1" expected_status="$2" coinbase_hex="$3"

  local header_file="$REPO_ROOT/gen-out/zisk_coinbase_extract_from_header_${name}.header"
  local in_file="$REPO_ROOT/gen-out/zisk_coinbase_extract_from_header_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_coinbase_extract_from_header_${name}.output"

  build_header "$coinbase_hex" > "$header_file"
  python3 -c "
import struct, sys
with open(sys.argv[1], 'rb') as f:
    body = f.read()
out  = struct.pack('<Q', len(body))
out += body
pad = (-(8 + len(body))) % 8
if pad:
    out += b'\x00' * pad
sys.stdout.buffer.write(out)
" "$header_file" > "$in_file"

  "$ZISKEMU" -e gen-out/zisk_coinbase_extract_from_header.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_coinbase_extract_from_header_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_addr;   actual_addr="$(dd if="$out_file" bs=1 skip=8 count=20 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"

  if [[ "$expected_status" == "0" ]]; then
    if [[ "$actual_status" == "$exp_status_le" && "$actual_addr" == "$coinbase_hex" ]]; then
      printf "  %-30s OK   status=0 coinbase=%s\n" "$name" "${coinbase_hex:0:10}..."
      return 0
    else
      printf "  %-30s FAIL  status=0x%s coinbase=0x%s (expected %s)\n" "$name" "$actual_status" "$actual_addr" "$coinbase_hex"
      return 1
    fi
  else
    if [[ "$actual_status" == "$exp_status_le" ]]; then
      printf "  %-30s OK   status=%d\n" "$name" "$expected_status"
      return 0
    else
      printf "  %-30s FAIL  expected status=%d got 0x%s\n" "$name" "$expected_status" "$actual_status"
      return 1
    fi
  fi
}

FAILED=0
# Standard valid coinbase shapes
run_case "alice_aa20"     0 "$(printf 'aa%.0s' $(seq 1 20))"   || FAILED=1
run_case "bob_bb20"       0 "$(printf 'bb%.0s' $(seq 1 20))"   || FAILED=1
run_case "zero_addr"      0 "$(printf '00%.0s' $(seq 1 20))"   || FAILED=1
run_case "ff_addr"        0 "$(printf 'ff%.0s' $(seq 1 20))"   || FAILED=1
# Mixed-byte coinbase
run_case "mixed_bytes"    0 "deadbeefcafebabe0011223344556677889900ff"  || FAILED=1
# Real Ethereum coinbase (Vitalik's known dev address, valid 20B)
run_case "real_address"   0 "ab5801a7d398351b8be11c439e05c5b3259aec9b"  || FAILED=1

# Failure: wrong-length coinbase (10 bytes instead of 20)
# Build manually since build_header always uses 20 bytes
SHORT_HEADER_FILE="$REPO_ROOT/gen-out/zisk_coinbase_extract_from_header_short_coinbase.header"
uv run --directory execution-specs --quiet python3 -c "
import sys
import rlp
short_coinbase = b'\x33' * 10  # 10 bytes, not 20
fields = [
    b'\x11' * 32, b'\x22' * 32, short_coinbase, b'\x44' * 32,
    b'\x55' * 32, b'\x66' * 32, b'\x00' * 256, 0,
    100, 0x1c9c380, 0x100, 1700000000,
]
sys.stdout.buffer.write(rlp.encode(fields))
" > "$SHORT_HEADER_FILE"

SHORT_IN_FILE="$REPO_ROOT/gen-out/zisk_coinbase_extract_from_header_short_coinbase.input"
python3 -c "
import struct, sys
with open(sys.argv[1], 'rb') as f:
    body = f.read()
out  = struct.pack('<Q', len(body))
out += body
pad = (-(8 + len(body))) % 8
if pad:
    out += b'\x00' * pad
sys.stdout.buffer.write(out)
" "$SHORT_HEADER_FILE" > "$SHORT_IN_FILE"

"$ZISKEMU" -e gen-out/zisk_coinbase_extract_from_header.elf \
  -i "$SHORT_IN_FILE" -o "$REPO_ROOT/gen-out/zisk_coinbase_extract_from_header_short_coinbase.output" \
  -n 500000 >"$REPO_ROOT/gen-out/zisk_coinbase_extract_from_header_short_coinbase.emu.log" 2>&1 || true

SHORT_STATUS="$(xxd -p -l 8 "$REPO_ROOT/gen-out/zisk_coinbase_extract_from_header_short_coinbase.output" | tr -d '\n')"
if [[ "$SHORT_STATUS" == "0100000000000000" ]]; then
  printf "  %-30s OK   status=1 (10B coinbase rejected)\n" "short_coinbase_rejected"
else
  printf "  %-30s FAIL  status=0x%s\n" "short_coinbase_rejected" "$SHORT_STATUS"
  FAILED=1
fi

# Failure: non-list input
NON_LIST_FILE="$REPO_ROOT/gen-out/zisk_coinbase_extract_from_header_non_list.input"
python3 -c "
import struct, sys
b = bytes([0x80])  # RLP empty string, not a list
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(b)))
    f.write(b)
    f.write(b'\x00' * 7)
" "$NON_LIST_FILE"
"$ZISKEMU" -e gen-out/zisk_coinbase_extract_from_header.elf \
  -i "$NON_LIST_FILE" -o "$REPO_ROOT/gen-out/zisk_coinbase_extract_from_header_non_list.output" \
  -n 500000 >"$REPO_ROOT/gen-out/zisk_coinbase_extract_from_header_non_list.emu.log" 2>&1 || true
NL_STATUS="$(xxd -p -l 8 "$REPO_ROOT/gen-out/zisk_coinbase_extract_from_header_non_list.output" | tr -d '\n')"
if [[ "$NL_STATUS" == "0100000000000000" ]]; then
  printf "  %-30s OK   status=1 (non-list rejected)\n" "non_list_rejected"
else
  printf "  %-30s FAIL  status=0x%s\n" "non_list_rejected" "$NL_STATUS"
  FAILED=1
fi

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: coinbase_extract_from_header returns the beneficiary"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
