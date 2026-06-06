#!/usr/bin/env bash
# codegen-zisk-receipt-records-encode-no-logs-check.sh -- receipt-record list encoder probe.
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

echo "==> emit zisk_receipt_records_encode_no_logs ELF"
lake exe codegen --program zisk_receipt_records_encode_no_logs --halt linux93 \
  -o gen-out/zisk_receipt_records_encode_no_logs

REPO_ROOT="$(pwd)"

# run_case <name> <cap> <records> <exp_status>
# records grammar: tx_type:status:cumulative_gas:log_count[, ...]
run_case() {
  local name="$1" cap="$2" records="$3" exp_status="$4"
  local in_file="$REPO_ROOT/gen-out/zisk_receipt_records_encode_no_logs_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_receipt_records_encode_no_logs_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_receipt_records_encode_no_logs_${name}.expected"

  python3 - "$in_file" "$exp_file" "$cap" "$records" "$exp_status" <<'PY'
import struct
import sys

in_file, exp_file, cap_s, records_s, exp_status_s = sys.argv[1:]
cap = int(cap_s)
exp_status = int(exp_status_s)

def parse_records(text):
    if text == "-":
        return []
    rows = []
    for item in text.split(","):
        tx_type, status, gas, log_count = item.split(":")
        rows.append((int(tx_type), int(status), int(gas), int(log_count)))
    return rows

def rlp_bytes(bs: bytes) -> bytes:
    if len(bs) == 1 and bs[0] < 0x80:
        return bs
    if len(bs) <= 55:
        return bytes([0x80 + len(bs)]) + bs
    l = len(bs).to_bytes((len(bs).bit_length() + 7) // 8, "big")
    return bytes([0xb7 + len(l)]) + l + bs

def rlp_int(n: int) -> bytes:
    if n == 0:
        return b"\x80"
    return rlp_bytes(n.to_bytes((n.bit_length() + 7) // 8, "big"))

def rlp_list(items) -> bytes:
    payload = b"".join(items)
    if len(payload) <= 55:
        return bytes([0xc0 + len(payload)]) + payload
    l = len(payload).to_bytes((len(payload).bit_length() + 7) // 8, "big")
    return bytes([0xf7 + len(l)]) + l + payload

def receipt(status: int, gas: int) -> bytes:
    return rlp_list([
        rlp_int(status),
        rlp_int(gas),
        rlp_bytes(b"\x00" * 256),
        rlp_list([]),
    ])

records = parse_records(records_s)
payload = bytearray(16 + 32 * len(records))
payload[0:8] = struct.pack("<Q", len(records))
payload[8:16] = struct.pack("<Q", cap)
cursor = 16
for row in records:
    payload[cursor:cursor + 32] = struct.pack("<QQQQ", *row)
    cursor += 32
with open(in_file, "wb") as f:
    f.write(payload)

expected = bytearray(16)
expected[0:8] = struct.pack("<Q", exp_status)
if exp_status == 0:
    encoded = rlp_list([receipt(status, gas) for tx_type, status, gas, log_count in records])
    expected[8:16] = struct.pack("<Q", len(encoded))
    expected.extend(encoded)
else:
    expected[8:16] = struct.pack("<Q", 0)
with open(exp_file, "wb") as f:
    f.write(expected)
PY

  "$ZISKEMU" -e gen-out/zisk_receipt_records_encode_no_logs.elf \
    -i "$in_file" -o "$out_file" -n 10000000 \
    >"$REPO_ROOT/gen-out/zisk_receipt_records_encode_no_logs_${name}.emu.log" 2>&1 || true

  local expected_len output_len compare_len actual expected
  expected_len="$(wc -c <"$exp_file")"
  output_len="$(wc -c <"$out_file")"
  compare_len="$expected_len"
  if (( compare_len > output_len )); then
    compare_len="$output_len"
  fi
  actual="$(dd if="$out_file" bs=1 count="$compare_len" 2>/dev/null | xxd -p | tr -d '\n')"
  expected="$(dd if="$exp_file" bs=1 count="$compare_len" 2>/dev/null | xxd -p | tr -d '\n')"
  if [[ "$actual" == "$expected" ]]; then
    printf "  %-22s OK\n" "$name"
    return 0
  fi
  printf "  %-22s FAIL\n" "$name"
  printf "    expected: %s\n    actual:   %s\n" "$expected" "$actual"
  printf "    emulator log: %s\n" "$REPO_ROOT/gen-out/zisk_receipt_records_encode_no_logs_${name}.emu.log"
  return 1
}

FAILED=0
run_case "empty"          256 "-"                              0 || FAILED=1
run_case "one_success"    512 "0:1:21000:0"                    0 || FAILED=1
run_case "two_statuses"   768 "0:1:21000:0,0:0:42000:0"        0 || FAILED=1
run_case "four_receipts"  2048 "0:1:1:0,0:1:127:0,0:1:128:0,0:1:1000000:0" 0 || FAILED=1
run_case "log_unsupported" 512 "0:1:21000:1"                   2 || FAILED=1
run_case "typed_unsupported" 512 "1:1:21000:0"                 4 || FAILED=1
run_case "small_cap"      1 "-"                                3 || FAILED=1

if [[ "$FAILED" -eq 0 ]]; then
  echo "==> PASS: no-log receipt-record list encoder"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
