#!/usr/bin/env bash
# codegen-zisk-block-receipt-records-materialize-check.sh -- block receipt-record materializer probe.
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

echo "==> emit zisk_block_receipt_records_materialize ELF"
lake exe codegen --program zisk_block_receipt_records_materialize --halt linux93 \
  -o gen-out/zisk_block_receipt_records_materialize

REPO_ROOT="$(pwd)"

# run_case <name> <mode>
# mode=empty: no transactions.
# mode=legacy_stop: one legacy tx whose data field is STOP (0x00).
# mode=two_legacy_stop: two legacy STOP txs, testing runtime receipt-gas increments.
run_case() {
  local name="$1" mode="$2"
  local in_file="$REPO_ROOT/gen-out/zisk_block_receipt_records_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_receipt_records_${name}.output"
  local expected_file="$REPO_ROOT/gen-out/zisk_block_receipt_records_${name}.expected.hex"

  python3 - "$in_file" "$expected_file" "$mode" <<'EOF_PY'
import struct
import sys

in_file, expected_file, mode = sys.argv[1:]
TX_OFF = 600
GAS_FEED_OFF = 0x1000
GAS_USED = 21000
payload = bytearray(GAS_FEED_OFF + 64)
payload[420:428] = struct.pack('<Q', GAS_USED)
payload[504:508] = struct.pack('<I', TX_OFF)

# Minimal RLP helpers for a legacy tx with calldata STOP. The materializer only
# needs a legacy transaction envelope (first byte >= 0xc0), but using a real
# 9-field legacy shape keeps the probe aligned with the receipt-record intent.
def rlp_bytes(bs: bytes) -> bytes:
    if len(bs) == 1 and bs[0] < 0x80:
        return bs
    if len(bs) <= 55:
        return bytes([0x80 + len(bs)]) + bs
    l = len(bs).to_bytes((len(bs).bit_length() + 7) // 8, 'big')
    return bytes([0xb7 + len(l)]) + l + bs

def rlp_int(n: int) -> bytes:
    if n == 0:
        return b'\x80'
    bs = n.to_bytes((n.bit_length() + 7) // 8, 'big')
    return rlp_bytes(bs)

def rlp_list(items) -> bytes:
    payload = b''.join(items)
    if len(payload) <= 55:
        return bytes([0xc0 + len(payload)]) + payload
    l = len(payload).to_bytes((len(payload).bit_length() + 7) // 8, 'big')
    return bytes([0xf7 + len(l)]) + l + payload

def legacy_stop_tx(gas_limit: int) -> bytes:
    return rlp_list([
    rlp_int(0),                  # nonce
    rlp_int(1),                  # gas_price
    rlp_int(gas_limit),          # gas_limit
    rlp_bytes(bytes(20)),        # to
    rlp_int(0),                  # value
    rlp_bytes(b'\x00'),          # data: STOP
    rlp_int(27),                 # v
    rlp_int(1),                  # r
    rlp_int(1),                  # s
    ])

if mode == 'empty':
    wd_off = TX_OFF
    expected_count = 0
    expected_first_status = 1
    expected_last_status = 1
    first_record = (0, 0, 0, 0, 0, 0, 0, 0)
    last_record = (0, 0, 0, 0, 0, 0, 0, 0)
elif mode == 'legacy_stop':
    tx = legacy_stop_tx(21000)
    tx_list = struct.pack('<I', 4) + tx
    payload[TX_OFF:TX_OFF + len(tx_list)] = tx_list
    payload[GAS_FEED_OFF:GAS_FEED_OFF + 16] = struct.pack('<QQ', 1, GAS_USED)
    wd_off = TX_OFF + len(tx_list)
    expected_count = 1
    expected_first_status = 0
    expected_last_status = 0
    first_record = (0, 1, GAS_USED, 0, 0, 0, 0, 0)
    last_record = first_record
elif mode == 'two_legacy_stop':
    tx1 = legacy_stop_tx(21000)
    tx2 = legacy_stop_tx(22000)
    tx_list = struct.pack('<II', 8, 8 + len(tx1)) + tx1 + tx2
    payload[TX_OFF:TX_OFF + len(tx_list)] = tx_list
    payload[GAS_FEED_OFF:GAS_FEED_OFF + 24] = struct.pack('<QQQ', 2, 18000, 24000)
    wd_off = TX_OFF + len(tx_list)
    expected_count = 2
    expected_first_status = 0
    expected_last_status = 0
    first_record = (0, 1, 18000, 0, 0, 0, 0, 0)
    last_record = (0, 1, 42000, 0, 0, 0, 0, 0)
else:
    raise ValueError(mode)

payload[508:512] = struct.pack('<I', wd_off)
with open(in_file, 'wb') as f:
    f.write(payload)

out = bytearray(168)
out[0:8] = struct.pack('<Q', 0)                    # brr_status
out[8:16] = struct.pack('<Q', expected_count)       # count
out[16:24] = struct.pack('<Q', 0)                   # append status
out[24:32] = struct.pack('<Q', expected_first_status)
out[32:96] = struct.pack('<QQQQQQQQ', *first_record)
out[96:104] = struct.pack('<Q', expected_last_status)
out[104:168] = struct.pack('<QQQQQQQQ', *last_record)
with open(expected_file, 'w') as f:
    f.write(out.hex())
EOF_PY

  "$ZISKEMU" -e gen-out/zisk_block_receipt_records_materialize.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_block_receipt_records_${name}.emu.log" 2>&1 || true

  local actual expected
  actual="$(dd if="$out_file" bs=1 count=168 2>/dev/null | xxd -p | tr -d '\n')"
  expected="$(cat "$expected_file")"
  if [[ "$actual" == "$expected" ]]; then
    printf "  %-18s OK\n" "$name"
    return 0
  fi
  printf "  %-18s FAIL\n" "$name"
  printf "      actual:   %s\n" "$actual"
  printf "      expected: %s\n" "$expected"
  return 1
}

FAILED=0
run_case "empty" empty || FAILED=1
run_case "legacy_stop" legacy_stop || FAILED=1
run_case "two_legacy_stop" two_legacy_stop || FAILED=1

if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block receipt-record materializer probe"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
