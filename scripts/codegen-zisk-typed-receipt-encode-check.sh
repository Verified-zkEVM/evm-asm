#!/usr/bin/env bash
# codegen-zisk-typed-receipt-encode-check.sh -- EIP-2718 typed receipt envelope.
#
# Encodes type_byte || rlp([status, cumulative_gas, logs_bloom, logs]).
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

echo "==> emit zisk_typed_receipt_encode ELF"
lake exe codegen --program zisk_typed_receipt_encode --halt linux93 \
  -o gen-out/zisk_typed_receipt_encode

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" type_byte="$2" status="$3" gas="$4" bloom="$5" logs="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_typed_receipt_encode_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_typed_receipt_encode_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_typed_receipt_encode_${name}.expected.hex"

  LOGS_JSON="$logs" uv run --directory execution-specs --quiet python3 -c '
import json, os, struct, sys, rlp
receipt_type = int(sys.argv[3], 0)
status = int(sys.argv[4], 0)
gas = int(sys.argv[5], 0)
bloom = bytes.fromhex(sys.argv[6])
assert len(bloom) == 256
raw_logs = json.loads(os.environ["LOGS_JSON"])
logs = []
for addr_hex, topic_hexes, data_hex in raw_logs:
    addr = bytes.fromhex(addr_hex)
    topics = [bytes.fromhex(t) for t in topic_hexes]
    data = bytes.fromhex(data_hex)
    logs.append([addr, topics, data])
logs_rlp = rlp.encode(logs)
typed = bytes([receipt_type & 0xff]) + rlp.encode([status, gas, bloom, logs])
with open(sys.argv[1], "wb") as f:
    f.write(struct.pack("<Q", receipt_type))
    f.write(struct.pack("<Q", status))
    f.write(struct.pack("<Q", gas))
    f.write(bloom)
    f.write(struct.pack("<Q", len(logs_rlp)))
    f.write(logs_rlp)
    pad = (-(288 + len(logs_rlp))) % 8
    if pad:
        f.write(bytes(pad))
with open(sys.argv[2], "w") as f:
    f.write(typed.hex())
' "$in_file" "$exp_hex_file" "$type_byte" "$status" "$gas" "$bloom"

  "$ZISKEMU" -e gen-out/zisk_typed_receipt_encode.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_typed_receipt_encode_${name}.emu.log" 2>&1 || true

  local actual_status actual_len_le actual_len expected_hex expected_len cmp_len actual_hex expected_prefix
  actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  actual_len_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  actual_len="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_len_le'))[0])")"
  expected_hex="$(cat "$exp_hex_file")"
  expected_len=$(( ${#expected_hex} / 2 ))
  cmp_len=$expected_len
  if [[ $cmp_len -gt 240 ]]; then cmp_len=240; fi
  actual_hex="$(dd if="$out_file" bs=1 skip=16 count="$cmp_len" 2>/dev/null | xxd -p | tr -d '\n')"
  expected_prefix="${expected_hex:0:$((2 * cmp_len))}"

  if [[ "$actual_status" == "0000000000000000" \
       && "$actual_len" == "$expected_len" \
       && "$actual_hex" == "$expected_prefix" ]]; then
    printf "  %-30s OK   type=%s len=%d (compared %d B)\n" "$name" "$type_byte" "$expected_len" "$cmp_len"
    return 0
  fi

  printf "  %-30s FAIL status=0x%s actual_len=%d expected_len=%d\n" "$name" "$actual_status" "$actual_len" "$expected_len"
  printf "      actual:   %s...\n" "${actual_hex:0:80}"
  printf "      expected: %s...\n" "${expected_prefix:0:80}"
  return 1
}

ZERO_BLOOM="$(python3 -c "print('00' * 256)")"
PATTERN_BLOOM="$(python3 -c "print(bytes(range(256)).hex())")"
A1="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
T0="1111111111111111111111111111111111111111111111111111111111111111"

FAILED=0
run_case "type1_empty_success" 0x01 1 21000 "$ZERO_BLOOM" "[]" || FAILED=1
run_case "type2_empty_revert"  0x02 0 50000 "$ZERO_BLOOM" "[]" || FAILED=1
run_case "type2_pattern_bloom" 0x02 1 30000000 "$PATTERN_BLOOM" "[]" || FAILED=1
run_case "type3_one_log"       0x03 1 70000 "$ZERO_BLOOM" "[[\"$A1\", [\"$T0\"], \"\"]]" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: typed_receipt_encode matches type_byte || Python receipt RLP"
  exit 0
fi

echo "==> FAIL"
exit 1
