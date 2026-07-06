#!/usr/bin/env bash
# codegen-zisk-captured-logs-bloom-add-check.sh -- M26 captured LOG descriptors.
#
# Converts dispatcher-captured LOG descriptors to a 256-byte Ethereum receipt
# logs_bloom. Descriptor words use EVM stack byte order (4 LE u64 limbs, low
# limb first); the helper canonicalizes address/topic bytes before hashing.
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

echo "==> emit zisk_captured_logs_bloom_add ELF"
lake exe codegen --program zisk_captured_logs_bloom_add --halt linux93 \
  -o gen-out/zisk_captured_logs_bloom_add
echo "==> emit zisk_logs_list_bloom_add ELF"
lake exe codegen --program zisk_logs_list_bloom_add --halt linux93 \
  -o gen-out/zisk_logs_list_bloom_add

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" spec="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_captured_logs_bloom_add_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_captured_logs_bloom_add_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_captured_logs_bloom_add_${name}.expected"
  local rlp_in_file="$REPO_ROOT/gen-out/zisk_logs_list_bloom_add_${name}.input"
  local rlp_out_file="$REPO_ROOT/gen-out/zisk_logs_list_bloom_add_${name}.output"

  SPEC_JSON="$spec" uv run --directory execution-specs --quiet python3 -c '
import json, os, struct, sys
from Crypto.Hash import keccak

def keccak256(b):
    h = keccak.new(digest_bits=256)
    h.update(b)
    return h.digest()

def add(bloom, value):
    h = keccak256(value)
    for idx in (0, 2, 4):
        raw = int.from_bytes(h[idx:idx+2], "big") & 0x07ff
        bit = 0x07ff - raw
        bloom[bit // 8] |= 1 << (7 - (bit % 8))

def stack_word_from_be32(value):
    return bytes.fromhex(value)[::-1]

def stack_word_from_address(address):
    return bytes.fromhex(address)[::-1] + bytes(12)

def descriptor(address, topics, data=b""):
    d = bytearray(256)
    struct.pack_into("<Q", d, 0, len(topics))
    copied = min(len(data), 32)
    struct.pack_into("<Q", d, 24, copied)
    for i, topic in enumerate(topics):
        d[32 + 32*i:64 + 32*i] = stack_word_from_be32(topic)
    d[160:160+copied] = data[:copied]
    d[192:224] = stack_word_from_address(address)
    return bytes(d)

def rlp_bytes(value):
    if len(value) == 1 and value[0] < 0x80:
        return value
    if len(value) < 56:
        return bytes([0x80 + len(value)]) + value
    length = len(value).to_bytes((len(value).bit_length() + 7) // 8, "big")
    return bytes([0xb7 + len(length)]) + length + value

def rlp_list(items):
    payload = b"".join(items)
    if len(payload) < 56:
        return bytes([0xc0 + len(payload)]) + payload
    length = len(payload).to_bytes((len(payload).bit_length() + 7) // 8, "big")
    return bytes([0xf7 + len(length)]) + length + payload

raw = json.loads(os.environ["SPEC_JSON"])
mode = raw.get("mode", "logs")
logs_rlp = None
if mode == "count_over_cap":
    # 6c7v9: the descriptor cap was raised 16 -> 1024; 1025 still exceeds it. The
    # count gate rejects before any descriptor is read, so the body is a placeholder.
    count = 1025
    descs = bytes(256)
    expected_status = 1
    bloom = bytes(256)
elif mode == "topic_over_cap":
    d = bytearray(256)
    struct.pack_into("<Q", d, 0, 5)
    descs = bytes(d)
    count = 1
    expected_status = 2
    bloom = bytes(256)
else:
    logs = raw["logs"]
    parts = []
    rlp_items = []
    bloom = bytearray(256)
    for log in logs:
        address = log["address"]
        topics = log.get("topics", [])
        data = bytes.fromhex(log.get("data", ""))
        parts.append(descriptor(address, topics, data))
        rlp_items.append(rlp_list([
            rlp_bytes(bytes.fromhex(address)),
            rlp_list([rlp_bytes(bytes.fromhex(topic)) for topic in topics]),
            rlp_bytes(data),
        ]))
        add(bloom, bytes.fromhex(address))
        for topic in topics:
            add(bloom, bytes.fromhex(topic))
    descs = b"".join(parts)
    count = len(parts)
    expected_status = 0
    bloom = bytes(bloom)
    logs_rlp = rlp_list(rlp_items)

with open(sys.argv[1], "wb") as f:
    f.write(struct.pack("<Q", count))
    f.write(descs)
    pad = (-(8 + len(descs))) % 8
    if pad:
        f.write(bytes(pad))
with open(sys.argv[2], "wb") as f:
    if expected_status == 0:
        f.write(bloom)
    else:
        f.write(struct.pack("<Q", expected_status))
        f.write(bytes(248))
if logs_rlp is not None:
    with open(sys.argv[3], "wb") as f:
        f.write(struct.pack("<Q", len(logs_rlp)))
        f.write(logs_rlp)
        pad = (-(8 + len(logs_rlp))) % 8
        if pad:
            f.write(bytes(pad))
' "$in_file" "$exp_file" "$rlp_in_file"

  "$ZISKEMU" -e gen-out/zisk_captured_logs_bloom_add.elf \
    -i "$in_file" -o "$out_file" -n 10000000 \
    >"$REPO_ROOT/gen-out/zisk_captured_logs_bloom_add_${name}.emu.log" 2>&1 || true

  local actual expected actual_status expected_status
  actual="$(xxd -p -l 256 "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l 256 "$exp_file" | tr -d '\n')"
  actual_status="${actual:0:16}"
  expected_status="${expected:0:16}"

  local rlp_actual=""
  if [[ -s "$rlp_in_file" ]]; then
    "$ZISKEMU" -e gen-out/zisk_logs_list_bloom_add.elf \
      -i "$rlp_in_file" -o "$rlp_out_file" -n 10000000 \
      >"$REPO_ROOT/gen-out/zisk_logs_list_bloom_add_${name}.emu.log" 2>&1 || true
    rlp_actual="$(xxd -p -l 256 "$rlp_out_file" 2>/dev/null | tr -d '\n')"
  fi

  if [[ "$actual" == "$expected" && ( -z "$rlp_actual" || "$rlp_actual" == "$expected" ) ]]; then
    local bits
    bits="$(python3 -c "print(bin(int('$actual', 16)).count('1'))")"
    if [[ -n "$rlp_actual" ]]; then
      printf "  %-24s OK   status=%s bits_set=%d rlp_oracle=match\n" "$name" "$expected_status" "$bits"
    else
      printf "  %-24s OK   status=%s bits_set=%d\n" "$name" "$expected_status" "$bits"
    fi
    return 0
  fi

  printf "  %-24s FAIL\n" "$name"
  printf "      status actual/expected: %s / %s\n" "$actual_status" "$expected_status"
  printf "      bloom actual:   %s...\n" "${actual:0:80}"
  printf "      bloom expected: %s...\n" "${expected:0:80}"
  if [[ -n "$rlp_actual" ]]; then
    printf "      rlp oracle:     %s...\n" "${rlp_actual:0:80}"
  fi
  return 1
}

A1="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
A2="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
T0="1111111111111111111111111111111111111111111111111111111111111111"
T1="2222222222222222222222222222222222222222222222222222222222222222"
T2="3333333333333333333333333333333333333333333333333333333333333333"
T3="4444444444444444444444444444444444444444444444444444444444444444"

FAILED=0
run_case "zero_logs" '{"logs":[]}' || FAILED=1
run_case "one_log0" "{\"logs\":[{\"address\":\"$A1\",\"topics\":[],\"data\":\"deadbeef\"}]}" || FAILED=1
run_case "one_log1" "{\"logs\":[{\"address\":\"$A1\",\"topics\":[\"$T0\"],\"data\":\"\"}]}" || FAILED=1
run_case "one_log2" "{\"logs\":[{\"address\":\"$A1\",\"topics\":[\"$T0\",\"$T1\"],\"data\":\"ab\"}]}" || FAILED=1
run_case "one_log3" "{\"logs\":[{\"address\":\"$A1\",\"topics\":[\"$T0\",\"$T1\",\"$T2\"],\"data\":\"abcdef\"}]}" || FAILED=1
run_case "one_log4" "{\"logs\":[{\"address\":\"$A1\",\"topics\":[\"$T0\",\"$T1\",\"$T2\",\"$T3\"],\"data\":\"ab\"}]}" || FAILED=1
run_case "two_logs_mixed" "{\"logs\":[{\"address\":\"$A1\",\"topics\":[\"$T0\"],\"data\":\"\"},{\"address\":\"$A2\",\"topics\":[\"$T1\",\"$T2\"],\"data\":\"cafebabe\"}]}" || FAILED=1
run_case "count_over_cap" '{"mode":"count_over_cap"}' || FAILED=1
run_case "topic_over_cap" '{"mode":"topic_over_cap"}' || FAILED=1
# 6c7v9: 20 LOG events (> the former 16-descriptor cap) must now be captured and bloomed.
many_logs=""; for _i in $(seq 1 20); do many_logs+="{\"address\":\"$A1\",\"topics\":[\"$T0\"],\"data\":\"\"},"; done
run_case "many_logs_over_old_cap" "{\"logs\":[${many_logs%,}]}" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: captured LOG descriptors produce expected receipt bloom"
  exit 0
fi

echo "==> FAIL"
exit 1
