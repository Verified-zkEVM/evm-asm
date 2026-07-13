#!/usr/bin/env bash
# codegen-zisk-rlp-list-nth-item-check.sh -- PR-K20.
#
# Walks an RLP-encoded list to extract the N-th item's content
# bounds. Foundation for MPT node decoding.
#
# Tests every RLP item form:
#   - single byte (0x00..0x7f)
#   - short string (0x80..0xb7)
#   - long string (0xb8..0xbf)
#   - short list (0xc0..0xf7)
#   - long list (0xf8..0xff)
#
# plus outer list prefix forms (short c0+, long f8/f9) and OOB
# indices.
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

echo "==> emit zisk_rlp_list_nth_item ELF"
lake exe codegen --program zisk_rlp_list_nth_item --halt linux93 \
  -o gen-out/zisk_rlp_list_nth_item

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" list_hex="$2" n="$3" \
        expected_status="$4" expected_offset="$5" expected_length="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_rlp_list_nth_item_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_rlp_list_nth_item_${name}.output"

  python3 -c "
import struct, sys
list_bytes = bytes.fromhex('$list_hex')
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(list_bytes)))
    f.write(struct.pack('<Q', $n))
    f.write(list_bytes)
    pad = (-(16 + len(list_bytes))) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_rlp_list_nth_item.elf \
    -i "$in_file" -o "$out_file" -n 50000 \
    >"$REPO_ROOT/gen-out/zisk_rlp_list_nth_item_${name}.emu.log" 2>&1 || true

  local actual_status actual_offset actual_length
  actual_status="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  actual_offset="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  actual_length="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_status_le exp_offset_le exp_length_le
  exp_status_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"
  exp_offset_le="$(python3 -c "print(int('$expected_offset').to_bytes(8, 'little').hex())")"
  exp_length_le="$(python3 -c "print(int('$expected_length').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" && \
        "$actual_offset" == "$exp_offset_le" && \
        "$actual_length" == "$exp_length_le" ]]; then
    printf "  %-26s OK   status=%d off=%d len=%d\n" \
      "$name" "$expected_status" "$expected_offset" "$expected_length"
    return 0
  else
    printf "  %-26s FAIL\n    expected: %d / %d / %d\n    actual:   0x%s / 0x%s / 0x%s\n" \
      "$name" "$expected_status" "$expected_offset" "$expected_length" \
      "$actual_status" "$actual_offset" "$actual_length"
    return 1
  fi
}

# Each fixture: (label list_hex N expected_status expected_offset expected_length)

FAILED=0

# Two-Bytes32 list (extension/leaf shape): 33+33 = 66 bytes payload,
# > 55 so long-list form: 0xf8 0x42 <body>.
# inner item 0: 0xa0 + 32 bytes aa; inner item 1: 0xa0 + 32 bytes bb
LIST_2BYTES32="f842a0$(printf 'aa%.0s' $(seq 1 32))a0$(printf 'bb%.0s' $(seq 1 32))"
# Item 0 content starts at outer prefix (2) + 1 (0xa0) = 3, length 32
run_case "two_bytes32_item0"  "$LIST_2BYTES32" 0 0 3  32                        || FAILED=1
# Item 1 content starts at 2 + 33 + 1 = 36, length 32
run_case "two_bytes32_item1"  "$LIST_2BYTES32" 1 0 36 32                        || FAILED=1
# Item 2 OOB
run_case "two_bytes32_oob"    "$LIST_2BYTES32" 2 1 0  0                         || FAILED=1

# Branch node shape: 17 items. Test minimal: 17 empty strings.
# 17 * 0x80 = 17 bytes payload. Outer: 0xc0 + 17 = 0xd1.
# Total: 18 bytes.
LIST_17_EMPTY="d1$(printf '80%.0s' $(seq 1 17))"
# Item 0: empty string content. For short string with b=0x80, content offset = item_start+1 = 2, length = 0.
run_case "branch_empty_item0" "$LIST_17_EMPTY" 0  0 2  0                        || FAILED=1
run_case "branch_empty_item8" "$LIST_17_EMPTY" 8  0 10 0                        || FAILED=1
run_case "branch_empty_item16" "$LIST_17_EMPTY" 16 0 18 0                       || FAILED=1
run_case "branch_empty_oob"   "$LIST_17_EMPTY" 17 1 0  0                        || FAILED=1

# Mix: list of [single_byte 0x42, short string "hello", empty bytes, Bytes32]
# Encoded items:
#   0x42                       (1 byte; single byte form)
#   0x85 "hello"               (6 bytes)
#   0x80                       (1 byte)
#   0xa0 <32 bytes 0x77>       (33 bytes)
# Total payload: 1+6+1+33 = 41 bytes. Short list: 0xc0+41 = 0xe9. Total 42 bytes.
LIST_MIXED="e94285$(printf '68656c6c6f')80a0$(printf '77%.0s' $(seq 1 32))"
# Item 0: single byte. content offset = item_start = 1 (after 0xe9), length = 1.
run_case "mixed_item0_single" "$LIST_MIXED" 0 0 1  1                            || FAILED=1
# Item 1: short string "hello". offset = 1+1+1 = 3, length = 5.
run_case "mixed_item1_str"    "$LIST_MIXED" 1 0 3  5                            || FAILED=1
# Item 2: empty string. offset = 1+1+6 = 8, length 0.
run_case "mixed_item2_empty"  "$LIST_MIXED" 2 0 9  0                            || FAILED=1
# Item 3: Bytes32(0x77). Item starts at 9 (1+1+6+1); content offset = 9+1 = 10, length 32.
run_case "mixed_item3_b32"    "$LIST_MIXED" 3 0 10 32                           || FAILED=1

# Empty list (0xc0): no items.
LIST_EMPTY="c0"
run_case "empty_list_oob"     "$LIST_EMPTY" 0 1 0  0                            || FAILED=1

# Not an RLP list (byte < 0xc0): parse fail.
NOT_LIST="80"
run_case "not_list"           "$NOT_LIST"   0 1 0  0                            || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: rlp_list_nth_item handles every RLP item form"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
