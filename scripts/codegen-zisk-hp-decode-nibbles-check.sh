#!/usr/bin/env bash
# codegen-zisk-hp-decode-nibbles-check.sh -- PR-K23.
#
# HP-decode an MPT leaf/extension path into a nibble array.
# Output: (status, count, is_leaf, nibbles...).
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

echo "==> emit zisk_hp_decode_nibbles ELF"
lake exe codegen --program zisk_hp_decode_nibbles --halt linux93 \
  -o gen-out/zisk_hp_decode_nibbles

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" path_hex="$2" \
        expected_status="$3" expected_count="$4" expected_is_leaf="$5" \
        expected_nibbles_hex="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_hp_decode_nibbles_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_hp_decode_nibbles_${name}.output"

  python3 -c "
import struct, sys
path = bytes.fromhex('$path_hex')
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(path)))
    f.write(path)
    pad = (-(8 + len(path))) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_hp_decode_nibbles.elf \
    -i "$in_file" -o "$out_file" -n 50000 \
    >"$REPO_ROOT/gen-out/zisk_hp_decode_nibbles_${name}.emu.log" 2>&1 || true

  local actual_status actual_count actual_is_leaf actual_nibbles
  actual_status="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  actual_count="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  actual_is_leaf="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local nibble_byte_count
  nibble_byte_count="$expected_count"
  if (( nibble_byte_count > 0 )); then
    actual_nibbles="$(dd if="$out_file" bs=1 skip=24 count="$nibble_byte_count" 2>/dev/null | xxd -p | tr -d '\n')"
  else
    actual_nibbles=""
  fi

  local exp_status_le exp_count_le exp_is_leaf_le
  exp_status_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"
  exp_count_le="$(python3 -c "print(int('$expected_count').to_bytes(8, 'little').hex())")"
  exp_is_leaf_le="$(python3 -c "print(int('$expected_is_leaf').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" && \
        "$actual_count"  == "$exp_count_le" && \
        "$actual_is_leaf" == "$exp_is_leaf_le" && \
        "$actual_nibbles" == "$expected_nibbles_hex" ]]; then
    printf "  %-26s OK   status=%d count=%d leaf=%d nibbles=%s\n" \
      "$name" "$expected_status" "$expected_count" "$expected_is_leaf" "$expected_nibbles_hex"
    return 0
  else
    printf "  %-26s FAIL\n    expected: status=%d count=%d leaf=%d nibbles=%s\n    actual:   status=0x%s count=0x%s leaf=0x%s nibbles=%s\n" \
      "$name" "$expected_status" "$expected_count" "$expected_is_leaf" "$expected_nibbles_hex" \
      "$actual_status" "$actual_count" "$actual_is_leaf" "$actual_nibbles"
    return 1
  fi
}

FAILED=0

# Even-extension: HP byte 0x00, bytes 0x12 0x34. Expected nibbles 1,2,3,4. count=4. leaf=0.
run_case "ext_even"     "001234"  0 4 0 "01020304"             || FAILED=1
# Odd-extension: HP byte 0x1A, then 0xBC. Expected A,B,C. count=3. leaf=0.
run_case "ext_odd"      "1abc"    0 3 0 "0a0b0c"               || FAILED=1
# Even-leaf: HP byte 0x20, then 0x56. Expected 5,6. count=2. leaf=1.
run_case "leaf_even"    "2056"    0 2 1 "0506"                 || FAILED=1
# Odd-leaf: HP byte 0x3F, then 0xEE. Expected F,E,E. count=3. leaf=1.
run_case "leaf_odd"     "3fee"    0 3 1 "0f0e0e"               || FAILED=1
# HP byte alone, even, count=0.
run_case "ext_empty"    "00"      0 0 0 ""                     || FAILED=1
# HP byte alone, odd, count=1, low nibble = 5.
run_case "ext_one_nib"  "15"      0 1 0 "05"                   || FAILED=1
# HP byte alone, odd leaf, low nibble = A.
run_case "leaf_one_nib" "3a"      0 1 1 "0a"                   || FAILED=1

# Invalid: empty input.
run_case "empty"        ""        1 0 0 ""                     || FAILED=1
# Invalid: high nibble 4.
run_case "bad_high"     "42aa"    1 0 0 ""                     || FAILED=1
# Even with non-zero padding nibble: LENIENT (execution-specs
# compact_to_nibbles ignores it; bead evm-asm-3umhl) — decodes bytes 1..
run_case "even_pad_lenient" "0742aa"  0 4 0 "04020a0a"         || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: hp_decode_nibbles handles every HP form + failure case"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
