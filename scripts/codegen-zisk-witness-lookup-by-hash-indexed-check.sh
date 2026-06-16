#!/usr/bin/env bash
# codegen-zisk-witness-lookup-by-hash-indexed-check.sh -- sorted NodeDb index path.
#
# Builds the witness.state full-hash index, then resolves an SSZ-list element by
# keccak256(element).  The probe returns:
#   OUTPUT+0  : lookup status (0 hit, 1 miss)
#   OUTPUT+8  : matched element offset within the section
#   OUTPUT+16 : matched element length
#   OUTPUT+24 : index-build status (0 built, 1 malformed/cap exceeded)
#   OUTPUT+32 : decoded SSZ element count seen by the builder
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

echo "==> emit zisk_witness_lookup_by_hash_indexed ELF"
lake exe codegen --program zisk_witness_lookup_by_hash_indexed --halt linux93 \
  -o gen-out/zisk_witness_lookup_by_hash_indexed

REPO_ROOT="$(pwd)"
MPT_WITNESS_INDEX_CAPACITY=131072
MPT_WITNESS_INDEX_OLD_CAPACITY=8192

run_case() {
  local name="$1" mode="$2"
  local in_file="$REPO_ROOT/gen-out/zisk_witness_lookup_by_hash_indexed_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_witness_lookup_by_hash_indexed_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
from Crypto.Hash import keccak

def k(b):
    h = keccak.new(digest_bits=256)
    h.update(b)
    return h.digest()

mode = '$mode'
parts = mode.split()
which = parts[0]
expected_build = 0

if which == 'hit':
    elem_idx = int(parts[1])
    elements = [bytes.fromhex(a) for a in parts[2:]]
    target = k(elements[elem_idx])
    expected_status = 0
    inner_off = 4 * len(elements) + sum(len(e) for e in elements[:elem_idx])
    expected_offset = inner_off
    expected_length = len(elements[elem_idx])
elif which == 'miss':
    elements = [bytes.fromhex(a) for a in parts[1:]]
    target = bytes.fromhex('deadbeef' * 8)
    expected_status = 1
    expected_offset = 0
    expected_length = 0
elif which == 'empty':
    elements = []
    target = bytes.fromhex('deadbeef' * 8)
    expected_status = 1
    expected_offset = 0
    expected_length = 0
elif which == 'large':
    count = int(parts[1])
    elem_idx = int(parts[2])
    elements = [i.to_bytes(8, 'little') + bytes([i % 251]) for i in range(count)]
    target = k(elements[elem_idx])
    expected_status = 0
    inner_off = 4 * len(elements) + sum(len(e) for e in elements[:elem_idx])
    expected_offset = inner_off
    expected_length = len(elements[elem_idx])
elif which == 'count_boundary':
    count = int(parts[1])
    capacity = int(parts[2])
    section = struct.pack('<I', 4 * count) + (b'\x00' * (4 * (count - 1)))
    target = bytes.fromhex('deadbeef' * 8)
    expected_build = 1
    expected_status = 0
    expected_offset = 0
    expected_length = 0
else:
    raise SystemExit(f'unknown mode: {mode}')

expected_count = len(elements) if which in ('hit', 'miss', 'large', 'empty') else count

if which != 'count_boundary':
    section = b''
    if elements:
        offset = 4 * len(elements)
        for e in elements:
            section += struct.pack('<I', offset)
            offset += len(e)
        section += b''.join(elements)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(section)))
    f.write(target)
    f.write(section)
    pad = (-(8 + 32 + len(section))) % 8
    if pad:
        f.write(b'\x00' * pad)

with open(sys.argv[1] + '.expected.txt', 'w') as f:
    f.write(f'{expected_status} {expected_offset} {expected_length} {expected_build} {expected_count}')
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_witness_lookup_by_hash_indexed.elf \
    -i "$in_file" -o "$out_file" -n 10000000 \
    >"$REPO_ROOT/gen-out/zisk_witness_lookup_by_hash_indexed_${name}.emu.log" 2>&1 || true

  if [[ ! -f "$in_file.expected.txt" ]]; then
    printf "  %-24s FAIL (Python helper failed to write expected)\n" "$name"
    return 1
  fi

  local expected_status expected_offset expected_length expected_build expected_count
  read -r expected_status expected_offset expected_length expected_build expected_count <"$in_file.expected.txt"

  local actual_status actual_offset actual_length actual_build actual_count
  actual_status="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  actual_offset="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  actual_length="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  actual_build="$(dd if="$out_file" bs=1 skip=24 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  actual_count="$(dd if="$out_file" bs=1 skip=32 count=8 2>/dev/null | xxd -p | tr -d '\n')"

  local exp_status_le exp_offset_le exp_length_le exp_build_le exp_count_le
  exp_status_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"
  exp_offset_le="$(python3 -c "print(int('$expected_offset').to_bytes(8, 'little').hex())")"
  exp_length_le="$(python3 -c "print(int('$expected_length').to_bytes(8, 'little').hex())")"
  exp_build_le="$(python3 -c "print(int('$expected_build').to_bytes(8, 'little').hex())")"
  exp_count_le="$(python3 -c "print(int('$expected_count').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" && \
        "$actual_offset" == "$exp_offset_le" && \
        "$actual_length" == "$exp_length_le" && \
        "$actual_build" == "$exp_build_le" && \
        "$actual_count" == "$exp_count_le" ]]; then
    printf "  %-24s OK   build=%d status=%d count=%d off=%d len=%d\n" \
      "$name" "$expected_build" "$expected_status" "$expected_count" "$expected_offset" "$expected_length"
    return 0
  fi

  printf "  %-24s FAIL\n    expected: build=%d status=%d count=%d off=%d len=%d\n    actual:   build=0x%s status=0x%s count=0x%s off=0x%s len=0x%s\n" \
    "$name" "$expected_build" "$expected_status" "$expected_count" "$expected_offset" "$expected_length" \
    "$actual_build" "$actual_status" "$actual_count" "$actual_offset" "$actual_length"
  return 1
}

FAILED=0
run_case "empty_list"       "empty"                                                || FAILED=1
run_case "n1_hit"           "hit 0 deadbeef"                                       || FAILED=1
run_case "n1_miss"          "miss deadbeef"                                        || FAILED=1
run_case "n4_hit_first"     "hit 0 010203 ff aabbcc 00"                           || FAILED=1
run_case "n4_hit_middle"    "hit 2 010203 ff aabbcc 00"                           || FAILED=1
run_case "n4_hit_last"      "hit 3 010203 ff aabbcc 00"                           || FAILED=1
run_case "n4_miss"          "miss 010203 ff aabbcc 00"                            || FAILED=1
run_case "n8_hit_6"         "hit 6 aa bb cc dd ee ff 001122334455 99"             || FAILED=1
run_case "long_hit"         "hit 0 $(printf 'aa%.0s' $(seq 1 160))"               || FAILED=1
run_case "large_valid_256"  "large 256 201"                                       || FAILED=1
run_case "old_cap_8192"    "count_boundary $MPT_WITNESS_INDEX_OLD_CAPACITY $MPT_WITNESS_INDEX_CAPACITY" || FAILED=1
run_case "old_cap_8193"    "count_boundary $((MPT_WITNESS_INDEX_OLD_CAPACITY + 1)) $MPT_WITNESS_INDEX_CAPACITY" || FAILED=1
run_case "exact_record_cap" "count_boundary $MPT_WITNESS_INDEX_CAPACITY $MPT_WITNESS_INDEX_CAPACITY" || FAILED=1
run_case "over_record_cap"  "count_boundary $((MPT_WITNESS_INDEX_CAPACITY + 1)) $MPT_WITNESS_INDEX_CAPACITY" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: indexed witness_lookup_by_hash matches Python over all 14 fixtures"
  exit 0
fi

echo "==> FAIL"
exit 1
