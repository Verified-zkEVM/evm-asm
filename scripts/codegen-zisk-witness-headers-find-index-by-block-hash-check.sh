#!/usr/bin/env bash
# codegen-zisk-witness-headers-find-index-by-block-hash-check.sh
#
# Pure hash -> index search: locate the position i where
# keccak(witness.headers[i]) == block_hash.
#
# Output (64 bytes):
#   bytes  0.. 8 : status (0 = found, 1 = miss)
#   bytes  8..16 : index (u64; 0 on miss)
#   bytes 16..24 : index build status
#   bytes 24..32 : witness_lookup_by_hash call count
#   bytes 32..40 : indexed lookup call count
#   bytes 40..48 : linear lookup call count
#   bytes 48..56 : linear lookup iteration count
#   bytes 56..64 : index build entry count
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

echo "==> emit zisk_witness_headers_find_index_by_block_hash ELF"
lake exe codegen --program zisk_witness_headers_find_index_by_block_hash \
  --halt linux93 \
  -o gen-out/zisk_witness_headers_find_index_by_block_hash

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_whfi_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_whfi_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_whfi_${name}.expected"
  rm -f "$in_file" "$out_file" "$exp_file"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp
from Crypto.Hash import keccak

def k256(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

def encode_header(fill):
    sr = bytes([fill]) * 32
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, sr, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    return rlp.encode(fields)

def build_ssz_section(elements):
    n = len(elements)
    if n == 0: return b''
    section = b''
    offset = 4 * n
    for e in elements:
        section += struct.pack('<I', offset); offset += len(e)
    for e in elements: section += e
    return section

def expected_words(status, index, build_status, lookup_calls, indexed_calls, linear_calls, linear_iters, build_count):
    return b''.join(struct.pack('<Q', x) for x in (
        status, index, build_status, lookup_calls, indexed_calls,
        linear_calls, linear_iters, build_count,
    ))

def valid_expected(status, index, count):
    return expected_words(status, index, 0, 1, 1, 0, 0, count)

mode = '$mode'

if mode == 'three_idx0':
    headers = [encode_header(0x44), encode_header(0x55), encode_header(0x66)]
    witness_headers = build_ssz_section(headers)
    block_hash = k256(headers[0])
    expected = valid_expected(0, 0, len(headers))
elif mode == 'three_idx1':
    headers = [encode_header(0x44), encode_header(0x55), encode_header(0x66)]
    witness_headers = build_ssz_section(headers)
    block_hash = k256(headers[1])
    expected = valid_expected(0, 1, len(headers))
elif mode == 'three_idx2_last':
    headers = [encode_header(0x44), encode_header(0x55), encode_header(0x66)]
    witness_headers = build_ssz_section(headers)
    block_hash = k256(headers[2])
    expected = valid_expected(0, 2, len(headers))
elif mode == 'many_headers_last':
    headers = [encode_header((0x40 + i) % 256) for i in range(96)]
    witness_headers = build_ssz_section(headers)
    block_hash = k256(headers[-1])
    expected = valid_expected(0, len(headers) - 1, len(headers))
elif mode == 'miss':
    headers = [encode_header(0x44), encode_header(0x55)]
    witness_headers = build_ssz_section(headers)
    block_hash = b'\\xee' * 32
    expected = valid_expected(1, 0, len(headers))
elif mode == 'empty_section':
    witness_headers = b''
    block_hash = b'\\xee' * 32
    expected = valid_expected(1, 0, 0)
elif mode == 'malformed_short_offsets':
    witness_headers = b'\\x02\\x00\\x00'
    block_hash = b'\\xee' * 32
    expected = expected_words(1, 0, 1, 1, 0, 1, 0, 0)
else:
    raise SystemExit('bad mode: ' + mode)

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_headers))
        + block_hash
        + witness_headers
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_witness_headers_find_index_by_block_hash.elf \
    -i "$in_file" -o "$out_file" -n 12000000 \
    >"$REPO_ROOT/gen-out/zisk_whfi_${name}.emu.log" 2>&1 || true

  local exp_size
  exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-40s OK   %d bytes match\n" "$name" "$exp_size"
    return 0
  else
    printf "  %-40s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

FAILED=0
run_case "first_index_match"           three_idx0 || FAILED=1
run_case "middle_index_match"          three_idx1 || FAILED=1
run_case "last_index_match"            three_idx2_last || FAILED=1
run_case "many_headers_last_match"     many_headers_last || FAILED=1
run_case "unrelated_hash_miss"         miss || FAILED=1
run_case "empty_section_miss"          empty_section || FAILED=1
run_case "malformed_short_offsets"     malformed_short_offsets || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: witness_headers_find_index_by_block_hash end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
