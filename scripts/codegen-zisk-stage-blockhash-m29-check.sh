#!/usr/bin/env bash
# codegen-zisk-stage-blockhash-m29-check.sh -- bead evm-asm-3vc2p.3.
#
# stage_blockhash_m29 reconstructs the M29 recent-blockhash table (cur, count,
# count x 32-byte hashes in increasing block-number order) for a contract-recipient
# runtime execution, from the stateless witness.headers section. It counts the
# CONTIGUOUS recent ancestors [cur-1, cur-2, ...] present in the witness (stopping
# at the first gap), clamped to min(256, cur), and writes block_hashes[i] =
# keccak256(header for block cur-count+i).
#
# Output (112 bytes): cur@0, count@8, block_hashes[0..2]@16/+48/+80.
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2; exit 1; fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_stage_blockhash_m29 ELF"
lake exe codegen --program zisk_stage_blockhash_m29 --halt linux93 \
  -o gen-out/zisk_stage_blockhash_m29

REPO_ROOT="$(pwd)"

# run_case <name> <cur> <numbers_csv>
#   witness.headers = synthetic headers with the given block numbers (any order;
#   lookup is by NUMBER field). Expected cur/count/hashes computed below.
run_case() {
  local name="$1" cur="$2" numbers="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_sbm_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_sbm_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_sbm_${name}.expected"

  CUR="$cur" NUMBERS="$numbers" uv run --directory execution-specs --quiet python3 -c "
import struct, sys, os
import rlp
from Crypto.Hash import keccak

def k256(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

def build_ssz_section(elements):
    n = len(elements)
    if n == 0: return b''
    section = b''; offset = 4*n
    for e in elements:
        section += struct.pack('<I', offset); offset += len(e)
    for e in elements:
        section += e
    return section

def header_with_number(n):
    number_bytes = n.to_bytes((n.bit_length()+7)//8, 'big') if n > 0 else b''
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, b'\\x44'*32, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'',
        number_bytes,
        b'\\x83\\xff\\xff\\xff', b'',
        b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    return rlp.encode(fields)

cur = int(os.environ['CUR'])
numbers = [int(p) for p in os.environ['NUMBERS'].split(',') if p != '']
present = set(numbers)
headers = [header_with_number(n) for n in numbers]
section = build_ssz_section(headers)

# count = contiguous recent ancestors present, clamped to min(256, cur).
window = min(256, cur)
count = 0
while count < window and (cur - (count + 1)) in present:
    count += 1

# block_hashes[i] = keccak256(header for block cur-count+i)
exp = struct.pack('<Q', cur) + struct.pack('<Q', count)
for i in range(3):
    if i < count:
        exp += k256(header_with_number(cur - count + i))
    else:
        exp += b'\\x00' * 32

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', cur) + struct.pack('<Q', len(section)) + section
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)
with open(sys.argv[2], 'wb') as f:
    f.write(exp)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_stage_blockhash_m29.elf \
    -i "$in_file" -o "$out_file" -n 8000000 \
    >"$REPO_ROOT/gen-out/zisk_sbm_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"
  if [[ "$actual" == "$expected" ]]; then
    printf "  %-22s OK   %d bytes match\n" "$name" "$exp_size"; return 0
  fi
  printf "  %-22s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected" "$actual"; return 1
}

FAILED=0
# three contiguous ancestors present -> count=3, hashes in increasing-number order.
run_case "full3"        103 "100,101,102" || FAILED=1
# a gap at cur-2 (101 missing) stops the count at the most-recent contiguous run.
run_case "gap_stops"    103 "100,102"     || FAILED=1
# the most-recent ancestor (cur-1) is absent -> count=0, all-zero table.
run_case "none"         103 "50"          || FAILED=1
# window clamps to cur (=1); cur-1=0 absent -> count=0.
run_case "window_clamp" 1   "5"           || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: stage_blockhash_m29 M29 table reconstruction"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
