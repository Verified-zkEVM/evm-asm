#!/usr/bin/env bash
# codegen-zisk-witness-codes-lookup-by-hash-indexed-check.sh -- independent witness.codes index path.
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

echo "==> emit zisk_witness_codes_lookup_by_hash_indexed ELF"
lake exe codegen --program zisk_witness_codes_lookup_by_hash_indexed --halt linux93 \
  -o gen-out/zisk_witness_codes_lookup_by_hash_indexed

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" mode="$2"
  local in_file="$REPO_ROOT/gen-out/zisk_witness_codes_lookup_by_hash_indexed_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_witness_codes_lookup_by_hash_indexed_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
from Crypto.Hash import keccak


def k(b):
    h = keccak.new(digest_bits=256)
    h.update(b)
    return h.digest()


def section_from_elements(elements):
    if not elements:
        return b''
    out = bytearray()
    offset = 4 * len(elements)
    for e in elements:
        out.extend(struct.pack('<I', offset))
        offset += len(e)
    out.extend(b''.join(elements))
    return bytes(out)

mode = '$mode'
parts = mode.split()
which = parts[0]
expected_build = 0
lookup_mode = 0
expected_state_enabled = 1
expected_code_enabled = 1
expected_indexed_calls = 1
expected_linear_calls = 0

if which == 'hit':
    elem_idx = int(parts[1])
    elements = [bytes.fromhex(a) for a in parts[2:]]
    target = k(elements[elem_idx])
    expected_status = 0
    expected_offset = 4 * len(elements) + sum(len(e) for e in elements[:elem_idx])
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
elif which == 'many':
    count = int(parts[1])
    elem_idx = int(parts[2])
    elements = [i.to_bytes(2, 'big') + bytes([i % 251]) for i in range(count)]
    target = k(elements[elem_idx])
    expected_status = 0
    expected_offset = 4 * len(elements) + sum(len(e) for e in elements[:elem_idx])
    expected_length = len(elements[elem_idx])
elif which == 'large':
    length = int(parts[1])
    elements = [bytes((i * 131 + 17) % 256 for i in range(length))]
    target = k(elements[0])
    expected_status = 0
    expected_offset = 4
    expected_length = length
elif which == 'mismatch':
    elements = [bytes.fromhex('aa'), bytes.fromhex('bbcc')]
    target = k(elements[0])
    expected_status = 1
    expected_offset = 0
    expected_length = 0
    lookup_mode = 1
    expected_indexed_calls = 0
    expected_linear_calls = 1
elif which == 'cap':
    count = 8193
    section = struct.pack('<I', 4 * count) + (b'\\x00' * (4 * (count - 1)))
    target = bytes.fromhex('deadbeef' * 8)
    expected_build = 1
    expected_status = 0
    expected_offset = 0
    expected_length = 0
    expected_code_enabled = 0
    expected_indexed_calls = 0
    expected_linear_calls = 0
else:
    raise SystemExit(f'unknown mode: {mode}')

if which != 'cap':
    section = section_from_elements(elements)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(section)))
    f.write(target)
    f.write(struct.pack('<Q', lookup_mode))
    f.write(section)
    pad = (-(8 + 32 + 8 + len(section))) % 8
    if pad:
        f.write(b'\\x00' * pad)

with open(sys.argv[1] + '.expected.txt', 'w') as f:
    f.write(' '.join(map(str, [
        expected_status, expected_offset, expected_length, expected_build,
        expected_state_enabled, expected_code_enabled,
        expected_indexed_calls, expected_linear_calls,
    ])))
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_witness_codes_lookup_by_hash_indexed.elf \
    -i "$in_file" -o "$out_file" -n 50000000 \
    >"$REPO_ROOT/gen-out/zisk_witness_codes_lookup_by_hash_indexed_${name}.emu.log" 2>&1 || true

  if [[ ! -f "$in_file.expected.txt" ]]; then
    printf "  %-24s FAIL (Python helper failed to write expected)\n" "$name"
    return 1
  fi

  local expected_status expected_offset expected_length expected_build expected_state expected_code expected_indexed expected_linear
  read -r expected_status expected_offset expected_length expected_build expected_state expected_code expected_indexed expected_linear <"$in_file.expected.txt"

  local vals
  vals="$(python3 - "$out_file" <<'PY2'
import struct, sys
from pathlib import Path
b = Path(sys.argv[1]).read_bytes()
vals = []
for off in range(0, 64, 8):
    vals.append(struct.unpack('<Q', b[off:off+8])[0] if len(b) >= off + 8 else None)
print(' '.join('None' if v is None else str(v) for v in vals))
PY2
)"
  local actual_status actual_offset actual_length actual_build actual_state actual_code actual_indexed actual_linear
  read -r actual_status actual_offset actual_length actual_build actual_state actual_code actual_indexed actual_linear <<< "$vals"

  if [[ "$actual_status" == "$expected_status" && \
        "$actual_offset" == "$expected_offset" && \
        "$actual_length" == "$expected_length" && \
        "$actual_build" == "$expected_build" && \
        "$actual_state" == "$expected_state" && \
        "$actual_code" == "$expected_code" && \
        "$actual_indexed" == "$expected_indexed" && \
        "$actual_linear" == "$expected_linear" ]]; then
    printf "  %-24s OK   build=%s status=%s off=%s len=%s state=%s code=%s indexed=%s linear=%s\n" \
      "$name" "$actual_build" "$actual_status" "$actual_offset" "$actual_length" \
      "$actual_state" "$actual_code" "$actual_indexed" "$actual_linear"
    return 0
  fi

  printf "  %-24s FAIL\n    expected: build=%s status=%s off=%s len=%s state=%s code=%s indexed=%s linear=%s\n    actual:   build=%s status=%s off=%s len=%s state=%s code=%s indexed=%s linear=%s\n    log=%s\n" \
    "$name" "$expected_build" "$expected_status" "$expected_offset" "$expected_length" \
    "$expected_state" "$expected_code" "$expected_indexed" "$expected_linear" \
    "$actual_build" "$actual_status" "$actual_offset" "$actual_length" \
    "$actual_state" "$actual_code" "$actual_indexed" "$actual_linear" \
    "$REPO_ROOT/gen-out/zisk_witness_codes_lookup_by_hash_indexed_${name}.emu.log"
  return 1
}

FAILED=0
run_case "empty_list"       "empty"                         || FAILED=1
run_case "n1_hit"           "hit 0 deadbeef"                || FAILED=1
run_case "n1_miss"          "miss deadbeef"                 || FAILED=1
run_case "many_hit_97"      "many 128 97"                   || FAILED=1
run_case "large_predeploy"  "large 72945"                   || FAILED=1
run_case "section_mismatch" "mismatch"                      || FAILED=1
run_case "over_record_cap"  "cap"                           || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: independent witness.codes indexed lookup covers hit/miss/large/mismatch/cap cases"
  exit 0
fi

echo "==> FAIL"
exit 1
