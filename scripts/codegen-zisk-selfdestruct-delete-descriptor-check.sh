#!/usr/bin/env bash
# codegen-zisk-selfdestruct-delete-descriptor-check.sh -- verify the
# SELFDESTRUCT account-delete descriptor helper.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_selfdestruct_delete_descriptor probe ELF"
lake exe codegen --program zisk_selfdestruct_delete_descriptor --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_selfdestruct_delete_descriptor"

run_case() {
  local name="$1" address="$2"
  local in_file="$REPO_ROOT/gen-out/zisk_selfdestruct_delete_descriptor_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_selfdestruct_delete_descriptor_${name}.output"

  uv run --directory execution-specs --quiet python3 - "$in_file" "$address" <<'PY'
import struct
import sys
from Crypto.Hash import keccak

out_path, address_hex = sys.argv[1], sys.argv[2]
address = bytes.fromhex(address_hex)
if len(address) != 20:
    raise SystemExit("address must be 20 bytes")
digest = keccak.new(digest_bits=256).update(address).digest()
nibbles = bytearray(64)
for i, b in enumerate(digest):
    nibbles[2 * i] = b >> 4
    nibbles[2 * i + 1] = b & 0x0f
descriptor = (
    struct.pack("<Q", 0xA0010028)
    + struct.pack("<Q", 64)
    + struct.pack("<Q", 0)
    + struct.pack("<Q", 0)
    + struct.pack("<Q", 2)
)
with open(out_path, "wb") as f:
    f.write(address)
    f.write(b"\x00" * 4)
with open(out_path + ".expected_desc", "wb") as f:
    f.write(descriptor)
with open(out_path + ".expected_path", "wb") as f:
    f.write(nibbles)
PY

  "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_selfdestruct_delete_descriptor.elf" \
    -i "$in_file" -o "$out_file" -n 1000000 >/dev/null 2>&1 </dev/null \
    || { echo "  ERROR  $name"; return 1; }

  local status actual_desc actual_path expected_desc expected_path
  status="$(od -An -tu8 -j 248 -N 8 "$out_file" | tr -d ' \n')"
  actual_desc="$(xxd -p -l 40 "$out_file" | tr -d '\n')"
  actual_path="$(xxd -p -s 40 -l 64 "$out_file" | tr -d '\n')"
  expected_desc="$(xxd -p "$in_file.expected_desc" | tr -d '\n')"
  expected_path="$(xxd -p "$in_file.expected_path" | tr -d '\n')"

  if [[ "$status" == "0" && "$actual_desc" == "$expected_desc" && "$actual_path" == "$expected_path" ]]; then
    echo "  PASS   $name"
    return 0
  fi

  echo "  FAIL   $name status=$status"
  echo "    descriptor expected: $expected_desc"
  echo "    descriptor actual:   $actual_desc"
  echo "    path expected:       ${expected_path:0:64}..."
  echo "    path actual:         ${actual_path:0:64}..."
  return 1
}

fail=0
run_case "zero" "0000000000000000000000000000000000000000" || fail=1
run_case "alice" "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" || fail=1
run_case "beneficiary" "1234567890abcdef1234567890abcdef12345678" || fail=1

[[ "$fail" -eq 0 ]] && echo "==> PASS: SELFDESTRUCT delete descriptor matches mpt_state_root_ins shape" \
  || { echo "==> FAIL"; exit 1; }
