#!/usr/bin/env bash
# codegen-zisk-selfdestruct-transfer-descriptors-check.sh -- verify the
# SELFDESTRUCT balance-transfer descriptor helper.
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
lake build codegen >/dev/null

echo "==> emit zisk_selfdestruct_transfer_descriptors probe ELF"
lake exe codegen --program zisk_selfdestruct_transfer_descriptors --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_selfdestruct_transfer_descriptors"

run_case() {
  local name="$1" origin="$2" beneficiary="$3" same="$4" created="$5" mode0="$6" count="$7"
  local in_file="$REPO_ROOT/gen-out/zisk_selfdestruct_transfer_descriptors_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_selfdestruct_transfer_descriptors_${name}.output"

  uv run --directory execution-specs --quiet python3 - "$in_file" "$origin" "$beneficiary" "$same" "$created" "$mode0" "$count" <<'PY'
import struct
import sys
from Crypto.Hash import keccak

out_path, origin_hex, beneficiary_hex, same_s, created_s, mode0_s, count_s = sys.argv[1:]
origin = bytes.fromhex(origin_hex)
beneficiary = bytes.fromhex(beneficiary_hex)
same = int(same_s)
created = int(created_s)
mode0 = int(mode0_s)
count = int(count_s)
if len(origin) != 20 or len(beneficiary) != 20:
    raise SystemExit("addresses must be 20 bytes")
origin_value = bytes.fromhex("f846018411223344a0" + "11" * 32 + "a0" + "22" * 32)
beneficiary_value = bytes.fromhex("f846028455667788a0" + "33" * 32 + "a0" + "44" * 32)
if len(origin_value) > 96 or len(beneficiary_value) > 96:
    raise SystemExit("probe value slot too small")
body = (
    origin
    + beneficiary
    + struct.pack("<Q", same)
    + struct.pack("<Q", created)
    + struct.pack("<Q", len(origin_value))
    + struct.pack("<Q", len(beneficiary_value))
    + origin_value
    + b"\x00" * (96 - len(origin_value))
    + beneficiary_value
    + b"\x00" * (96 - len(beneficiary_value))
)
with open(out_path, "wb") as f:
    f.write(body)

def path(addr: bytes) -> bytes:
    digest = keccak.new(digest_bits=256).update(addr).digest()
    out = bytearray(64)
    for i, b in enumerate(digest):
        out[2 * i] = b >> 4
        out[2 * i + 1] = b & 0x0F
    return bytes(out)

desc0 = (
    struct.pack("<Q", 0xA0010060)
    + struct.pack("<Q", 64)
    + struct.pack("<Q", 0xA0020010)
    + struct.pack("<Q", len(origin_value))
    + struct.pack("<Q", mode0)
)
descs = desc0
paths = path(origin)
if count == 2 and same == 1 and created == 1:
    descs += (
        struct.pack("<Q", 0xA00100A0)
        + struct.pack("<Q", 64)
        + struct.pack("<Q", 0)
        + struct.pack("<Q", 0)
        + struct.pack("<Q", 2)
    )
    paths += path(origin)
elif count == 2:
    descs += (
        struct.pack("<Q", 0xA00100A0)
        + struct.pack("<Q", 64)
        + struct.pack("<Q", 0xA0020080)
        + struct.pack("<Q", len(beneficiary_value))
        + struct.pack("<Q", 0)
    )
    paths += path(beneficiary)
with open(out_path + ".expected_desc", "wb") as f:
    f.write(descs)
with open(out_path + ".expected_path", "wb") as f:
    f.write(paths)
PY

  "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_selfdestruct_transfer_descriptors.elf" \
    -i "$in_file" -o "$out_file" -n 1000000 >/dev/null 2>&1 </dev/null \
    || { echo "  ERROR  $name"; return 1; }

  uv run --directory execution-specs --quiet python3 - "$out_file" "$in_file.expected_desc" "$in_file.expected_path" "$count" "$name" <<'PY'
import struct
import sys

out_path, desc_path, path_path, count_s, name = sys.argv[1:]
count = int(count_s)
with open(out_path, "rb") as f:
    out = f.read()
with open(desc_path, "rb") as f:
    expected_desc = f.read()
with open(path_path, "rb") as f:
    expected_path = f.read()
status = struct.unpack_from("<Q", out, 0)[0]
dup_status = struct.unpack_from("<Q", out, 248)[0]
actual_count = struct.unpack_from("<Q", out, 8)[0]
actual_desc = out[16:16 + 40 * count]
actual_path = out[96:96 + 64 * count]
if status == 0 and dup_status == 0 and actual_count == count and actual_desc == expected_desc and actual_path == expected_path:
    print(f"  PASS   {name}")
    raise SystemExit(0)
print(f"  FAIL   {name} status={status} dup_status={dup_status} count={actual_count}")
print(f"    desc expected: {expected_desc.hex()}")
print(f"    desc actual:   {actual_desc.hex()}")
print(f"    path expected: {expected_path[:32].hex()}...")
print(f"    path actual:   {actual_path[:32].hex()}...")
raise SystemExit(1)
PY
}

fail=0
run_case "different" "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" \
  "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" 0 0 0 2 || fail=1
run_case "same_keep" "cccccccccccccccccccccccccccccccccccccccc" \
  "cccccccccccccccccccccccccccccccccccccccc" 1 0 3 1 || fail=1
run_case "same_burn" "dddddddddddddddddddddddddddddddddddddddd" \
  "dddddddddddddddddddddddddddddddddddddddd" 1 1 0 2 || fail=1

[[ "$fail" -eq 0 ]] && echo "==> PASS: SELFDESTRUCT transfer descriptors match mpt_state_root_ins shape" \
  || { echo "==> FAIL"; exit 1; }
