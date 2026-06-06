#!/usr/bin/env bash
# codegen-zisk-storage-access-outcome-records-check.sh -- storage warmth records.
#
# Exercises evm_storage_access_charge_key directly and checks that each access
# appends an outcome record:
#   - first slot A touch: cold, charges 2000;
#   - repeated slot A touch: warm, charges 0;
#   - first slot B touch: cold, charges 2000.
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

echo "==> emit zisk_storage_access_outcome_records ELF"
lake exe codegen --program zisk_storage_access_outcome_records --halt linux93 \
  -o gen-out/zisk_storage_access_outcome_records

in_file="gen-out/zisk_storage_access_outcome_records.input"
out_file="gen-out/zisk_storage_access_outcome_records.output"
log_file="gen-out/zisk_storage_access_outcome_records.emu.log"

python3 - "$in_file" <<'PY'
import struct
import sys

path = sys.argv[1]
slot_a = bytes.fromhex("11" * 32)
slot_b = bytes.fromhex("22" * 32)

with open(path, "wb") as f:
    f.write(struct.pack("<Q", 5000))
    f.write(slot_a)
    f.write(slot_b)
PY

"$ZISKEMU" -e gen-out/zisk_storage_access_outcome_records.elf \
  -i "$in_file" -o "$out_file" -n 500000 \
  >"$log_file" 2>&1

expected="$(python3 - <<'PY'
import struct

parts = [
    3,     # outcome records appended
    2,     # warm storage-key table contains slot A and slot B
    1000,  # final gas after two cold deltas
    1, 2000,
    0, 0,
    1, 2000,
]
print(b"".join(struct.pack("<Q", x) for x in parts).hex())
PY
)"

actual="$(xxd -p -c 256 -l 72 "$out_file" | tr -d '\n')"

echo "expected:"
echo "  $expected"
echo "actual:"
echo "  $actual"

if [[ "$actual" != "$expected" ]]; then
  echo "FAIL: storage access outcome records" >&2
  exit 1
fi

echo "==> PASS: storage access outcomes record warm/cold status and gas deltas"
