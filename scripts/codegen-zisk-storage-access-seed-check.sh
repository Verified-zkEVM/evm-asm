#!/usr/bin/env bash
# codegen-zisk-storage-access-seed-check.sh -- storage-key warm-set seeding.
#
# Exercises evm_storage_access_seed_key directly:
#   - seeding slot A inserts it without charging gas;
#   - duplicate seeding leaves the table unchanged;
#   - charging seeded slot A is warm and charges nothing;
#   - charging unseeded slot B is cold and charges the 2000 delta.
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

echo "==> emit zisk_storage_access_seed ELF"
lake exe codegen --program zisk_storage_access_seed --halt linux93 \
  -o gen-out/zisk_storage_access_seed

in_file="gen-out/zisk_storage_access_seed.input"
out_file="gen-out/zisk_storage_access_seed.output"
log_file="gen-out/zisk_storage_access_seed.emu.log"

python3 - "$in_file" <<'PY'
import struct
import sys

path = sys.argv[1]
initial_gas = 5000
slot_a = bytes.fromhex("11" * 32)
slot_b = bytes.fromhex("22" * 32)

with open(path, "wb") as f:
    f.write(struct.pack("<Q", initial_gas))
    f.write(slot_a)
    f.write(slot_b)
PY

"$ZISKEMU" -e gen-out/zisk_storage_access_seed.elf \
  -i "$in_file" -o "$out_file" -n 500000 \
  >"$log_file" 2>&1

EXPECTED="$(python3 - <<'PY'
import struct

parts = [
    (1, 5000, 1),  # seed slot A: insert warm, no charge
    (0, 5000, 1),  # duplicate seed slot A: no mutation
    (0, 5000, 1),  # charge slot A: warm, no charge
    (1, 3000, 2),  # charge slot B: cold, charge 2000
]
print(b"".join(struct.pack("<Q", x) for triple in parts for x in triple).hex())
PY
)"

actual="$(xxd -p -c 256 -l 96 "$out_file" | tr -d '\n')"

echo "expected:"
echo "  $EXPECTED"
echo "actual:"
echo "  $actual"

if [[ "$actual" != "$EXPECTED" ]]; then
  echo "FAIL: storage access seed helper" >&2
  exit 1
fi

echo "==> PASS: storage access seed helper warms keys without charging gas"
