#!/usr/bin/env bash
# codegen-zisk-storage-access-gas-check.sh -- runtime storage-key warmth helper.
#
# Exercises evm_storage_access_charge_key directly:
#   - first touch of slot A charges the 2000 cold delta and inserts it;
#   - repeating slot A is warm and charges nothing;
#   - touching slot B is cold and charges the delta again;
#   - insufficient gas returns status 2 without inserting.
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

echo "==> emit zisk_storage_access_gas ELF"
lake exe codegen --program zisk_storage_access_gas --halt linux93 \
  -o gen-out/zisk_storage_access_gas

run_case() {
  local name="$1" initial_gas="$2" expected_hex="$3"
  local in_file="gen-out/zisk_storage_access_gas_${name}.input"
  local out_file="gen-out/zisk_storage_access_gas_${name}.output"
  local log_file="gen-out/zisk_storage_access_gas_${name}.emu.log"

  python3 - "$in_file" "$initial_gas" <<'PY'
import struct
import sys

path = sys.argv[1]
initial_gas = int(sys.argv[2], 0)
slot_a = bytes.fromhex("11" * 32)
slot_b = bytes.fromhex("22" * 32)

with open(path, "wb") as f:
    f.write(struct.pack("<Q", initial_gas))
    f.write(slot_a)
    f.write(slot_b)
PY

  "$ZISKEMU" -e gen-out/zisk_storage_access_gas.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$log_file" 2>&1

  local actual
  actual="$(xxd -p -c 256 -l 72 "$out_file" | tr -d '\n')"

  echo "==> $name"
  echo "expected:"
  echo "  $expected_hex"
  echo "actual:"
  echo "  $actual"

  if [[ "$actual" != "$expected_hex" ]]; then
    echo "FAIL: $name" >&2
    return 1
  fi
}

EXPECTED_OK="$(python3 - <<'PY'
import struct
parts = [
    (1, 3000, 1),  # cold slot A: charge 2000
    (0, 3000, 1),  # warm slot A: no charge
    (1, 1000, 2),  # cold slot B: charge 2000
]
print(b"".join(struct.pack("<Q", x) for triple in parts for x in triple).hex())
PY
)"

EXPECTED_OOG="$(python3 - <<'PY'
import struct
parts = [
    (2, 1999, 0),  # cold slot A: not enough gas, no insert
    (2, 1999, 0),  # still cold and still no insert
    (2, 1999, 0),  # slot B also cannot insert
]
print(b"".join(struct.pack("<Q", x) for triple in parts for x in triple).hex())
PY
)"

FAILED=0
run_case "cold_warm_cold" 5000 "$EXPECTED_OK" || FAILED=1
run_case "out_of_gas" 1999 "$EXPECTED_OOG" || FAILED=1

if [[ "$FAILED" -ne 0 ]]; then
  exit 1
fi

echo "==> PASS: storage access gas helper charges cold delta and tracks warm keys"
