#!/usr/bin/env bash
# codegen-zisk-runtime-access-seed-account-list-check.sh -- access-list account warm seeding.
#
# Exercises runtime_access_seed_account_list directly:
#   - a decoded access-list account A is inserted as warm without charging gas;
#   - duplicate A entries do not grow the warmth table;
#   - charging seeded A is warm and charges nothing;
#   - charging unlisted B is cold and charges the 2500 account cold delta.
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

echo "==> emit zisk_runtime_access_seed_account_list ELF"
lake exe codegen --program zisk_runtime_access_seed_account_list --halt linux93 \
  -o gen-out/zisk_runtime_access_seed_account_list

in_file="gen-out/zisk_runtime_access_seed_account_list.input"
out_file="gen-out/zisk_runtime_access_seed_account_list.output"
log_file="gen-out/zisk_runtime_access_seed_account_list.emu.log"

python3 - "$in_file" <<'PY'
import struct
import sys

path = sys.argv[1]
account_a = bytes.fromhex("00" * 16 + "aabbccdd") + bytes(12)

with open(path, "wb") as f:
    f.write(struct.pack("<Q", 2))
    f.write(account_a)
    f.write(account_a)
PY

"$ZISKEMU" -e gen-out/zisk_runtime_access_seed_account_list.elf \
  -i "$in_file" -o "$out_file" -n 500000 \
  >"$log_file" 2>&1

expected="$(python3 - <<'PY'
import struct

vals = [
    1, 5000,  # seed A,A: one warm entry, no charge
    0, 5000, 1,  # charge A: warm
    1, 2500, 2,  # charge unlisted B: cold
]
print(b"".join(struct.pack("<Q", x) for x in vals).hex())
PY
)"

actual="$(xxd -p -c 256 -l 64 "$out_file" | tr -d '\n')"

echo "expected:"
echo "  $expected"
echo "actual:"
echo "  $actual"

if [[ "$actual" != "$expected" ]]; then
  echo "FAIL: runtime account access-list seed helper" >&2
  echo "emulator log: $log_file" >&2
  exit 1
fi

echo "==> PASS: runtime account access-list seeding warms listed accounts without charging gas"
