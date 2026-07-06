#!/usr/bin/env bash
# codegen-zisk-runtime-access-account-outcome-records-check.sh -- account warmth records.
#
# Exercises runtime_access_account_charge directly and checks that each normal
# access appends an outcome record:
#   - first account A touch: cold, charges 2500;
#   - repeated account A touch: warm, charges 0;
#   - active precompile 0x04 touch: precompile-warm, charges 0.
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

echo "==> emit zisk_runtime_access_account_outcome_records ELF"
lake exe codegen --program zisk_runtime_access_account_outcome_records --halt linux93 \
  -o gen-out/zisk_runtime_access_account_outcome_records

in_file="gen-out/zisk_runtime_access_account_outcome_records.input"
out_file="gen-out/zisk_runtime_access_account_outcome_records.output"
log_file="gen-out/zisk_runtime_access_account_outcome_records.emu.log"

python3 -c "open('$in_file', 'wb').write(b'\x00' * 8)"

"$ZISKEMU" -e gen-out/zisk_runtime_access_account_outcome_records.elf \
  -i "$in_file" -o "$out_file" -n 500000 \
  >"$log_file" 2>&1

expected="$(python3 - <<'PY'
import struct

parts = [
    3,    # outcome records appended
    1,    # warm account table contains only account A; precompile is not inserted
    500,  # final gas after one cold account delta
    1, 2500,
    0, 0,
    2, 0,
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
  echo "FAIL: runtime account access outcome records" >&2
  echo "emulator log: $log_file" >&2
  exit 1
fi

echo "==> PASS: account access outcomes record warm/cold/precompile status and gas deltas"
