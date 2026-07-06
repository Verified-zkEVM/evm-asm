#!/usr/bin/env bash
# codegen-zisk-runtime-access-seed-initial-check.sh -- initial warm account seed probe.
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

echo "==> emit zisk_runtime_access_seed_initial ELF"
lake exe codegen --program zisk_runtime_access_seed_initial --halt linux93 \
  -o gen-out/zisk_runtime_access_seed_initial

in_file="gen-out/zisk_runtime_access_seed_initial.input"
out_file="gen-out/zisk_runtime_access_seed_initial.output"
python3 -c "open('$in_file', 'wb').write(b'\x00' * 8)"

"$ZISKEMU" -e gen-out/zisk_runtime_access_seed_initial.elf \
  -i "$in_file" -o "$out_file" -n 500000 \
  >gen-out/zisk_runtime_access_seed_initial.emu.log 2>&1 || true

expected="$(
python3 - <<'PY'
import struct
# (status, gasRemaining, count):
# ADDRESS, CALLER, ORIGIN are seeded warm; unrelated address is cold;
# active precompile 0x04 remains warm through the helper fast path.
vals = [
    0, 10000, 3,
    0, 10000, 3,
    0, 10000, 3,
    1, 7500, 4,
    0, 7500, 4,
]
print(b''.join(struct.pack('<Q', v) for v in vals).hex())
PY
)"
actual="$(xxd -p -l $(( ${#expected} / 2 )) "$out_file" | tr -d '\n')"

if [[ "$actual" == "$expected" ]]; then
  echo "==> PASS: runtime_access_seed_initial_accounts seeds ADDRESS/CALLER/ORIGIN"
  exit 0
else
  echo "==> FAIL"
  echo "expected: $expected"
  echo "actual:   $actual"
  echo "emulator log: gen-out/zisk_runtime_access_seed_initial.emu.log"
  exit 1
fi
