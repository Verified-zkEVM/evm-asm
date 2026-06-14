#!/usr/bin/env bash
# codegen-zisk-runtime-access-list-seeded-sload-check.sh
#
# Regression for nxio8.5.2b: the callable dispatcher setup hook seeds pending
# transaction access-list storage keys after evm_storage_access_count is reset.
# This focused executable arms the same pending globals, runs the hook, then
# charges the listed key directly. A seeded key must be warm: status 0, no gas
# delta, one warm-set key, and the pending globals cleared.
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

echo "==> emit zisk_runtime_access_list_seeded_sload ELF"
lake exe codegen --program zisk_runtime_access_list_seeded_sload --halt linux93 \
  -o gen-out/zisk_runtime_access_list_seeded_sload

out_file="gen-out/zisk_runtime_access_list_seeded_sload.output"
log_file="gen-out/zisk_runtime_access_list_seeded_sload.emu.log"

"$ZISKEMU" -e gen-out/zisk_runtime_access_list_seeded_sload.elf \
  -o "$out_file" -n 200000000 >"$log_file" 2>&1

EXPECTED="$(python3 - <<PY
import struct
# status, gas, count, pending ptr, pending len, pending fn
print(b"".join(struct.pack("<Q", x) for x in [0, 5000, 1, 0, 0, 0]).hex())
PY
)"

actual="$(xxd -p -c 256 -l 48 "$out_file" | tr -d '
')"

echo "expected:"
echo "  $EXPECTED"
echo "actual:"
echo "  $actual"

if [[ "$actual" != "$EXPECTED" ]]; then
  echo "FAIL: runtime access-list seeded SLOAD warmness" >&2
  exit 1
fi

echo "==> PASS: tx access-list seed hook warms listed storage keys before charging"
