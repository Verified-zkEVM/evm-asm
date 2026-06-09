#!/usr/bin/env bash
# codegen-zisk-create-roundtrip-check.sh
# End-to-end verification of the INLINE CREATE descent through the real dispatch
# loop (bead fhsxz.2.4.2.61.8): a depth-0 frame whose bytecode does CREATE then
# SSTOREs the deployed address to slot 0. Asserts halt 0, one emitted slot, key 0,
# and a NON-ZERO value (CREATE staged init code, ran the mini-interp, derived +
# pushed a keccak address through the inline tail). No input.
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  elif [[ -x /var/tmp/zisk-shared/ziskemu ]]; then
    ZISKEMU=/var/tmp/zisk-shared/ziskemu
  else
    echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2
    exit 1
  fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_create_roundtrip ELF"
lake exe codegen --program zisk_create_roundtrip --halt linux93 \
  -o gen-out/zisk_create_roundtrip

"$ZISKEMU" -e gen-out/zisk_create_roundtrip.elf \
  -o gen-out/zisk_create_roundtrip.out -n 5000000 >/dev/null 2>&1 || true

python3 - <<'PY'
import struct, sys
d = open('gen-out/zisk_create_roundtrip.out', 'rb').read()
def w(off): return struct.unpack('<Q', d[off:off+8])[0]
halt, cnt, key, val = w(32), w(56), w(64), w(96)
print(f"  halt_kind(+32)  = {halt} (exp 0)")
print(f"  slot count(+56) = {cnt} (exp 1)")
print(f"  slot0 key(+64)  = {key} (exp 0)")
print(f"  slot0 val(+96)  = {hex(val)} (exp != 0 : deployed CREATE address low limb)")
if halt == 0 and cnt == 1 and key == 0 and val != 0:
    print("==> PASS: inline CREATE descent deployed + pushed a non-zero address through the dispatch loop")
else:
    print("==> FAIL"); sys.exit(1)
PY
