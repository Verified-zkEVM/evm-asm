#!/usr/bin/env bash
# codegen-zisk-create-roundtrip-check.sh
# End-to-end verification of the INLINE CREATE descent through the real dispatch
# loop (bead fhsxz.2.4.2.61.8): a depth-0 frame whose bytecode does TWO sequential
# CREATEs by the same creator, SSTORE'ing each deployed address (slot 0, slot 1).
# Asserts halt 0, TWO emitted slots, and that slot{0,1} are DISTINCT non-zero
# addresses (slot 0 == the nonce-0 address regression; slot 1 != slot 0, proving the
# .8c-1 per-creator nonce increment AND that x13/mem-base survives SSTORE -> the
# double-CREATE panic fhsxz.2.4.2.61.8.3.4 is fixed). No input.
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
# Emitted slots: count at +56, then (key@+0, val@+32) 64 B records from +64.
# Output order is reverse-chronological (last-written first); match by key.
halt, cnt = w(32), w(56)
ka, va = w(64), w(96)
kb, vb = w(128), w(160)
slots = {ka: va, kb: vb}
KNOWN = 0xcb804a576fa48eb1   # nonce-0 CREATE address low limb (original single-CREATE regression)
print(f"  halt_kind(+32)   = {halt} (exp 0)")
print(f"  slot count(+56)  = {cnt} (exp 2)")
print(f"  record0 (+64/+96)   key={ka} val={hex(va)}")
print(f"  record1 (+128/+160) key={kb} val={hex(vb)}")
ok = (halt == 0 and cnt == 2 and 0 in slots and 1 in slots
      and slots[0] == KNOWN and slots[1] != 0 and slots[1] != slots[0])
if ok:
    print(f"  slot0 (nonce 0) = {hex(slots[0])} (== known {hex(KNOWN)})")
    print(f"  slot1 (nonce 1) = {hex(slots[1])} (!= slot0 -> distinct; x13 survived SSTORE)")
    print("==> PASS: two sequential CREATEs by one creator deployed DISTINCT addresses (double-CREATE panic fixed)")
else:
    print("==> FAIL"); sys.exit(1)
PY
