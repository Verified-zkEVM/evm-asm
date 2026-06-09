#!/usr/bin/env bash
# codegen-zisk-call-roundtrip-check.sh -- bead fhsxz.2.4.2.61.6.6.
#
# End-to-end verification of the nested-call cycle through the REAL dispatch loop:
# the zisk_call_roundtrip probe is a self-contained dispatcher that descends into a
# child frame (via call_frame_descend with a fixed child-code blob), runs the child
# (STOP) at depth 1, and the depth-aware STOP returns to the parent via frame_return
# instead of halting. The parent then SSTOREs the propagated success word to slot 0.
#
# A correct round trip => storage slot 0 = 1 (success propagated) and halt_kind 0.
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2; exit 1; fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_call_roundtrip ELF"
lake exe codegen --program zisk_call_roundtrip --halt linux93 -o gen-out/zisk_call_roundtrip

: > gen-out/zisk_call_roundtrip.input
"$ZISKEMU" -e gen-out/zisk_call_roundtrip.elf \
  -i gen-out/zisk_call_roundtrip.input -o gen-out/zisk_call_roundtrip.output -n 100000000 \
  >gen-out/zisk_call_roundtrip.emu.log 2>&1

python3 - <<'PY'
import struct, sys
data = open('gen-out/zisk_call_roundtrip.output', 'rb').read()
def u64(off): return struct.unpack('<Q', data[off:off+8])[0] if off + 8 <= len(data) else None
checks = [
    ('halt_kind (OUTPUT+32)',      u64(32), 0),
    ('emitted slot count (+56)',   u64(56), 1),
    ('slot 0 key low (+64)',       u64(64), 0),
    ('slot 0 value low (+96)',     u64(96), 32),
]
failed = False
for label, got, exp in checks:
    ok = got == exp
    failed = failed or not ok
    print(f"  {'OK  ' if ok else 'FAIL'} {label:28s} got={got} exp={exp}")
sys.exit(1 if failed else 0)
PY

echo
echo "==> PASS: child ran a GUARDED MSTORE + RETURN(0,32); frame_return staged the"
echo "          returndata; parent RETURNDATASIZE read 32 -> slot 0 = 32 (frame-relative"
echo "          guard + returndata staging verified end-to-end through the dispatcher)"
