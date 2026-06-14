#!/usr/bin/env bash
# codegen-zisk-call-depth-limit-check.sh -- bead fhsxz.2.4.2.61.10.
#
# Drive the CALL-handler depth-gate fragment at evm_call_depth=1024.
# It must reject before frame descent, push 0, leave depth unchanged,
# and advance the parent PC.
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

echo "==> emit zisk_call_depth_limit ELF"
lake exe codegen --program zisk_call_depth_limit --halt linux93 \
  -o gen-out/zisk_call_depth_limit

: > gen-out/zisk_call_depth_limit.input
"$ZISKEMU" -e gen-out/zisk_call_depth_limit.elf \
  -i gen-out/zisk_call_depth_limit.input -o gen-out/zisk_call_depth_limit.output -n 5000000 \
  >gen-out/zisk_call_depth_limit.emu.log 2>&1 || true

python3 - <<'PY'
import struct, sys
d = open('gen-out/zisk_call_depth_limit.output', 'rb').read()
def w(off):
    return struct.unpack('<Q', d[off:off+8])[0] if off + 8 <= len(d) else None

depth, result, stack_delta, pc_after = w(0), w(8), w(16), w(24)
print(f"  evm_call_depth after = {depth} (exp 1024)")
print(f"  CALL result          = {result} (exp 0)")
print(f"  stack delta          = {stack_delta} (exp 192)")
print(f"  parent PC after      = {pc_after:#x} (exp 0x501)")
ok = (depth == 1024 and result == 0 and stack_delta == 192 and pc_after == 0x501)
if ok:
    print("==> PASS: depth-1024 CALL fail path pushes 0 without descending")
else:
    print("==> FAIL")
    sys.exit(1)
PY
