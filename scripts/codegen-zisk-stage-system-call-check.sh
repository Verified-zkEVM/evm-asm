#!/usr/bin/env bash
# codegen-zisk-stage-system-call-check.sh -- bead 8uld3.2.1.3 (EIP-7002/7251/6110).
#
# End-to-end check for stage_system_call: stage a SYSTEM call to a synthetic
# predeploy that RETURNs 32 known bytes (PUSH1 0x42; PUSH1 0; MSTORE; PUSH1 32;
# PUSH1 0; RETURN), run it through the callable runtime dispatcher with
# system_call_mode=1, and assert the depth-0 RETURN (#8681) was captured into
# system_call_returndata.
#
# Regression guard for the 8uld3.1a x5-clobber bug (the input-driven dispatcher
# setup must preserve the x5 input-walk cursor across the per-tx log-data resets,
# else the M30 gas trailer reads 0 -> OOG before any opcode -> capture is empty).
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

echo "==> emit zisk_stage_system_call ELF"
lake exe codegen --program zisk_stage_system_call --halt linux93 -o gen-out/zisk_ssc

python3 -c "import struct; open('gen-out/zisk_ssc.input','wb').write(struct.pack('<Q',0))"

"$ZISKEMU" -e gen-out/zisk_ssc.elf -i gen-out/zisk_ssc.input -o gen-out/zisk_ssc.output -n 2000000 \
  >gen-out/zisk_ssc.emu.log 2>&1 || true

python3 - <<'PY'
import struct
d = open('gen-out/zisk_ssc.output', 'rb').read()
returndata_len = struct.unpack('<Q', d[0:8])[0]
status         = struct.unpack('<Q', d[8:16])[0]
rd31           = struct.unpack('<Q', d[16:24])[0]
rd0            = struct.unpack('<Q', d[24:32])[0]
ok = (returndata_len == 32 and status == 0 and rd31 == 0x42 and rd0 == 0x00)
print(f"  returndata_len={returndata_len} status={status} returndata[31]=0x{rd31:x} returndata[0]=0x{rd0:x}")
if not ok:
    print("  FAIL: system-call did not capture the predeploy RETURN (expect len=32, [31]=0x42, [0]=0x00, status=0)")
    raise SystemExit(1)
print("  PASS: stage_system_call captured the predeploy depth-0 RETURN (32 bytes, byte[31]=0x42)")
PY
