#!/usr/bin/env bash
# codegen-zisk-derive-withdrawal-requests-check.sh -- bead 8uld3.2.2 (EIP-7002).
#
# End-to-end check for derive_withdrawal_requests: stage a synthetic WITHDRAWAL_REQUEST
# predeploy that RETURNs a 76-byte withdrawal record, run it through the system-call
# harness, and assert the captured return_data IS the withdrawal-request body (raw, the
# 0x01 type framing is added by assemble_execution_requests / RequestsHash at hash time).
# Predeploy: PUSH1 0xAB; PUSH1 0; MSTORE; PUSH1 76; PUSH1 0; RETURN -> body[31]=0xAB.
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

echo "==> emit zisk_derive_withdrawal_requests ELF"
lake exe codegen --program zisk_derive_withdrawal_requests --halt linux93 -o gen-out/zisk_dwr

python3 -c "import struct; open('gen-out/zisk_dwr.input','wb').write(struct.pack('<Q',0))"

"$ZISKEMU" -e gen-out/zisk_dwr.elf -i gen-out/zisk_dwr.input -o gen-out/zisk_dwr.output -n 2000000 \
  >gen-out/zisk_dwr.emu.log 2>&1 || true

python3 - <<'PY'
import struct
d = open('gen-out/zisk_dwr.output', 'rb').read()
body_len = struct.unpack('<Q', d[0:8])[0]
status   = struct.unpack('<Q', d[8:16])[0]
b31      = struct.unpack('<Q', d[16:24])[0]
b0       = struct.unpack('<Q', d[24:32])[0]
b75      = struct.unpack('<Q', d[32:40])[0]
ok = (body_len == 76 and status == 0 and b31 == 0xAB and b0 == 0x00 and b75 == 0x00)
print(f"  body_len={body_len} status={status} body[31]=0x{b31:x} body[0]=0x{b0:x} body[75]=0x{b75:x}")
if not ok:
    print("  FAIL: derive_withdrawal_requests did not return the 76-byte predeploy RETURN as the body")
    raise SystemExit(1)
print("  PASS: derive_withdrawal_requests body == return_data (76 bytes, byte[31]=0xAB)")
PY
