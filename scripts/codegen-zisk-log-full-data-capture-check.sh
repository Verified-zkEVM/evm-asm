#!/usr/bin/env bash
# codegen-zisk-log-full-data-capture-check.sh -- bead 8uld3.1a (EIP-6110 prereq).
#
# Drives logCapturePreBody (LOG0) with a 64-byte (> 32) data region and verifies
# that the FULL data lands in the persistent evm_log_data buffer (not just the
# truncated 32-byte descriptor prefix), with a correct parallel
# evm_log_data_meta[0] = (offset, len) entry. The previous capture kept only the
# first 32 bytes + a mem pointer that is stale at block-end, so parse_deposit_requests
# could not read the 576-byte DepositEvent.
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

echo "==> emit zisk_log_full_data_capture ELF"
lake exe codegen --program zisk_log_full_data_capture --halt linux93 -o gen-out/zisk_log_full_data_capture

python3 -c "import struct; open('gen-out/zisk_lfdc.input','wb').write(struct.pack('<Q',0))"

"$ZISKEMU" -e gen-out/zisk_log_full_data_capture.elf \
  -i gen-out/zisk_lfdc.input -o gen-out/zisk_lfdc.output -n 2000000 \
  >gen-out/zisk_lfdc.emu.log 2>&1 || true

python3 - <<'PY'
import struct
d = open('gen-out/zisk_lfdc.output','rb').read()
used = struct.unpack('<Q', d[0:8])[0]
ovf  = struct.unpack('<Q', d[8:16])[0]
moff = struct.unpack('<Q', d[16:24])[0]
mlen = struct.unpack('<Q', d[24:32])[0]
cap  = d[32:96]
expect = bytes(range(1,65))
ok = (used==64 and ovf==0 and moff==0 and mlen==64 and cap==expect)
print(f"  used={used} overflow={ovf} meta=({moff},{mlen}) full64={'yes' if cap==expect else 'NO'}")
if not ok:
    print("  FAIL: full-data capture incorrect")
    raise SystemExit(1)
print("  PASS: full 64-byte log data captured into evm_log_data (untruncated)")
PY
