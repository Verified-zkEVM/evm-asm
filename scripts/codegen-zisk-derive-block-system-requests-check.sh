#!/usr/bin/env bash
# codegen-zisk-derive-block-system-requests-check.sh -- bead 8uld3.2.3 (EIP-7002/7251).
#
# Verify derive_block_system_requests runs BOTH system-call request derivations (withdrawal then
# consolidation) sequentially and copies each return_data body to a stable buffer (the verdict
# needs both live at once; system_call_returndata is a single shared buffer). Synthetic withdrawal
# predeploy RETURNs 76 bytes (byte[31]=0xAB); consolidation predeploy RETURNs 116 bytes (byte[31]=0xCD).
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
echo "==> emit zisk_derive_block_system_requests ELF"
lake exe codegen --program zisk_derive_block_system_requests --halt linux93 -o gen-out/zisk_dbsr
python3 -c "import struct; open('gen-out/zisk_dbsr.input','wb').write(struct.pack('<Q',0))"
"$ZISKEMU" -e gen-out/zisk_dbsr.elf -i gen-out/zisk_dbsr.input -o gen-out/zisk_dbsr.output -n 4000000 \
  >gen-out/zisk_dbsr.emu.log 2>&1 || true
python3 - <<'PY'
import struct
d=open('gen-out/zisk_dbsr.output','rb').read()
wl=struct.unpack('<Q',d[0:8])[0]; cl=struct.unpack('<Q',d[8:16])[0]
wb=struct.unpack('<Q',d[16:24])[0]; cb=struct.unpack('<Q',d[24:32])[0]; st=struct.unpack('<Q',d[32:40])[0]
ok=(wl==76 and cl==116 and wb==0xAB and cb==0xCD and st==0)
print(f"  wlen={wl} clen={cl} wbody[31]=0x{wb:x} cbody[31]=0x{cb:x} status={st}")
if not ok:
    print("  FAIL: two sequential system-call bodies not extracted (expect 76/116/0xAB/0xCD/0)")
    raise SystemExit(1)
print("  PASS: derive_block_system_requests extracted both system-call bodies (sequential, copy-out)")
PY
