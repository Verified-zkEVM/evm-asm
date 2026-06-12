#!/usr/bin/env bash
# codegen-zisk-stage-predeploy-storage-preload-check.sh -- bead 8uld3.2.1.4 (EIP-7002/7251).
#
# stage_predeploy_storage_preload composes bal_recipient_storage_keys (slot keys from the
# predeploy's BAL AccountChanges) + per-key slot_at_header_state_root (witness MPT -> original
# value) into the (key,value) storage preload for a system-call predeploy. This probe reuses
# the bal probe's AccountChanges fixture (one slot key 0x00..07) + a NULL witness, so the slot
# lookup fails and values are 0 -- verifying the key enumeration + pairing (the real MPT
# value-lookup is verified by the 8uld3.2.2 wiring).
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

echo "==> emit zisk_stage_predeploy_storage_preload ELF"
lake exe codegen --program zisk_stage_predeploy_storage_preload --halt linux93 -o gen-out/zisk_spsp

python3 -c "import struct; open('gen-out/zisk_spsp.input','wb').write(struct.pack('<Q',0))"

"$ZISKEMU" -e gen-out/zisk_spsp.elf -i gen-out/zisk_spsp.input -o gen-out/zisk_spsp.output -n 3000000 \
  >gen-out/zisk_spsp.emu.log 2>&1 || true

python3 - <<'PY'
import struct
d = open('gen-out/zisk_spsp.output', 'rb').read()
count = struct.unpack('<Q', d[0:8])[0]
k31 = struct.unpack('<Q', d[8:16])[0]
v0  = struct.unpack('<Q', d[16:24])[0]
k0  = struct.unpack('<Q', d[24:32])[0]
# 8uld3.2.3.3.1 Fix5: the preload writes the KEY byte-reversed (BE->LE) so the
# dispatcher's little-endian SLOAD key matches -- the BE slot key 0x00..07 lands
# with 0x07 at byte 0 and 0x00 at byte 31.
ok = (count == 1 and k31 == 0 and v0 == 0 and k0 == 0x07)
print(f"  count={count} key[0].b31={hex(k31)} value[0].b0={hex(v0)} key[0].b0={hex(k0)}")
if not ok:
    print("  FAIL: storage-preload key enumeration / pairing incorrect")
    raise SystemExit(1)
print("  PASS: slot key enumerated from BAL + (key,value) paired (value 0 on null-witness lookup)")
PY
