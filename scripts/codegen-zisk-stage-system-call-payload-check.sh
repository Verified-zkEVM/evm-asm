#!/usr/bin/env bash
# codegen-zisk-stage-system-call-payload-check.sh -- bead 8uld3.2.1.2 (EIP-7002/7251).
#
# stage_system_call_payload stages an Amsterdam system call's runtime payload
# (process_unchecked_system_transaction): caller=origin=SYSTEM_ADDRESS, value 0, empty
# calldata, gas 30M, the predeploy code -- reusing stage_runtime_payload_code with a
# synthesized SYSTEM context record, then overwriting CALLER/ORIGIN with SYSTEM_ADDRESS.
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

echo "==> emit zisk_stage_system_call_payload ELF"
lake exe codegen --program zisk_stage_system_call_payload --halt linux93 -o gen-out/zisk_scc

python3 -c "import struct; open('gen-out/zisk_scc.input','wb').write(struct.pack('<Q',0))"

"$ZISKEMU" -e gen-out/zisk_scc.elf -i gen-out/zisk_scc.input -o gen-out/zisk_scc.output -n 2000000 \
  >gen-out/zisk_scc.emu.log 2>&1 || true

python3 - <<'PY'
import struct
d = open('gen-out/zisk_scc.output', 'rb').read()
codelen = struct.unpack('<Q', d[0:8])[0]
gas = struct.unpack('<Q', d[8:16])[0]
caller_ok = struct.unpack('<Q', d[16:24])[0]
status = struct.unpack('<Q', d[24:32])[0]
ok = (codelen == 6 and gas == 30_000_000 and caller_ok == 1 and status == 0)
print(f"  codelen={codelen} gas={gas} caller_ok={caller_ok} status={status}")
if not ok:
    print("  FAIL: system-call payload staging incorrect")
    raise SystemExit(1)
print("  PASS: predeploy code + SYSTEM caller (env+64) + 30M gas (env+448) staged")
PY
