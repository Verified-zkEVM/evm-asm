#!/usr/bin/env bash
# codegen-zisk-sstore-clear-gas-check.sh -- regression pin for the SSTORE-clear
# charge (formerly the bead .57.11.6.5.3 d'/bv_fail=41 undercount reproducer).
#
# Dispatches 10x (PUSH0; PUSH1 i; SSTORE) clearing slots 0..9 (each preloaded to 1)
# with gas=71050. Amsterdam spec: 21000 intrinsic + 10 x (2 + 3 + 5000) = 71050,
# where each cold clean-changing SSTORE-clear is 2100 cold + 2900 regular = 5000
# (no EIP-8037 state gas: the original is non-zero). Expects gas_left == 0 and all
# 10 SSTOREs executed (log_count = 10 preload + 10 appends = 20).
# History: this used to assert the d' undercharge (gas_left=25200), caused by
# BE-staged preload keys being invisible to the LE exec-log scan -- fixed in
# dispatch_tx_runtime_code (BAL keys) and in the probe's own preload (now LE).
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi
mkdir -p gen-out
echo "==> lake build codegen"; lake build codegen
echo "==> emit zisk_sstore_clear_gas_probe"
lake exe codegen --program zisk_sstore_clear_gas_probe --halt linux93 -o gen-out/zisk_scgp
python3 -c "import struct; open('gen-out/zisk_scgp.input','wb').write(struct.pack('<Q',0))"
"$ZISKEMU" -e gen-out/zisk_scgp.elf -i gen-out/zisk_scgp.input -o gen-out/zisk_scgp.output -n 4000000 >gen-out/zisk_scgp.emu.log 2>&1 || true
python3 - <<'PY'
import struct
d=open('gen-out/zisk_scgp.output','rb').read()
gl=struct.unpack('<Q',d[0:8])[0]; lc=struct.unpack('<Q',d[8:16])[0]; st=struct.unpack('<Q',d[16:24])[0]
print(f"  status={st} gas_left={gl} log_count={lc} (block_inc={71050-gl})")
# correctness invariants: staged+dispatched ok, all 10 SSTOREs ran (10 preload + 10 appends = 20)
assert st==0, f"staging/dispatch failed (status={st})"
assert lc==20, f"not all 10 SSTOREs executed (log_count={lc}, expected 20)"
assert gl==0, f"SSTORE-clear charge drifted: gas_left={gl}, expected 0 (each clear = 5000)"
print("  PASS: all 10 cold SSTORE-clears charged the full 5000 (gas_left=0).")
PY
