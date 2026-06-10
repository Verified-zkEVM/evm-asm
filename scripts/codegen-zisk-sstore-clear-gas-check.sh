#!/usr/bin/env bash
# codegen-zisk-sstore-clear-gas-check.sh -- diagnostic for bead .57.11.6.5.3 (d'/bv_fail=41).
#
# Reproduces the multi_transaction_gas_accounting tx0 regular-gas undercount STANDALONE:
# dispatch 10x (PUSH0; PUSH1 i; SSTORE) clearing slots 0..9 (each preloaded to 1) with gas=71050.
# FINDINGS (claude-c1): the dispatch runs ALL 10 SSTOREs (log_count=20) but charges only 45850
# (gas_left=25200) vs the spec's 71050 (10 cold SSTORE-clears @5000). Isolated: the FIRST SSTORE
# charges 5000 (correct cold); the 2nd+ DISTINCT slots charge 2200 = 100 static + 2000 cold-access
# + 100 DIRTY transition -> the handler mis-sees repeated-tx SSTOREs as DIRTY (wrong original/current
# from the log scan), charging the 100 dirty path instead of 2900 clean-changing. This is the (d')
# block_regular undercount that false-rejects mtx rows 1-8 (bv_fail=41).
# Asserts the dispatch INVARIANTS (status=0, all 10 SSTOREs executed) and documents the undercharge
# (gas_left=25200; the fix target is gas_left~0 / each SSTORE 5000).
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
if gl==0:
    print("  FIXED: gas_left=0 -> all SSTORE-clears charged correctly (5000 each). Update this check.")
else:
    print(f"  KNOWN BUG (d'/.57.11.6.5.3): gas_left={gl} (expect 25200) -> block_regular undercount; "
          f"2nd+ SSTOREs charged ~2200 (dirty) not 5000 (cold clean-changing). Fix target: gas_left~0.")
    assert gl==25200, f"undercharge magnitude changed ({gl} != 25200) -- investigate"
print("  PASS (reproducer): dispatch ran all 10 SSTOREs; the undercharge is characterized.")
PY
