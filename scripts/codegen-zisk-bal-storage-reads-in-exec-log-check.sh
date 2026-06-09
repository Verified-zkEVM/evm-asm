#!/usr/bin/env bash
# codegen-zisk-bal-storage-reads-in-exec-log-check.sh -- bead bmvmx.1.6.7.
# Checks bal_storage_reads_in_exec_log: every BAL storage_read (AccountChanges item 2)
# slot must appear in the persistent exec log keyed on the account (was accessed).
# storage_reads is consensus-bound but NOT in the state root, so this is non-redundant.
# Probe: exec log accesses slots 7,9; BAL reads [7,9] -> 0; BAL reads [7,0x0b] -> 1.
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
echo "==> emit zisk_bal_storage_reads_in_exec_log ELF"
lake exe codegen --program zisk_bal_storage_reads_in_exec_log --halt linux93 -o gen-out/zisk_bsr
: > gen-out/zisk_bsr.input
"$ZISKEMU" -e gen-out/zisk_bsr.elf -i gen-out/zisk_bsr.input -o gen-out/zisk_bsr.output -n 100000000 >gen-out/zisk_bsr.emu.log 2>&1
python3 - <<'PY'
import struct, sys
d = open('gen-out/zisk_bsr.output', 'rb').read()
def u(o): return struct.unpack('<Q', d[o:o+8])[0] if o+8 <= len(d) else None
ok = (u(0) == 0) and (u(8) == 1)
print(f"  both reads present={u(0)} (exp 0)   absent read={u(8)} (exp 1)")
sys.exit(0 if ok else 1)
PY
echo; echo "==> PASS: bal_storage_reads_in_exec_log accepts present reads, rejects an absent one"
