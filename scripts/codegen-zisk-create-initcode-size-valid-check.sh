#!/usr/bin/env bash
# codegen-zisk-create-initcode-size-valid-check.sh
# Known-answer probe for create_initcode_size_valid (Amsterdam EIP-3860 MAX_INITCODE_SIZE 65536
# = 2 * EIP-7954 MAX_CODE_SIZE 0x8000), the init-code size gate a CREATE/CREATE2 must pass
# before executing init code. No input. (bead xpgl5: was stale 49152 = pre-Amsterdam 2*0x6000.)
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)";
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu";
  elif [[ -x /var/tmp/zisk-shared/ziskemu ]]; then ZISKEMU=/var/tmp/zisk-shared/ziskemu;
  else echo "ziskemu not found" >&2; exit 1; fi
fi
mkdir -p gen-out
echo "==> lake build codegen"; lake build codegen
echo "==> emit zisk_create_initcode_size_valid ELF"
lake exe codegen --program zisk_create_initcode_size_valid --halt linux93 -o gen-out/zisk_create_initcode_size_valid
"$ZISKEMU" -e gen-out/zisk_create_initcode_size_valid.elf -o gen-out/zisk_create_initcode_size_valid.out -n 2000000 >/dev/null 2>&1 || true
python3 - <<'PY'
import struct, sys
d = open('gen-out/zisk_create_initcode_size_valid.out','rb').read()
vals = [struct.unpack('<Q', d[i:i+8])[0] for i in range(0,32,8)]
labels = ['len 0','len 32','len 65536','len 65537']; exp = [0,0,0,1]
ok = True
for l,v,e in zip(labels,vals,exp):
    s='OK' if v==e else 'FAIL'
    if v!=e: ok=False
    print(f"  {s:4} {l:12} got={v} exp={e}")
if not ok: print("==> FAIL"); sys.exit(1)
print("==> PASS: create_initcode_size_valid (EIP-3860 MAX_INITCODE_SIZE)")
PY
