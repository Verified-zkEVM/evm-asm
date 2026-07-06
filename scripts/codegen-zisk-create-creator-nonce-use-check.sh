#!/usr/bin/env bash
# codegen-zisk-create-creator-nonce-use-check.sh
# Known-answer probe for create_creator_nonce_use (per-creator running nonce for
# multi-CREATE address correctness, bead .61.8). No input.
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
echo "==> emit zisk_create_creator_nonce_use ELF"
lake exe codegen --program zisk_create_creator_nonce_use --halt linux93 -o gen-out/zisk_create_creator_nonce_use
"$ZISKEMU" -e gen-out/zisk_create_creator_nonce_use.elf -o gen-out/zisk_create_creator_nonce_use.out -n 2000000 >/dev/null 2>&1 || true
python3 - <<'PY'
import struct, sys
d = open('gen-out/zisk_create_creator_nonce_use.out','rb').read()
vals = [struct.unpack('<Q', d[i:i+8])[0] for i in range(0,48,8)]
labels = ['use(A,5)','use(A,5)','use(B,0)','use(A,5)','use(B,0)','count']; exp = [5,6,0,7,1,2]
ok = True
for l,v,e in zip(labels,vals,exp):
    s='OK' if v==e else 'FAIL'
    if v!=e: ok=False
    print(f"  {s:4} {l:10} got={v} exp={e}")
if not ok: print("==> FAIL"); sys.exit(1)
print("==> PASS: create_creator_nonce_use (per-creator running nonce)")
PY
