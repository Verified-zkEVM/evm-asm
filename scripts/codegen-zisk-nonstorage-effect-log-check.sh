#!/usr/bin/env bash
# codegen-zisk-nonstorage-effect-log-check.sh
# Known-answer probe for the non-storage exec-effect producer (record_nonstorage_effect):
# append two per-account balance/nonce records (c2#5 112-byte layout) + read them back. No input.
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
echo "==> emit zisk_nonstorage_effect_log ELF"
lake exe codegen --program zisk_nonstorage_effect_log --halt linux93 -o gen-out/zisk_nonstorage_effect_log
"$ZISKEMU" -e gen-out/zisk_nonstorage_effect_log.elf -o gen-out/zisk_nonstorage_effect_log.out -n 2000000 >/dev/null 2>&1 || true
python3 - <<'PY'
import struct, sys
d = open('gen-out/zisk_nonstorage_effect_log.out','rb').read()
vals = [struct.unpack('<Q', d[i:i+8])[0] for i in range(0,64,8)]
labels = ['count','A.pre_bal','A.post_bal','A.pre_nonce','A.post_nonce','A.addr[0]','B.post_bal','B.post_nonce']
exp = [2,10,20,1,2,0x11,5,1]
ok = True
for l,v,e in zip(labels,vals,exp):
    s='OK' if v==e else 'FAIL'
    if v!=e: ok=False
    print(f"  {s:4} {l:14} got={v} exp={e}")
if not ok: print("==> FAIL"); sys.exit(1)
print("==> PASS: non-storage exec-effect producer (record_nonstorage_effect)")
PY
