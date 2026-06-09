#!/usr/bin/env bash
# codegen-zisk-create-code-effect-log-check.sh
# Known-answer probe for the CREATE code-effect log (bead fhsxz.2.4.2.61.8b, .8b-1):
# append two deployed-code records, look up both + a missing address, assert the
# surfaced fields. No input needed (the probe builds its test data inline).
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  elif [[ -x /var/tmp/zisk-shared/ziskemu ]]; then
    ZISKEMU=/var/tmp/zisk-shared/ziskemu
  else
    echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2
    exit 1
  fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_create_code_effect_log ELF"
lake exe codegen --program zisk_create_code_effect_log --halt linux93 \
  -o gen-out/zisk_create_code_effect_log

"$ZISKEMU" -e gen-out/zisk_create_code_effect_log.elf \
  -o gen-out/zisk_create_code_effect_log.out -n 2000000 >/dev/null 2>&1 || true

python3 - <<'PY'
import struct, sys
d = open('gen-out/zisk_create_code_effect_log.out', 'rb').read()
vals = [struct.unpack('<Q', d[i:i+8])[0] for i in range(0, 72, 8)]
labels = ['find(A)!=0','A.has_code_change','A.code_len','A.code[0]','A.code[1]',
          'B.code_len','B.code[0]','find(C)==0','count']
exp = [1, 1, 2, 0x60, 0xff, 1, 0x00, 1, 2]
ok = True
for l, v, e in zip(labels, vals, exp):
    status = 'OK' if v == e else 'FAIL'
    if v != e: ok = False
    print(f"  {status:4} {l:20} got={v} exp={e}")
if not ok:
    print("==> FAIL"); sys.exit(1)
print("==> PASS: CREATE code-effect log append + lookup")
PY
