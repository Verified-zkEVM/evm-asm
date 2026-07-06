#!/usr/bin/env bash
# codegen-zisk-create-deployed-code-valid-check.sh
# Known-answer probe for create_deployed_code_valid (EIP-3541 + EIP-170), the
# deployed-code validity gate a successful CREATE/CREATE2 must pass. No input.
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

echo "==> emit zisk_create_deployed_code_valid ELF"
lake exe codegen --program zisk_create_deployed_code_valid --halt linux93 \
  -o gen-out/zisk_create_deployed_code_valid

"$ZISKEMU" -e gen-out/zisk_create_deployed_code_valid.elf \
  -o gen-out/zisk_create_deployed_code_valid.out -n 2000000 >/dev/null 2>&1 || true

python3 - <<'PY'
import struct, sys
d = open('gen-out/zisk_create_deployed_code_valid.out', 'rb').read()
vals = [struct.unpack('<Q', d[i:i+8])[0] for i in range(0, 40, 8)]
labels = ['empty(len 0)','{0x60}(len 1)','{0xEF}(len 1)','{0x60}(len 32768)','{0x60}(len 32769)']
exp = [0, 0, 1, 0, 1]
ok = True
for l, v, e in zip(labels, vals, exp):
    status = 'OK' if v == e else 'FAIL'
    if v != e: ok = False
    print(f"  {status:4} {l:20} got={v} exp={e}")
if not ok:
    print("==> FAIL"); sys.exit(1)
print("==> PASS: create_deployed_code_valid (EIP-3541 + EIP-170)")
PY
