#!/usr/bin/env bash
# codegen-zisk-create2-descend-check.sh -- bead fhsxz.2.4.2.61.8.1 (CREATE2 slice).
#
# Checks create2_descend: the CREATE2 (0xf5) handler logic over the inline init-code
# machinery. From a synthetic stack (value,offset,length,salt) + init code in memory +
# env.ADDRESS sender, it computes the CREATE2 address, runs the bounded mini-interpreter
# (init code deploys 1 byte), and pushes the new address. Known-answer: the pushed
# address (LE stack word) must equal the LE-reversed result of a DIRECT
# address_compute_create2 over the same (sender, salt-BE, init code), and status==2.
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
echo "==> emit zisk_create2_descend ELF"
lake exe codegen --program zisk_create2_descend --halt linux93 -o gen-out/zisk_create2_descend
: > gen-out/zisk_create2_descend.input
"$ZISKEMU" -e gen-out/zisk_create2_descend.elf \
  -i gen-out/zisk_create2_descend.input -o gen-out/zisk_create2_descend.output -n 100000000 \
  >gen-out/zisk_create2_descend.emu.log 2>&1
python3 - <<'PY'
import struct, sys
data = open('gen-out/zisk_create2_descend.output', 'rb').read()
def u64(o): return struct.unpack('<Q', data[o:o+8])[0] if o+8 <= len(data) else None
status, pushed, expected, match = u64(0), u64(8), u64(16), u64(24)
ok = (status == 2) and (pushed == expected) and (match == 1)
print(f"  status={status} (exp 2)  pushed={hex(pushed)}  expected-LE={hex(expected)}  match={match} (exp 1)")
sys.exit(0 if ok else 1)
PY
echo
echo "==> PASS: create2_descend computes the CREATE2 address, deploys via the mini-interp, pushes it"
