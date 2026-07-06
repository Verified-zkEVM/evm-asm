#!/usr/bin/env bash
# codegen-zisk-create-descend-check.sh -- bead fhsxz.2.4.2.61.8.1 (CREATE 0xf0 slice).
# Checks create_descend: CREATE (0xf0) handler logic. From a synthetic stack
# (value,offset,length) + init code + env.ADDRESS sender + create_nonce, computes the
# address (keccak(rlp([sender,nonce]))[12:]), runs the bounded mini-interp, pushes the
# new address. Known-answer: pushed (LE) == LE-reverse of a DIRECT address_compute_create,
# status==2.
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
echo "==> emit zisk_create_descend ELF"
lake exe codegen --program zisk_create_descend --halt linux93 -o gen-out/zisk_create_descend
: > gen-out/zisk_create_descend.input
"$ZISKEMU" -e gen-out/zisk_create_descend.elf \
  -i gen-out/zisk_create_descend.input -o gen-out/zisk_create_descend.output -n 100000000 \
  >gen-out/zisk_create_descend.emu.log 2>&1
python3 - <<'PY'
import struct, sys
d = open('gen-out/zisk_create_descend.output', 'rb').read()
def u(o): return struct.unpack('<Q', d[o:o+8])[0] if o+8 <= len(d) else None
status, pushed, expected, match = u(0), u(8), u(16), u(24)
ok = (status == 2) and (pushed == expected) and (match == 1)
print(f"  status={status} (exp 2)  pushed={hex(pushed)}  expected-LE={hex(expected)}  match={match} (exp 1)")
sys.exit(0 if ok else 1)
PY
echo; echo "==> PASS: create_descend computes the CREATE address (sender,nonce), deploys, pushes it"
