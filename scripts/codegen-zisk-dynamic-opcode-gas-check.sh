#!/usr/bin/env bash
# codegen-zisk-dynamic-opcode-gas-check.sh -- bead nxio8.3.
# keccak256=30+6*words; copy=3*words; log=375+375*topics+8*bytes; exp=10+50*exponent_bytes.
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
echo "==> emit zisk_dynamic_opcode_gas"; lake exe codegen --program zisk_dynamic_opcode_gas --halt linux93 -o gen-out/zisk_dynamic_opcode_gas
REPO_ROOT="$(pwd)"; FAILED=0
run_case() { # name ksize csize topics lbytes exp_int  ek ec el ee
  local name="$1"
  K="$2" C="$3" T="$4" L="$5" E="$6" python3 -c "
import struct,sys,os
b=open(sys.argv[1],'wb')
b.write(struct.pack('<QQQQ',int(os.environ['K']),int(os.environ['C']),int(os.environ['T']),int(os.environ['L'])))
b.write(int(os.environ['E']).to_bytes(32,'big')); b.close()
" "$REPO_ROOT/gen-out/zisk_dog_${name}.in"
  "$ZISKEMU" -e gen-out/zisk_dynamic_opcode_gas.elf -i "$REPO_ROOT/gen-out/zisk_dog_${name}.in" -o "$REPO_ROOT/gen-out/zisk_dog_${name}.out" -n 2000000 >/dev/null 2>&1 || true
  read gk gc gl ge < <(python3 -c "
d=open('$REPO_ROOT/gen-out/zisk_dog_${name}.out','rb').read();import struct
print(*[struct.unpack('<Q',d[i*8:i*8+8])[0] for i in range(4)])")
  if [[ "$gk" == "$7" && "$gc" == "$8" && "$gl" == "$9" && "$ge" == "${10}" ]]; then
    printf "  %-12s OK   keccak=%s copy=%s log=%s exp=%s\n" "$name" "$gk" "$gc" "$gl" "$ge"
  else printf "  %-12s FAIL keccak=%s/%s copy=%s/%s log=%s/%s exp=%s/%s\n" "$name" "$gk" "$7" "$gc" "$8" "$gl" "$9" "$ge" "${10}"; FAILED=1; fi
}
#         name      ks   cs   tp lb  exp                 ek  ec el   ee
run_case typical     64   100  3  10  255                42  12 1580 60
run_case zeros       0    0    0  0   0                   30  0  375  10
run_case word_edge   32   32   1  0   256                 36  3  750  110
run_case big         1024 1024 4  256 57896044618658097711785492504343953926634992332820282019728792003956564819968  222 96 3923 1610
echo
if [[ $FAILED -eq 0 ]]; then echo "==> PASS: dynamic per-unit opcode gas (keccak/copy/log/exp) matches Amsterdam"; exit 0; else echo "==> FAIL"; exit 1; fi
