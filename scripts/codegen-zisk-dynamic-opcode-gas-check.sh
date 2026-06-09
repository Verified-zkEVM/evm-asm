#!/usr/bin/env bash
# codegen-zisk-dynamic-opcode-gas-check.sh -- bead nxio8.3.
# keccak256_word_gas=30+6*words; copy_word_gas=3*words; log_data_gas=375+375*topics+8*bytes.
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
run_case() { # name ksize csize topics lbytes ek ec el
  local name="$1"
  K="$2" C="$3" T="$4" L="$5" python3 -c "
import struct,sys,os
open(sys.argv[1],'wb').write(struct.pack('<QQQQ',int(os.environ['K']),int(os.environ['C']),int(os.environ['T']),int(os.environ['L'])))
" "$REPO_ROOT/gen-out/zisk_dog_${name}.in"
  "$ZISKEMU" -e gen-out/zisk_dynamic_opcode_gas.elf -i "$REPO_ROOT/gen-out/zisk_dog_${name}.in" -o "$REPO_ROOT/gen-out/zisk_dog_${name}.out" -n 2000000 >/dev/null 2>&1 || true
  read gk gc gl < <(python3 -c "
d=open('$REPO_ROOT/gen-out/zisk_dog_${name}.out','rb').read();import struct
print(*[struct.unpack('<Q',d[i*8:i*8+8])[0] for i in range(3)])")
  if [[ "$gk" == "$6" && "$gc" == "$7" && "$gl" == "$8" ]]; then printf "  %-12s OK   keccak=%s copy=%s log=%s\n" "$name" "$gk" "$gc" "$gl"
  else printf "  %-12s FAIL keccak=%s/%s copy=%s/%s log=%s/%s\n" "$name" "$gk" "$6" "$gc" "$7" "$gl" "$8"; FAILED=1; fi
}
#         name      ksize csize topics lbytes  e_keccak e_copy e_log
run_case typical     64   100   3      10      42       12     1580
run_case zeros       0    0     0      0       30       0      375
run_case word_edge   32   32    1      0       36       3      750
run_case big         1024 1024  4      256     222      96     3923
echo
if [[ $FAILED -eq 0 ]]; then echo "==> PASS: dynamic per-unit opcode gas matches Amsterdam"; exit 0; else echo "==> FAIL"; exit 1; fi
