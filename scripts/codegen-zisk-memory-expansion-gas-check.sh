#!/usr/bin/env bash
# codegen-zisk-memory-expansion-gas-check.sh -- bead nxio8.2.
# memory_expansion_gas: cost(b)=words*3+words^2//512, words=(b+31)//32; charge=cost(new)-cost(old).
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
echo "==> emit zisk_memory_expansion_gas"; lake exe codegen --program zisk_memory_expansion_gas --halt linux93 -o gen-out/zisk_memory_expansion_gas
REPO_ROOT="$(pwd)"; FAILED=0
run_case() {
  local name="$1" old="$2" new="$3" expect="$4"
  local in_file="$REPO_ROOT/gen-out/zisk_meg_${name}.input" out_file="$REPO_ROOT/gen-out/zisk_meg_${name}.output"
  OLD="$old" NEW="$new" python3 -c "
import struct,sys,os
open(sys.argv[1],'wb').write(struct.pack('<QQ',int(os.environ['OLD']),int(os.environ['NEW'])))
" "$in_file"
  "$ZISKEMU" -e gen-out/zisk_memory_expansion_gas.elf -i "$in_file" -o "$out_file" -n 2000000 >"$REPO_ROOT/gen-out/zisk_meg_${name}.emu.log" 2>&1 || true
  local got; got=$(python3 -c "print(int.from_bytes(open('$out_file','rb').read()[0:8],'little'))")
  if [[ "$got" == "$expect" ]]; then printf "  %-14s OK   gas=%s\n" "$name" "$got"; else printf "  %-14s FAIL got=%s expected=%s\n" "$name" "$got" "$expect"; FAILED=1; fi
}
run_case zero_to_32   0 32 3
run_case zero_to_1024 0 1024 98
run_case w32_to_64    32 64 3
run_case no_growth    1024 1024 0
run_case shrink       1024 64 0
run_case zero_to_96   0 96 9
echo
if [[ $FAILED -eq 0 ]]; then echo "==> PASS: memory_expansion_gas matches Amsterdam memory gas"; exit 0; else echo "==> FAIL"; exit 1; fi
