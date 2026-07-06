#!/usr/bin/env bash
# codegen-zisk-sstore-regular-gas-check.sh -- bead nxio8.1.
#
# sstore_regular_gas computes the exact Amsterdam SSTORE *regular* gas cost
# (EIP-7778 block_regular component): gas = (cold?2100:0) + (original==current &&
# current!=new ? 2900 : 100). Verifies the four spec cases (execution-specs
# amsterdam vm/instructions/storage.py + vm/gas.py).
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2; exit 1; fi
fi

mkdir -p gen-out
echo "==> lake build codegen"
lake build codegen
echo "==> emit zisk_sstore_regular_gas ELF"
lake exe codegen --program zisk_sstore_regular_gas --halt linux93 -o gen-out/zisk_sstore_regular_gas

REPO_ROOT="$(pwd)"
FAILED=0
run_case() {
  local name="$1" is_cold="$2" orig="$3" cur="$4" new="$5" expect="$6"
  local in_file="$REPO_ROOT/gen-out/zisk_srg_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_srg_${name}.output"
  COLD="$is_cold" O="$orig" C="$cur" N="$new" python3 -c "
import struct, sys, os
def b32(n): return int(n,0).to_bytes(32,'big')
with open(sys.argv[1],'wb') as f:
    f.write(struct.pack('<Q', int(os.environ['COLD'])))
    f.write(b32(os.environ['O'])); f.write(b32(os.environ['C'])); f.write(b32(os.environ['N']))
    tot=8+96; pad=(-tot)%8
    if pad: f.write(b'\x00'*pad)
" "$in_file"
  "$ZISKEMU" -e gen-out/zisk_sstore_regular_gas.elf -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_srg_${name}.emu.log" 2>&1 || true
  local got
  got=$(python3 -c "print(int.from_bytes(open('$out_file','rb').read()[0:8],'little'))")
  if [[ "$got" == "$expect" ]]; then
    printf "  %-20s OK   gas=%s\n" "$name" "$got"
  else
    printf "  %-20s FAIL got=%s expected=%s\n" "$name" "$got" "$expect"; FAILED=1
  fi
}

run_case cold_clean_change   1 0x5 0x5 0x7 5000
run_case cold_else_orig_ne   1 0x3 0x5 0x7 2200
run_case cold_else_nochange  1 0x5 0x7 0x7 2200
run_case warm_clean_change   0 0x5 0x5 0x7 2900
run_case warm_else_nochange  0 0x5 0x7 0x7 100
run_case warm_else_dirty     0 0x3 0x5 0x7 100

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: sstore_regular_gas matches Amsterdam SSTORE regular gas"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
