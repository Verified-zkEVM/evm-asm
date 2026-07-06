#!/usr/bin/env bash
# codegen-zisk-exec-log-latest-value-check.sh -- bead fhsxz.2.4.2.57.11.6.3.1.
#
# exec_log_latest_value scans the append-per-write storage exec-log (128B entries
# addrHash@0/slotKey@32/original@64/current@96) for the entries matching a query
# (addrHash, slotKey) and returns the LAST match's `current` value (the slot's
# latest committed value) with a found flag; foundation for cross-tx storage
# threading (snapshot tx[i]'s committed writes to thread into tx[i+1]'s preload).
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

echo "==> emit zisk_exec_log_latest_value ELF"
lake exe codegen --program zisk_exec_log_latest_value --halt linux93 \
  -o gen-out/zisk_exec_log_latest_value

REPO_ROOT="$(pwd)"

# run_case <name> <mode> <expected "found:value" | "0:">
run_case() {
  local name="$1" mode="$2" expect="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_ellv_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_ellv_${name}.output"

  MODE="$mode" python3 -c "
import struct, sys, os
mode=os.environ['MODE']
def b32(n): return n.to_bytes(32,'big')
A=b32(0xAA); B=b32(0xBB); K=b32(7); O=b32(0)
def entry(ah,sk,orig,cur): return ah+sk+orig+cur   # 128 bytes
if mode=='single_write':
    rows=[entry(A,K,O,b32(0x11))]
elif mode=='last_of_two':
    rows=[entry(A,K,O,b32(0x11)),entry(A,K,b32(0x11),b32(0x33))]      # same slot, two writes
elif mode=='skip_other':
    rows=[entry(A,K,O,b32(0x11)),entry(B,K,O,b32(0x55)),entry(A,K,b32(0x11),b32(0x33))]
elif mode=='not_present':
    rows=[entry(B,K,O,b32(0x11)),entry(A,b32(9),O,b32(0x22))]         # wrong account / wrong slot
count=len(rows)
log=b''.join(rows)
with open(sys.argv[1],'wb') as f:
    f.write(struct.pack('<Q', count))   # entry count
    f.write(A)                          # query addrHash (32B)
    f.write(K)                          # query slotKey (32B)
    f.write(log)                        # exec-log (count*128)
    total=8+32+32+len(log)
    pad=(-total)%8
    if pad: f.write(b'\x00'*pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_exec_log_latest_value.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_ellv_${name}.emu.log" 2>&1 || true

  local got
  got=$(python3 -c "
d=open('$out_file','rb').read()
found=int.from_bytes(d[0:8],'little')
val=int.from_bytes(d[8:40],'big') if found else 0
print('%d:%d'%(found,val) if found else '0:')
")
  local norm
  norm=$(EXP="$expect" python3 -c "
import os
e=os.environ['EXP']
if e.startswith('0:') :
    print('0:')
else:
    f,v=e.split(':'); print('%d:%d'%(int(f,0),int(v,0)))
")
  if [[ "$got" == "$norm" ]]; then
    printf "  %-16s OK   [%s]\n" "$name" "$got"; return 0
  fi
  printf "  %-16s FAIL got=[%s] expected=[%s]\n" "$name" "$got" "$norm"; return 1
}

FAILED=0
run_case "single_write" single_write "1:0x11"  || FAILED=1
run_case "last_of_two"  last_of_two  "1:0x33"  || FAILED=1
run_case "skip_other"   skip_other   "1:0x33"  || FAILED=1
run_case "not_present"  not_present  "0:"      || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: exec_log_latest_value returns the latest committed current value (with found flag)"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
