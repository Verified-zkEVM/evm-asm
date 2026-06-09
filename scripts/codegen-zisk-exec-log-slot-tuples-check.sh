#!/usr/bin/env bash
# codegen-zisk-exec-log-slot-tuples-check.sh -- bead bmvmx.1.6.9.
#
# exec_log_slot_tuples reconstructs a slot's per-tx net-change (block_access_index, new_value)
# tuple sequence from the append-per-write storage exec-log + the parallel exec_log_txindex
# array: group matching entries by txindex (last-write-per-tx), emit a tuple per tx whose
# end-of-tx value differs from the running value (net-zero-per-tx filtered).
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

echo "==> emit zisk_exec_log_slot_tuples ELF"
lake exe codegen --program zisk_exec_log_slot_tuples --halt linux93 \
  -o gen-out/zisk_exec_log_slot_tuples

REPO_ROOT="$(pwd)"

# run_case <name> <mode> <expected "tx:val,tx:val" | "">
run_case() {
  local name="$1" mode="$2" expect="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_elst_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_elst_${name}.output"

  MODE="$mode" uv run --directory execution-specs --quiet python3 -c "
import struct, sys, os
mode=os.environ['MODE']
def b32(n): return n.to_bytes(32,'big')
A=b32(0xAA); B=b32(0xBB); K=b32(7); O=b32(0)
def entry(ah,sk,orig,cur): return ah+sk+orig+cur   # 128 bytes
# (entry, txindex) lists per mode
if mode=='two_changes':
    rows=[(entry(A,K,O,b32(0x11)),1),(entry(B,K,O,b32(0x55)),1),(entry(A,K,O,b32(0x33)),3)]
elif mode=='within_tx_netzero':
    rows=[(entry(A,K,O,b32(0x11)),1),(entry(A,K,O,O),1)]              # tx1 writes V then back to O
elif mode=='cross_tx_back':
    rows=[(entry(A,K,O,b32(0x11)),1),(entry(A,K,O,O),2)]             # tx2 reverts to original
elif mode=='not_present':
    rows=[(entry(B,K,O,b32(0x11)),1),(entry(A,b32(9),O,b32(0x22)),1)] # wrong account / wrong slot
count=len(rows)
txidx=b''.join(struct.pack('<Q',t) for (_,t) in rows)
log=b''.join(e for (e,_) in rows)
with open(sys.argv[1],'wb') as f:
    f.write(struct.pack('<Q', count))   # entry count
    f.write(A)                          # query addrHash (32B)
    f.write(K)                          # query slotKey (32B)
    f.write(txidx)                      # txindex array (count*8)
    f.write(log)                        # exec-log (count*128)
    total=8+32+32+len(txidx)+len(log)
    pad=(-total)%8
    if pad: f.write(b'\x00'*pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_exec_log_slot_tuples.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_elst_${name}.emu.log" 2>&1 || true

  local got
  got=$(python3 -c "
d=open('$out_file','rb').read()
cnt=int.from_bytes(d[0:8],'little')
out=[]
for j in range(cnt):
    base=8+j*40
    tx=int.from_bytes(d[base:base+8],'little')
    val=int.from_bytes(d[base+8:base+40],'big')
    out.append('%d:%d'%(tx,val))
print(','.join(out))
")
  local norm
  norm=$(EXP="$expect" python3 -c "
import os
e=os.environ['EXP']
print('' if not e else ','.join('%d:%d'%(int(p.split(':')[0],0),int(p.split(':')[1],0)) for p in e.split(',')))
")
  if [[ "$got" == "$norm" ]]; then
    printf "  %-18s OK   [%s]\n" "$name" "$got"; return 0
  fi
  printf "  %-18s FAIL got=[%s] expected=[%s]\n" "$name" "$got" "$norm"; return 1
}

FAILED=0
run_case "two_changes"       two_changes       "1:0x11,3:0x33" || FAILED=1
run_case "within_tx_netzero" within_tx_netzero ""              || FAILED=1
run_case "cross_tx_back"     cross_tx_back     "1:0x11,2:0"    || FAILED=1
run_case "not_present"       not_present       ""              || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: exec_log_slot_tuples reconstructs the per-tx net-change tuple sequence"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
