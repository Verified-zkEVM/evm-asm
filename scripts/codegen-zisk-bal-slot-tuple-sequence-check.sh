#!/usr/bin/env bash
# codegen-zisk-bal-slot-tuple-sequence-check.sh -- bead bmvmx.1.6.8.
#
# bal_slot_tuple_sequence extracts a target slot's FULL per-tx (block_access_index, new_value)
# tuple sequence from a BAL AccountChanges' storage_changes (the BAL side of the bmvmx.1.6.6
# tuple-sequence comparator). Returns the tuple count; writes count x 40-byte records
# [bai u64 | value 32B BE].
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

echo "==> emit zisk_bal_slot_tuple_sequence ELF"
lake exe codegen --program zisk_bal_slot_tuple_sequence --halt linux93 \
  -o gen-out/zisk_bal_slot_tuple_sequence

REPO_ROOT="$(pwd)"

# run_case <name> <target_slot_int> <expected_pairs "bai:val,bai:val" | "">
run_case() {
  local name="$1" slot="$2" expect="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_bts_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_bts_${name}.output"

  SLOT="$slot" uv run --directory execution-specs --quiet python3 -c "
import struct, sys, os, rlp
slot=int(os.environ['SLOT'])
addr=bytes(range(1,21))
def k(n): return n.to_bytes(32,'big')
storage_changes = [
  [k(7), [[1, k(0x11)], [3, k(0x22)], [5, k(0x33)]]],   # target with 3 tuples
  [k(9), [[2, k(0x99)]]],                               # another slot, 1 tuple
]
acct = rlp.encode([addr, storage_changes, [], [], [], []])
with open(sys.argv[1],'wb') as f:
    f.write(struct.pack('<Q', len(acct)))   # AccountChanges len
    f.write(k(slot))                        # target slot key (32B)
    f.write(acct)                           # AccountChanges RLP
    pad=(-(8+32+len(acct)))%8
    if pad: f.write(b'\x00'*pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_bal_slot_tuple_sequence.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_bts_${name}.emu.log" 2>&1 || true

  local got
  got=$(EXPECT="$expect" python3 -c "
import os
d=open('$out_file','rb').read()
cnt=int.from_bytes(d[0:8],'little')
pairs=[]
for j in range(cnt):
    base=8+j*40
    bai=int.from_bytes(d[base:base+8],'little')
    val=int.from_bytes(d[base+8:base+40],'big')
    pairs.append('%d:%d'%(bai,val))
print(','.join(pairs))
")
  # normalise expected (decimal vals)
  local norm
  norm=$(EXP="$expect" python3 -c "
import os
e=os.environ['EXP']
if not e: print(''); raise SystemExit
out=[]
for p in e.split(','):
    b,v=p.split(':'); out.append('%d:%d'%(int(b,0),int(v,0)))
print(','.join(out))
")
  if [[ "$got" == "$norm" ]]; then
    printf "  %-14s OK   [%s]\n" "$name" "$got"; return 0
  fi
  printf "  %-14s FAIL got=[%s] expected=[%s]\n" "$name" "$got" "$norm"; return 1
}

FAILED=0
run_case "three"     7  "1:0x11,3:0x22,5:0x33" || FAILED=1
run_case "one"       9  "2:0x99"               || FAILED=1
run_case "not_found" 85 ""                     || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: bal_slot_tuple_sequence extracts the full per-slot (bai,value) tuple sequence"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
