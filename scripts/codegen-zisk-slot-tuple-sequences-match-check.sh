#!/usr/bin/env bash
# codegen-zisk-slot-tuple-sequences-match-check.sh -- bead bmvmx.1.6.6 (per-slot comparator).
#
# slot_tuple_sequences_match compares a BAL slot tuple sequence (bal_slot_tuple_sequence #8593)
# against the exec-reconstructed sequence (exec_log_slot_tuples #8595), as two arrays of 40-byte
# records [block_access_index u64 | value 32B]. Status: 0 identical / 1 mismatch.
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

echo "==> emit zisk_slot_tuple_sequences_match ELF"
lake exe codegen --program zisk_slot_tuple_sequences_match --halt linux93 \
  -o gen-out/zisk_slot_tuple_sequences_match

REPO_ROOT="$(pwd)"

# run_case <name> <bal "tx:val,..."> <exec "tx:val,..."> <exp_status>
run_case() {
  local name="$1" bal="$2" exec="$3" exp="$4"
  local in_file="$REPO_ROOT/gen-out/zisk_stsm_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_stsm_${name}.output"

  BAL="$bal" EXC="$exec" uv run --directory execution-specs --quiet python3 -c "
import struct, sys, os
def seq(s):
    out=b''
    if s:
        for p in s.split(','):
            tx,val=p.split(':')
            out+=struct.pack('<Q', int(tx,0)) + int(val,0).to_bytes(32,'big')
    return out
bal=seq(os.environ['BAL']); exc=seq(os.environ['EXC'])
bc=len(bal)//40; ec=len(exc)//40
with open(sys.argv[1],'wb') as f:
    f.write(struct.pack('<Q', bc))   # BAL tuple count
    f.write(struct.pack('<Q', ec))   # exec tuple count
    f.write(bal); f.write(exc)
    pad=(-(16+len(bal)+len(exc)))%8
    if pad: f.write(b'\x00'*pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_slot_tuple_sequences_match.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_stsm_${name}.emu.log" 2>&1 || true

  local st
  st=$(python3 -c "d=open('$out_file','rb').read(); print(int.from_bytes(d[0:8],'little'))")
  if [[ "$st" == "$exp" ]]; then
    printf "  %-16s OK   status=%s\n" "$name" "$st"; return 0
  fi
  printf "  %-16s FAIL status=%s expected=%s\n" "$name" "$st" "$exp"; return 1
}

FAILED=0
run_case "match"          "1:0x11,3:0x33" "1:0x11,3:0x33" 0 || FAILED=1
run_case "value_mismatch" "1:0x11"        "1:0x22"        1 || FAILED=1
run_case "index_mismatch" "1:0x11"        "2:0x11"        1 || FAILED=1
run_case "count_mismatch" "1:0x11,3:0x33" "1:0x11"        1 || FAILED=1
run_case "both_empty"     ""              ""              0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: slot_tuple_sequences_match exact list-vs-list tuple-sequence comparison"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
