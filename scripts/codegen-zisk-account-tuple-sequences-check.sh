#!/usr/bin/env bash
# codegen-zisk-account-tuple-sequences-check.sh -- bead bmvmx.1.6.6 (per-account all-slots wrapper).
#
# account_tuple_sequences_consistent iterates an account's storage_changes slots and, per slot,
# compares the BAL-declared per-tx (block_access_index,new_value) tuple sequence (bal_slot_tuple_sequence
# #8593) against the exec-reconstructed sequence (exec_log_slot_tuples #8595) via slot_tuple_sequences_match
# (#8596). Status: 0 every slot matches / 1 mismatch. This is the integration that closes the Q5
# finals-only false-accept gap (wrong/extra/missing intermediate tuples).
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

echo "==> emit zisk_account_tuple_sequences_consistent ELF"
lake exe codegen --program zisk_account_tuple_sequences_consistent --halt linux93 \
  -o gen-out/zisk_account_tuple_sequences_consistent

REPO_ROOT="$(pwd)"

# run_case <name> <mode> <exp_status>
run_case() {
  local name="$1" mode="$2" exp="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_ats_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_ats_${name}.output"

  MODE="$mode" uv run --directory execution-specs --quiet python3 -c "
import struct, sys, os, rlp
mode=os.environ['MODE']
def b32(n): return n.to_bytes(32,'big')        # BAL (RLP) keys/values = big-endian
def b32le(n): return n.to_bytes(32,'little')   # exec-log slotKey/value = LE EVM-stack limbs (Storage.lean:19)
addr=bytes(range(1,21)); addrHash=bytes([0xAA])*32
O=b32le(0)
# exec-log entries store slotKey + value in the real guest's LITTLE-endian stack-word order.
def entry(sk_n,cur_n): return addrHash+b32le(sk_n)+O+b32le(cur_n)   # 128B: addrHash|slotKey|original|current

# exec-log for slot 7: tx1 -> 0x11, tx3 -> 0x33  => reconstructs [(1,0x11),(3,0x33)]
rows=[(entry(7,0x11),1),(entry(7,0x33),3)]
# BAL storage_changes for slot 7 (SlotChanges = [slot_key, [[bai,new_value],...]]), big-endian.
sc=[[b32(7), [[1,b32(0x11)],[3,b32(0x33)]]]]

if mode=='wrong_tuple':
    sc=[[b32(7), [[1,b32(0x11)],[3,b32(0x99)]]]]            # final tuple value wrong vs exec 0x33
elif mode=='extra_bal_tuple':
    sc=[[b32(7), [[1,b32(0x11)],[3,b32(0x33)],[5,b32(0x55)]]]]  # spurious extra tuple BAL has, exec doesn't
elif mode=='multi_slot':
    rows=rows+[(entry(9,0x22),2)]                 # exec slot 9: tx2 -> 0x22
    sc=sc+[[b32(9), [[2,b32(0x22)]]]]

acct=rlp.encode([addr, sc, [], [], [], []])
count=len(rows)
txidx=b''.join(struct.pack('<Q',t) for (_,t) in rows)
log=b''.join(e for (e,_) in rows)
with open(sys.argv[1],'wb') as f:
    f.write(struct.pack('<Q', len(acct)))   # AccountChanges len
    f.write(addrHash)                        # addrHash (32B)
    f.write(struct.pack('<Q', count))        # exec-log entry count
    f.write(txidx)                           # txindex array (count*8)
    f.write(log)                             # exec-log (count*128)
    f.write(acct)                            # AccountChanges RLP
    total=8+32+8+len(txidx)+len(log)+len(acct)
    pad=(-total)%8
    if pad: f.write(b'\x00'*pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_account_tuple_sequences_consistent.elf \
    -i "$in_file" -o "$out_file" -n 8000000 \
    >"$REPO_ROOT/gen-out/zisk_ats_${name}.emu.log" 2>&1 || true

  local st
  st=$(python3 -c "d=open('$out_file','rb').read(); print(int.from_bytes(d[0:8],'little'))")
  if [[ "$st" == "$exp" ]]; then
    printf "  %-16s OK   status=%s\n" "$name" "$st"; return 0
  fi
  printf "  %-16s FAIL status=%s expected=%s\n" "$name" "$st" "$exp"; return 1
}

FAILED=0
# BAL tuple sequence equals exec reconstruction for the slot -> consistent.
run_case "consistent"      consistent      0 || FAILED=1
# BAL declares a wrong intermediate/final tuple value (the Q5 gap) -> mismatch.
run_case "wrong_tuple"     wrong_tuple     1 || FAILED=1
# BAL declares an extra spurious tuple exec didn't produce -> count mismatch.
run_case "extra_bal_tuple" extra_bal_tuple 1 || FAILED=1
# two slots, both BAL sequences match exec -> consistent.
run_case "multi_slot"      multi_slot      0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_tuple_sequences_consistent per-account all-slots tuple-sequence check"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
