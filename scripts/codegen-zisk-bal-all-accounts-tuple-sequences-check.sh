#!/usr/bin/env bash
# codegen-zisk-bal-all-accounts-tuple-sequences-check.sh -- bead bmvmx.1.6.6 (all-accounts tuple wrapper).
#
# bal_all_accounts_tuple_sequences_consistent runs account_tuple_sequences_consistent (#8602) over every
# block_access_list account: SKIP the recipient (BE-keyed storage checked in block_verdict), derive each
# callee's LE exec-log key via bal_addr_to_exec_log_key (#8575), and compare per-slot BAL tuple sequences
# vs the exec reconstruction. Status: 0 consistent / 1 mismatch.
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

echo "==> emit zisk_bal_all_accounts_tuple_sequences_consistent ELF"
lake exe codegen --program zisk_bal_all_accounts_tuple_sequences_consistent --halt linux93 \
  -o gen-out/zisk_bal_all_accounts_tuple_sequences_consistent

REPO_ROOT="$(pwd)"

# run_case <name> <mode> <exp_status>
run_case() {
  local name="$1" mode="$2" exp="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_bats_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_bats_${name}.output"

  MODE="$mode" uv run --directory execution-specs --quiet python3 -c "
import struct, sys, os, rlp
mode=os.environ['MODE']
def b32(n): return n.to_bytes(32,'big')        # BAL (RLP) keys/values = big-endian
def b32le(n): return n.to_bytes(32,'little')   # exec-log slotKey/value = LE stack-word (Storage.lean:19)
callee=bytes(range(1,21)); recipient=bytes(range(0x21,0x35))
ckey=callee[::-1]+b'\x00'*12          # bal_addr_to_exec_log_key(callee): addr reversed, low-aligned
K=b32(7); O=b32le(0)
# exec-log entries store slotKey + value in the real little-endian stack-word order.
def entry(ah,sk_n,cur_n,o=O): return ah+b32le(sk_n)+o+b32le(cur_n)  # 128B addrHash|slotKey|original|current

# exec-log for callee's slot 7: tx1 -> 0x11, tx3 -> 0x33  => reconstructs [(1,0x11),(3,0x33)]
rows=[(entry(ckey,7,0x11),1),(entry(ckey,7,0x33),3)]
callee_sc=[[K, [[1,b32(0x11)],[3,b32(0x33)]]]]
recip_sc =[[K, [[1,b32(0xDEAD)],[2,b32(0xBEEF)]]]]   # recipient storage (BE-keyed; must be SKIPPED)
accounts=[[callee, callee_sc, [], [], [], []], [recipient, recip_sc, [], [], [], []]]

if mode=='wrong_tuple':
    callee_sc=[[K, [[1,b32(0x11)],[3,b32(0x99)]]]]    # final tuple value wrong vs exec 0x33
    accounts=[[callee, callee_sc, [], [], [], []], [recipient, recip_sc, [], [], [], []]]
elif mode=='recipient_only':
    rows=[]                                            # no exec entries
    accounts=[[recipient, recip_sc, [], [], [], []]]   # only the recipient -> skipped -> OK

count=len(rows)
txidx=b''.join(struct.pack('<Q',t) for (_,t) in rows)
log=b''.join(e for (e,_) in rows)
bal=rlp.encode(accounts)
with open(sys.argv[1],'wb') as f:
    f.write(struct.pack('<Q', len(bal)))     # BAL section len
    f.write(struct.pack('<Q', count))        # exec-log entry count
    f.write(recipient.ljust(32, b'\x00'))    # recipient (20B padded to 32)
    f.write(txidx)                           # txindex array
    f.write(log)                             # exec-log
    f.write(bal)                             # BAL section
    total=8+8+32+len(txidx)+len(log)+len(bal)
    pad=(-total)%8
    if pad: f.write(b'\x00'*pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_bal_all_accounts_tuple_sequences_consistent.elf \
    -i "$in_file" -o "$out_file" -n 9000000 \
    >"$REPO_ROOT/gen-out/zisk_bats_${name}.emu.log" 2>&1 || true

  local st
  st=$(python3 -c "d=open('$out_file','rb').read(); print(int.from_bytes(d[0:8],'little'))")
  if [[ "$st" == "$exp" ]]; then
    printf "  %-16s OK   status=%s\n" "$name" "$st"; return 0
  fi
  printf "  %-16s FAIL status=%s expected=%s\n" "$name" "$st" "$exp"; return 1
}

FAILED=0
# callee's per-slot BAL tuple sequence matches exec; recipient (BE-keyed storage) skipped -> consistent.
run_case "consistent"     consistent     0 || FAILED=1
# callee declares a wrong tuple value -> mismatch (the Q5 gap, at the all-accounts level).
run_case "wrong_tuple"    wrong_tuple    1 || FAILED=1
# only the recipient present (with storage the LE exec-log can't match) -> skipped -> OK (proves recipient skip).
run_case "recipient_only" recipient_only 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: bal_all_accounts_tuple_sequences_consistent all-accounts per-tx tuple-sequence check"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
