#!/usr/bin/env bash
# codegen-zisk-bal-account-nonstorage-consistent-check.sh -- bead i3djw (bmvmx.1.6.4.4 step .2).
#
# bal_account_nonstorage_consistent checks a BAL AccountChanges' FINAL balance/nonce
# (parsed by bal_account_nonstorage_finals, step .1) against an execution-derived
# non-storage effect record for the same account, in both directions:
#   forward: BAL-declared final == exec block-post value;
#   reverse: exec net-change (block-post != block-pre) => BAL declares it.
# Status: 0 consistent / 1 inconsistent / 2 BAL parse failure.
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

echo "==> emit zisk_bal_account_nonstorage_consistent ELF"
lake exe codegen --program zisk_bal_account_nonstorage_consistent --halt linux93 \
  -o gen-out/zisk_bal_account_nonstorage_consistent

REPO_ROOT="$(pwd)"

# run_case <name> <bal_mode> <pre_bal> <post_bal> <pre_nonce> <post_nonce> <exp_status>
#   bal_mode controls what the BAL AccountChanges declares (final balance/nonce):
#     match     -> balance_changes final = $post_bal, nonce_changes final = $post_nonce
#     no_balance-> balance_changes empty (nonce still declared = $post_nonce)
#     no_nonce  -> nonce_changes empty (balance still declared = $post_bal)
#     wrong_bal -> balance_changes final = $post_bal + 1 (wrong final)
#     wrong_nonce-> nonce_changes final = $post_nonce + 1 (wrong final)
run_case() {
  local name="$1" bmode="$2" preb="$3" postb="$4" pren="$5" postn="$6" exp="$7"
  local in_file="$REPO_ROOT/gen-out/zisk_nsc_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_nsc_${name}.output"

  BMODE="$bmode" PREB="$preb" POSTB="$postb" PREN="$pren" POSTN="$postn" \
  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, os, rlp
bmode=os.environ['BMODE']
preb=int(os.environ['PREB']);  postb=int(os.environ['POSTB'])
pren=int(os.environ['PREN']);  postn=int(os.environ['POSTN'])
addr=bytes(range(1,21))
# BAL final declarations: a 2-tuple list whose LAST tuple is the declared final.
bal_balance = postb
bal_nonce   = postn
balance_changes = [[1, bal_balance//2 if bal_balance else 0], [3, bal_balance]]
nonce_changes   = [[1, max(bal_nonce-1,0)], [2, bal_nonce]]
if bmode=='no_balance':  balance_changes=[]
if bmode=='no_nonce':    nonce_changes=[]
if bmode=='wrong_bal':   balance_changes=[[1,0],[3, postb+1]]
if bmode=='wrong_nonce': nonce_changes=[[1,0],[2, postn+1]]
acct=rlp.encode([addr, [], [], balance_changes, nonce_changes, []])
# exec non-storage effect record: 32 addrHash | 32 pre_bal BE | 32 post_bal BE | u64 pre_n | u64 post_n
eff =bytes(32)
eff+=preb.to_bytes(32,'big')+postb.to_bytes(32,'big')
eff+=struct.pack('<Q',pren)+struct.pack('<Q',postn)
assert len(eff)==112, len(eff)
with open(sys.argv[1],'wb') as f:
    f.write(struct.pack('<Q', len(acct)))    # bytes 0..8 : AccountChanges len
    f.write(eff)                             # bytes 8..120 : 112-byte effect record
    f.write(acct)                            # bytes 120.. : AccountChanges RLP
    pad=(-(8+112+len(acct)))%8
    if pad: f.write(b'\x00'*pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_bal_account_nonstorage_consistent.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_nsc_${name}.emu.log" 2>&1 || true

  local st
  st=$(python3 -c "d=open('$out_file','rb').read(); print(int.from_bytes(d[0:8],'little'))")
  if [[ "$st" == "$exp" ]]; then
    printf "  %-16s OK   status=%s\n" "$name" "$st"; return 0
  fi
  printf "  %-16s FAIL status=%s expected=%s\n" "$name" "$st" "$exp"; return 1
}

FAILED=0
# Consistent: BAL final balance/nonce match exec post; exec net-changed both.
run_case "match"          match       100 999 5 9 0 || FAILED=1
# Reverse fail: exec changed balance (100->999) but BAL omits balance_changes.
run_case "omit_balance"   no_balance  100 999 5 9 1 || FAILED=1
# Reverse fail: exec changed nonce (5->9) but BAL omits nonce_changes.
run_case "omit_nonce"     no_nonce    100 999 5 9 1 || FAILED=1
# Forward fail: BAL declares a balance final != exec post.
run_case "wrong_balance"  wrong_bal   100 999 5 9 1 || FAILED=1
# Forward fail: BAL declares a nonce final != exec post.
run_case "wrong_nonce"    wrong_nonce 100 999 5 9 1 || FAILED=1
# Net-zero-OK: exec did NOT change balance (pre==post) but BAL declares a final == that
# value; nonce unchanged + undeclared. Final-consistent -> accepted (tuple layer = bmvmx.1.6.6).
run_case "netzero_ok"     match       777 777 0 0 0 || FAILED=1
# No-change/no-declare: exec unchanged, BAL declares nothing -> consistent.
run_case "untouched_ok"   no_balance  300 300 0 0 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: bal_account_nonstorage_consistent forward+reverse FINAL checks for balance/nonce"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
