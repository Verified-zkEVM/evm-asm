#!/usr/bin/env bash
# codegen-zisk-bal-account-nonstorage-finals-check.sh -- bead i3djw (bmvmx.1.6.4.4 step .1).
#
# bal_account_nonstorage_finals parses a BAL AccountChanges' NON-storage fields
# (balance/nonce/code changes) into their per-account FINAL values (the value of the
# last tuple of each), the BAL-side foundation for the non-storage exec-vs-BAL check.
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

echo "==> emit zisk_bal_account_nonstorage_finals ELF"
lake exe codegen --program zisk_bal_account_nonstorage_finals --halt linux93 \
  -o gen-out/zisk_bal_account_nonstorage_finals

REPO_ROOT="$(pwd)"
# code = 0x6000600055; rlp_list_nth_item returns the CONTENT (prefix stripped), so the
# located code field is the raw 5 code bytes (what a comparator keccaks).
CODEFIELD="6000600055"

# run_case <name> <mode> <exp_hasbal> <exp_bal> <exp_hasnonce> <exp_nonce> <exp_hascode>
run_case() {
  local name="$1" mode="$2" ehb="$3" ebal="$4" ehn="$5" en="$6" ehc="$7"
  local in_file="$REPO_ROOT/gen-out/zisk_nsf_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_nsf_${name}.output"

  MODE="$mode" uv run --directory execution-specs --quiet python3 -c "
import struct, sys, os, rlp
mode = os.environ['MODE']
addr = bytes(range(1,21))
balance_changes = [[1, 5000], [3, 10**18]]   # final post_balance = 10**18
nonce_changes   = [[1, 7], [2, 9]]           # final new_nonce = 9
code_changes    = [[4, bytes.fromhex('6000600055')]]
if mode == 'no_balance': balance_changes = []
if mode == 'no_code':    code_changes = []
acct = rlp.encode([addr, [], [], balance_changes, nonce_changes, code_changes])
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(acct))); f.write(acct)
    pad = (-(8 + len(acct))) % 8
    if pad: f.write(b'\x00'*pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_bal_account_nonstorage_finals.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_nsf_${name}.emu.log" 2>&1 || true

  local g
  g() { python3 -c "d=open('$out_file','rb').read(); print(int.from_bytes(d[$1:$1+8],'little'))"; }
  local st hb hn n hc coff clen bal
  st=$(g 0); hb=$(g 8); hn=$(g 48); n=$(g 56); hc=$(g 64); coff=$(g 72); clen=$(g 80)
  bal=$(python3 -c "d=open('$out_file','rb').read(); print(int.from_bytes(d[16:48],'big'))")

  local ok=1 msg=""
  [[ "$st" == "0"   ]] || { ok=0; msg+=" st=$st"; }
  [[ "$hb" == "$ehb" ]] || { ok=0; msg+=" hb=$hb!=$ehb"; }
  [[ "$ehb" != "1" || "$bal" == "$ebal" ]] || { ok=0; msg+=" bal=$bal!=$ebal"; }
  [[ "$hn" == "$ehn" ]] || { ok=0; msg+=" hn=$hn!=$ehn"; }
  [[ "$ehn" != "1" || "$n" == "$en" ]] || { ok=0; msg+=" n=$n!=$en"; }
  [[ "$hc" == "$ehc" ]] || { ok=0; msg+=" hc=$hc!=$ehc"; }
  if [[ "$ehc" == "1" ]]; then
    local got; got="$(python3 -c "d=open('$in_file','rb').read()[8:]; print(d[$coff:$coff+$clen].hex())")"
    [[ "$got" == "$CODEFIELD" ]] || { ok=0; msg+=" code=$got!=$CODEFIELD(off$coff,len$clen)"; }
  fi
  if [[ "$ok" == "1" ]]; then
    printf "  %-12s OK   bal=(%s,%s) nonce=(%s,%s) code=(%s)\n" "$name" "$hb" "$bal" "$hn" "$n" "$hc"; return 0
  fi
  printf "  %-12s FAIL%s\n" "$name" "$msg"; return 1
}

FAILED=0
run_case "all_three"  full       1 1000000000000000000 1 9 1 || FAILED=1
run_case "no_balance" no_balance 0 0                   1 9 1 || FAILED=1
run_case "no_code"    no_code    1 1000000000000000000 1 9 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: bal_account_nonstorage_finals extracts final balance/nonce + locates final code"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
