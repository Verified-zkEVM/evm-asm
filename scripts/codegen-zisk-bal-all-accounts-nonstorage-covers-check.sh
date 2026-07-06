#!/usr/bin/env bash
# codegen-zisk-bal-all-accounts-nonstorage-covers-check.sh -- bead i3djw (bmvmx.1.6.4.4 step .3b).
#
# bal_all_accounts_nonstorage_covers is the REVERSE half: it iterates the exec non-storage
# effect array and rejects if any account exec NET-CHANGED (post != pre, balance or nonce),
# excluding the recipient, is ENTIRELY ABSENT from the block_access_list. Status: 0 / 1.
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

echo "==> emit zisk_bal_all_accounts_nonstorage_covers ELF"
lake exe codegen --program zisk_bal_all_accounts_nonstorage_covers --halt linux93 \
  -o gen-out/zisk_bal_all_accounts_nonstorage_covers

REPO_ROOT="$(pwd)"

# run_case <name> <mode> <exp_status>
run_case() {
  local name="$1" mode="$2" exp="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_aac_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_aac_${name}.output"

  MODE="$mode" uv run --directory execution-specs --quiet python3 -c "
import struct, sys, os, rlp
mode=os.environ['MODE']
callee1  = bytes(range(1,21))
callee2  = bytes(range(0x41,0x55))
recipient= bytes(range(0x21,0x35))
sender   = bytes(range(0x61,0x75))

def eff(addr, preb, postb, pren, postn):
    r  = addr.ljust(32, b'\x00')
    r += preb.to_bytes(32,'big') + postb.to_bytes(32,'big')
    r += struct.pack('<Q', pren) + struct.pack('<Q', postn)
    assert len(r)==112, len(r); return r

def acct(addr): return [addr, [], [], [[1, 999]], [], []]   # a BAL account (declares a change)

skip = [recipient, sender]   # the gas/value-coupled accounts
# default: callee1 + callee2 both net-changed, both in BAL.
effects  = [eff(callee1, 100, 999, 5, 9), eff(callee2, 0, 50, 0, 1)]
accounts = [acct(callee1), acct(callee2)]

if mode=='omitted':
    accounts = [acct(callee1)]                  # callee2 net-changed but ABSENT -> reject
elif mode=='unchanged_skip':
    effects  = [eff(callee1, 100, 999, 5, 9), eff(callee2, 77, 77, 3, 3)]  # callee2 pre==post
    accounts = [acct(callee1)]                  # callee2 unchanged + absent -> OK (skipped)
elif mode=='skipmember_skip':
    # the SENDER (a skip-list member) is net-changed but absent from the BAL as a callee
    # -> must be SKIPPED (gas-path checked), not rejected as an omitted account.
    effects  = [eff(sender, 100, 999, 5, 9), eff(callee1, 0, 50, 0, 1)]
    accounts = [acct(callee1)]

bal = rlp.encode(accounts)
with open(sys.argv[1],'wb') as f:
    f.write(struct.pack('<Q', len(bal)))            # BAL section len
    f.write(struct.pack('<Q', len(effects)))        # effect count
    f.write(struct.pack('<Q', len(skip)))           # skip-list count
    for a in skip: f.write(a.ljust(32, b'\x00'))    # skip-list (32B entries)
    for e in effects: f.write(e)
    f.write(bal)
    total = 8 + 8 + 8 + 32*len(skip) + 112*len(effects) + len(bal)
    pad = (-total) % 8
    if pad: f.write(b'\x00'*pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_bal_all_accounts_nonstorage_covers.elf \
    -i "$in_file" -o "$out_file" -n 8000000 \
    >"$REPO_ROOT/gen-out/zisk_aac_${name}.emu.log" 2>&1 || true

  local st
  st=$(python3 -c "d=open('$out_file','rb').read(); print(int.from_bytes(d[0:8],'little'))")
  if [[ "$st" == "$exp" ]]; then
    printf "  %-18s OK   status=%s\n" "$name" "$st"; return 0
  fi
  printf "  %-18s FAIL status=%s expected=%s\n" "$name" "$st" "$exp"; return 1
}

FAILED=0
# every net-changed effect present in the BAL -> covered.
run_case "covered"        covered         0 || FAILED=1
# a net-changed callee absent from the BAL -> reject.
run_case "omitted"        omitted         1 || FAILED=1
# an effect with pre==post (no net change) absent from the BAL -> no obligation, OK.
run_case "unchanged_skip" unchanged_skip  0 || FAILED=1
# a skip-list member (sender) is net-changed but skipped (gas-path checked), absent as a callee -> OK.
run_case "skipmember_skip" skipmember_skip 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: bal_all_accounts_nonstorage_covers reverse all-accounts non-storage completeness"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
