#!/usr/bin/env bash
# codegen-zisk-bal-all-accounts-nonstorage-check.sh -- bead i3djw (bmvmx.1.6.4.4 step .3a).
#
# bal_all_accounts_nonstorage_consistent runs the per-account non-storage FINAL comparator
# (bal_account_nonstorage_consistent, step .2) over every account in the block_access_list,
# skipping the top-level recipient, keying each callee to its exec effect record by 20-byte
# address. Status: 0 consistent / 1 reject.
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

echo "==> emit zisk_bal_all_accounts_nonstorage_consistent ELF"
lake exe codegen --program zisk_bal_all_accounts_nonstorage_consistent --halt linux93 \
  -o gen-out/zisk_bal_all_accounts_nonstorage_consistent

REPO_ROOT="$(pwd)"

# run_case <name> <mode> <exp_status>
run_case() {
  local name="$1" mode="$2" exp="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_aan_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_aan_${name}.output"

  MODE="$mode" uv run --directory execution-specs --quiet python3 -c "
import struct, sys, os, rlp
mode=os.environ['MODE']
callee   = bytes(range(1,21))        # callee1 address
recipient= bytes(range(0x21,0x35))   # 20-byte recipient address
callee2  = bytes(range(0x41,0x55))   # second callee address

def eff(addr, preb, postb, pren, postn):
    r  = addr.ljust(32, b'\x00')
    r += preb.to_bytes(32,'big') + postb.to_bytes(32,'big')
    r += struct.pack('<Q', pren) + struct.pack('<Q', postn)
    assert len(r)==112, len(r)
    return r

# BAL accounts: [addr, storage_changes, storage_reads, balance_changes, nonce_changes, code_changes]
recip_acct = [recipient, [], [], [[1, 1000]], [], []]            # has changes but is SKIPPED
callee_bal_final = 999
if mode=='inconsistent': callee_bal_final = 888                  # BAL final != exec post (999)
callee_acct = [callee, [], [], [[1, 499], [3, callee_bal_final]], [[1, 8], [2, 9]], []]

accounts = [callee_acct, recip_acct]
effects  = [eff(callee, 100, 999, 5, 9)]                         # exec: bal 100->999, nonce 5->9

if mode=='missing_declares':
    # a second callee that DECLARES a balance change but has NO effect record -> reject
    accounts.append([callee2, [], [], [[1, 7]], [], []])
elif mode=='missing_storage_only':
    # a second callee with ONLY a storage_change (no balance/nonce) + no effect -> skipped, OK
    accounts.append([callee2, [[b'\x01'.rjust(32,b'\x00'), [[1, b'\x05'.rjust(32,b'\x00')]]]], [], [], [], []])

bal = rlp.encode(accounts)
with open(sys.argv[1],'wb') as f:
    f.write(struct.pack('<Q', len(bal)))            # bytes 0..8 : BAL section len
    f.write(struct.pack('<Q', len(effects)))        # bytes 8..16 : effect count
    f.write(recipient.ljust(32, b'\x00'))           # bytes 16..48 : recipient (20B padded to 32)
    for e in effects: f.write(e)                    # effect array
    f.write(bal)                                    # BAL section
    total = 8 + 8 + 32 + 112*len(effects) + len(bal)
    pad = (-total) % 8
    if pad: f.write(b'\x00'*pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_bal_all_accounts_nonstorage_consistent.elf \
    -i "$in_file" -o "$out_file" -n 8000000 \
    >"$REPO_ROOT/gen-out/zisk_aan_${name}.emu.log" 2>&1 || true

  local st
  st=$(python3 -c "d=open('$out_file','rb').read(); print(int.from_bytes(d[0:8],'little'))")
  if [[ "$st" == "$exp" ]]; then
    printf "  %-22s OK   status=%s\n" "$name" "$st"; return 0
  fi
  printf "  %-22s FAIL status=%s expected=%s\n" "$name" "$st" "$exp"; return 1
}

FAILED=0
# callee finals match exec, recipient skipped -> consistent.
run_case "consistent"          consistent           0 || FAILED=1
# callee declares balance final 888 != exec post 999 -> .2 rejects.
run_case "inconsistent"        inconsistent         1 || FAILED=1
# extra callee declares a balance change with no exec effect record -> reject.
run_case "missing_declares"    missing_declares     1 || FAILED=1
# extra callee declares only a storage change (no non-storage), no effect -> skipped, OK.
run_case "missing_storage_only" missing_storage_only 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: bal_all_accounts_nonstorage_consistent forward all-accounts non-storage FINAL check"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
