#!/usr/bin/env bash
# codegen-zisk-bal-all-accounts-nonstorage-check.sh -- bead i3djw (bmvmx.1.6.4.4 step .3a).
#
# bal_all_accounts_nonstorage_consistent runs the per-account non-storage FINAL comparator
# over every block_access_list account, SKIPPING the gas/value-coupled accounts in the
# skip-list {sender,recipient,coinbase} (checked on the gas path), keying each remaining
# callee to its exec effect record by 20-byte address. Status: 0 consistent / 1 reject.
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
callee   = bytes(range(1,21))        # callee1
recipient= bytes(range(0x21,0x35))   # recipient (skip-list)
sender   = bytes(range(0x61,0x75))   # sender    (skip-list)
callee2  = bytes(range(0x41,0x55))   # second callee

def eff(addr, preb, postb, pren, postn):
    r  = addr.ljust(32, b'\x00')
    r += preb.to_bytes(32,'big') + postb.to_bytes(32,'big')
    r += struct.pack('<Q', pren) + struct.pack('<Q', postn)
    assert len(r)==112, len(r); return r

skip = [recipient, sender]   # the gas/value-coupled accounts
recip_acct = [recipient, [], [], [[1, 1000]], [], []]              # skipped
sender_acct= [sender,    [], [], [[1, 222]], [[1, 5]], []]         # skipped (gas-derived; no effect)
callee_bal_final = 999
if mode=='inconsistent': callee_bal_final = 888
callee_acct = [callee, [], [], [[1, 499], [3, callee_bal_final]], [[1, 8], [2, 9]], []]

accounts = [callee_acct, recip_acct, sender_acct]
effects  = [eff(callee, 100, 999, 5, 9)]                           # only the callee has an effect

if mode=='missing_declares':
    # a non-skip-list callee that declares a balance change but has no effect -> reject
    accounts.append([callee2, [], [], [[1, 7]], [], []])

bal = rlp.encode(accounts)
with open(sys.argv[1],'wb') as f:
    f.write(struct.pack('<Q', len(bal)))            # BAL section len
    f.write(struct.pack('<Q', len(effects)))        # effect count
    f.write(struct.pack('<Q', len(skip)))           # skip-list count
    for a in skip: f.write(a.ljust(32, b'\x00'))    # skip-list (32B entries)
    for e in effects: f.write(e)                    # effect array
    f.write(bal)                                    # BAL section
    total = 8 + 8 + 8 + 32*len(skip) + 112*len(effects) + len(bal)
    pad = (-total) % 8
    if pad: f.write(b'\x00'*pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_bal_all_accounts_nonstorage_consistent.elf \
    -i "$in_file" -o "$out_file" -n 8000000 \
    >"$REPO_ROOT/gen-out/zisk_aan_${name}.emu.log" 2>&1 || true

  local st
  st=$(python3 -c "d=open('$out_file','rb').read(); print(int.from_bytes(d[0:8],'little'))")
  if [[ "$st" == "$exp" ]]; then
    printf "  %-18s OK   status=%s\n" "$name" "$st"; return 0
  fi
  printf "  %-18s FAIL status=%s expected=%s\n" "$name" "$st" "$exp"; return 1
}

FAILED=0
# callee finals match exec; recipient + sender both in the skip-list -> consistent.
run_case "consistent"       consistent       0 || FAILED=1
# callee declares balance final 888 != exec post 999 -> reject.
run_case "inconsistent"     inconsistent     1 || FAILED=1
# the SENDER declares balance/nonce changes with NO effect record, but is in the skip-list
# -> must be SKIPPED (not the "declares-but-no-effect" reject); proves multi-account skipping.
run_case "skip_sender"      consistent       0 || FAILED=1
# a non-skip-list callee declares a balance change with no effect record -> reject.
run_case "missing_declares" missing_declares 1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: bal_all_accounts_nonstorage_consistent forward check with {sender,recipient,coinbase} skip-set"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
