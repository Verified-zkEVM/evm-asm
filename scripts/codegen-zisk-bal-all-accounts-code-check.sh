#!/usr/bin/env bash
# codegen-zisk-bal-all-accounts-code-check.sh -- bead i3djw (bmvmx.1.6.4.4, all-accounts CODE).
#
# bal_all_accounts_code_consistent runs the per-account code comparator (bal_account_code_consistent
# #8591) over every block_access_list account, keying each to its VARIABLE-STRIDE exec code-effect
# record by 20-byte address. Status: 0 consistent / 1 reject.
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

echo "==> emit zisk_bal_all_accounts_code_consistent ELF"
lake exe codegen --program zisk_bal_all_accounts_code_consistent --halt linux93 \
  -o gen-out/zisk_bal_all_accounts_code_consistent

REPO_ROOT="$(pwd)"

# run_case <name> <mode> <exp_status>
run_case() {
  local name="$1" mode="$2" exp="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_aacode_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_aacode_${name}.output"

  MODE="$mode" uv run --directory execution-specs --quiet python3 -c "
import struct, sys, os, rlp
mode=os.environ['MODE']
acct1=bytes(range(1,21)); acct2=bytes(range(0x41,0x55))
acct3=bytes(range(0x61,0x75)); acct4=bytes(range(0x81,0x95))
code1=bytes.fromhex('6000600055')   # 5 bytes
code2=bytes.fromhex('600055')       # 3 bytes (different length -> exercises variable stride)

def rec(addr, has, code):
    r = addr.ljust(32, b'\x00') + struct.pack('<Q', has) + struct.pack('<Q', len(code)) + code
    pad = (-len(r)) % 8
    return r + b'\x00'*pad

def acct(addr, code): return [addr, [], [], [], [], [[4, code]]]   # declares a code change
def acct_nocode(addr): return [addr, [], [], [[1, 5]], [], []]      # no code change

# default: two accounts both declare code, both have matching effects.
effects  = [rec(acct1, 1, code1), rec(acct2, 1, code2)]
accounts = [acct(acct1, code1), acct(acct2, code2)]

if mode=='wrong_code':
    effects = [rec(acct1, 1, bytes.fromhex('6001600155')), rec(acct2, 1, code2)]  # acct1 bytes differ
elif mode=='declares_no_effect':
    accounts = [acct(acct1, code1), acct(acct3, code1)]   # acct3 declares code, no effect -> reject
    effects  = [rec(acct1, 1, code1)]
elif mode=='no_code_no_effect':
    accounts = [acct(acct1, code1), acct_nocode(acct4)]   # acct4 no code change, no effect -> skip
    effects  = [rec(acct1, 1, code1)]
elif mode=='delegation_7702_no_effect':
    # i3djw.4: an EIP-7702 delegation indicator (0xef0100 || 20-byte address, 23 bytes) is
    # installed from the authorization list, NOT a CREATE deposit, so it has no exec code-effect.
    # The forward comparator must SKIP it (status 0), not false-reject.
    deleg = bytes.fromhex('ef0100') + bytes(range(1,21))   # 3 + 20 = 23 bytes
    accounts = [acct(acct1, code1), acct(acct3, deleg)]
    effects  = [rec(acct1, 1, code1)]
elif mode=='wrong_len_no_effect':
    # 0xef0100-prefixed but 24 bytes (one too long) -> NOT a valid delegation -> still reject.
    almost = bytes.fromhex('ef0100') + bytes(range(1,22))  # 3 + 21 = 24 bytes
    accounts = [acct(acct1, code1), acct(acct3, almost)]
    effects  = [rec(acct1, 1, code1)]
elif mode=='wrong_prefix_no_effect':
    # 23 bytes but prefix 0xef0200 (not the 0xef0100 delegation magic) -> still reject.
    notdeleg = bytes.fromhex('ef0200') + bytes(range(1,21))  # 23 bytes, wrong prefix
    accounts = [acct(acct1, code1), acct(acct3, notdeleg)]
    effects  = [rec(acct1, 1, code1)]

earr = b''.join(effects)
bal  = rlp.encode(accounts)
with open(sys.argv[1],'wb') as f:
    f.write(struct.pack('<Q', len(bal)))     # BAL section len
    f.write(struct.pack('<Q', len(effects))) # code-effect record count
    f.write(struct.pack('<Q', len(earr)))    # code-effect array total byte length
    f.write(earr)                            # code-effect array (variable-stride)
    f.write(bal)                             # BAL section
    total = 8 + 8 + 8 + len(earr) + len(bal)
    pad = (-total) % 8
    if pad: f.write(b'\x00'*pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_bal_all_accounts_code_consistent.elf \
    -i "$in_file" -o "$out_file" -n 8000000 \
    >"$REPO_ROOT/gen-out/zisk_aacode_${name}.emu.log" 2>&1 || true

  local st
  st=$(python3 -c "d=open('$out_file','rb').read(); print(int.from_bytes(d[0:8],'little'))")
  if [[ "$st" == "$exp" ]]; then
    printf "  %-20s OK   status=%s\n" "$name" "$st"; return 0
  fi
  printf "  %-20s FAIL status=%s expected=%s\n" "$name" "$st" "$exp"; return 1
}

FAILED=0
# two code-declaring accounts, both with matching effects (different code lengths) -> consistent.
run_case "consistent"        consistent        0 || FAILED=1
# acct1's effect code bytes differ from the BAL declaration -> reject.
run_case "wrong_code"        wrong_code        1 || FAILED=1
# a code-declaring account with no matching effect record -> reject.
run_case "declares_no_effect" declares_no_effect 1 || FAILED=1
# an account with no code change + no effect -> skipped, OK.
run_case "no_code_no_effect" no_code_no_effect 0 || FAILED=1
# i3djw.4: an EIP-7702 delegation (0xef0100||addr, 23B) declared but with no exec effect -> skipped, OK.
run_case "delegation_7702_no_effect" delegation_7702_no_effect 0 || FAILED=1
# precision: a 0xef0100-prefixed code of the WRONG length (24B) with no effect -> still reject.
run_case "wrong_len_no_effect"    wrong_len_no_effect    1 || FAILED=1
# precision: a 23B code with the WRONG prefix (0xef0200) and no effect -> still reject.
run_case "wrong_prefix_no_effect" wrong_prefix_no_effect 1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: bal_all_accounts_code_consistent forward all-accounts code check (variable-stride effects)"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
