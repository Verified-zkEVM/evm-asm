#!/usr/bin/env bash
# codegen-zisk-bal-all-accounts-code-covers-check.sh -- bead i3djw (bmvmx.1.6.4.4, all-accounts CODE reverse).
#
# bal_all_accounts_code_covers is the REVERSE half: iterate the exec code-effect array and reject if any
# account exec changed code for (has_code_change=1) is ENTIRELY ABSENT from the block_access_list.
# Presence-only (a present account's declaration is verified by the forward wrapper #8600). Status: 0 / 1.
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

echo "==> emit zisk_bal_all_accounts_code_covers ELF"
lake exe codegen --program zisk_bal_all_accounts_code_covers --halt linux93 \
  -o gen-out/zisk_bal_all_accounts_code_covers

REPO_ROOT="$(pwd)"

# run_case <name> <mode> <exp_status>
run_case() {
  local name="$1" mode="$2" exp="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_aacc_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_aacc_${name}.output"

  MODE="$mode" uv run --directory execution-specs --quiet python3 -c "
import struct, sys, os, rlp
mode=os.environ['MODE']
acct1=bytes(range(1,21)); acct2=bytes(range(0x41,0x55))
code1=bytes.fromhex('6000600055')   # 5 bytes
code2=bytes.fromhex('600055')       # 3 bytes (different length -> exercises variable stride)

def rec(addr, has, code):
    r = addr.ljust(32, b'\x00') + struct.pack('<Q', has) + struct.pack('<Q', len(code)) + code
    pad = (-len(r)) % 8
    return r + b'\x00'*pad

def acct(addr, code): return [addr, [], [], [], [], [[4, code]]]   # declares a code change

# default: both code-effect records changed; both accounts present in the BAL.
effects  = [rec(acct1, 1, code1), rec(acct2, 1, code2)]
accounts = [acct(acct1, code1), acct(acct2, code2)]

if mode=='omitted':
    accounts = [acct(acct1, code1)]              # acct2 changed code but ABSENT -> reject
elif mode=='unchanged_skip':
    effects  = [rec(acct1, 1, code1), rec(acct2, 0, code2)]  # acct2 has_code_change=0
    accounts = [acct(acct1, code1)]              # acct2 unchanged + absent -> OK (skipped)

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

  "$ZISKEMU" -e gen-out/zisk_bal_all_accounts_code_covers.elf \
    -i "$in_file" -o "$out_file" -n 8000000 \
    >"$REPO_ROOT/gen-out/zisk_aacc_${name}.emu.log" 2>&1 || true

  local st
  st=$(python3 -c "d=open('$out_file','rb').read(); print(int.from_bytes(d[0:8],'little'))")
  if [[ "$st" == "$exp" ]]; then
    printf "  %-16s OK   status=%s\n" "$name" "$st"; return 0
  fi
  printf "  %-16s FAIL status=%s expected=%s\n" "$name" "$st" "$exp"; return 1
}

FAILED=0
# both changed code-effects' accounts present in the BAL -> covered.
run_case "covered"        covered        0 || FAILED=1
# a changed code-effect whose account is absent from the BAL -> reject.
run_case "omitted"        omitted        1 || FAILED=1
# a code-effect with has_code_change=0 (absent account) imposes no obligation -> OK.
run_case "unchanged_skip" unchanged_skip 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: bal_all_accounts_code_covers reverse all-accounts code completeness (variable-stride)"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
