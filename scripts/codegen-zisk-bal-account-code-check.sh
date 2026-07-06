#!/usr/bin/env bash
# codegen-zisk-bal-account-code-check.sh -- bead i3djw (bmvmx.1.6.4.4, CODE field).
#
# bal_account_code_consistent compares a BAL AccountChanges' declared deployed code bytes
# (located by bal_account_nonstorage_finals) against an execution-derived code effect,
# forward (BAL declares => exec changed + bytes match) + reverse (exec changed => BAL
# declares). Status: 0 consistent / 1 inconsistent / 2 BAL parse failure.
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

echo "==> emit zisk_bal_account_code_consistent ELF"
lake exe codegen --program zisk_bal_account_code_consistent --halt linux93 \
  -o gen-out/zisk_bal_account_code_consistent

REPO_ROOT="$(pwd)"

# run_case <name> <mode> <exp_status>
run_case() {
  local name="$1" mode="$2" exp="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_bacc_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_bacc_${name}.output"

  MODE="$mode" uv run --directory execution-specs --quiet python3 -c "
import struct, sys, os, rlp
mode=os.environ['MODE']
addr=bytes(range(1,21))
code = bytes.fromhex('6000600055')        # deployed bytecode the BAL declares
code_changes = [[4, code]]
exec_has = 1
exec_code = code
if mode=='wrong_code':   exec_code = bytes.fromhex('6001600155')   # same len, different bytes
if mode=='bal_omits':    code_changes = []                          # BAL silent, exec changed
if mode=='exec_silent':  exec_has = 0                               # BAL declares, exec didn't
if mode=='both_silent':  code_changes = []; exec_has = 0            # neither -> consistent

acct = rlp.encode([addr, [], [], [], [], code_changes])
# exec code effect: has_code_change u64 | code_len u64 | code bytes ; padded to 8.
eff = struct.pack('<Q', exec_has) + struct.pack('<Q', len(exec_code)) + exec_code
pad = (-len(eff)) % 8
eff_padded = eff + b'\x00'*pad
with open(sys.argv[1],'wb') as f:
    f.write(struct.pack('<Q', len(acct)))        # AccountChanges len
    f.write(struct.pack('<Q', len(eff_padded)))  # effect padded length
    f.write(eff_padded)                          # exec code effect (8-aligned region)
    f.write(acct)                                # AccountChanges RLP
    total = 8 + 8 + len(eff_padded) + len(acct)
    p = (-total) % 8
    if p: f.write(b'\x00'*p)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_bal_account_code_consistent.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_bacc_${name}.emu.log" 2>&1 || true

  local st
  st=$(python3 -c "d=open('$out_file','rb').read(); print(int.from_bytes(d[0:8],'little'))")
  if [[ "$st" == "$exp" ]]; then
    printf "  %-14s OK   status=%s\n" "$name" "$st"; return 0
  fi
  printf "  %-14s FAIL status=%s expected=%s\n" "$name" "$st" "$exp"; return 1
}

FAILED=0
run_case "consistent"  consistent   0 || FAILED=1   # BAL code == exec code, both declare
run_case "wrong_code"  wrong_code   1 || FAILED=1   # same len, different bytes -> reject
run_case "bal_omits"   bal_omits    1 || FAILED=1   # exec changed code, BAL silent -> reject
run_case "exec_silent" exec_silent  1 || FAILED=1   # BAL declares, exec didn't -> reject
run_case "both_silent" both_silent  0 || FAILED=1   # neither changed code -> consistent

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: bal_account_code_consistent forward+reverse code-byte check"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
