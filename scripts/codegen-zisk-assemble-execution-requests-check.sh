#!/usr/bin/env bash
# codegen-zisk-assemble-execution-requests-check.sh -- bead evm-asm-8uld3.4 (EIP-7685).
#
# assemble_execution_requests builds the SSZ ExecutionRequests section ([u32 off0][u32 off1]
# [u32 off2][deposits][withdrawals][consolidations]) from the three execution-derived request
# bodies, then execution_requests_hash computes the post-execution requests_hash =
# SHA256(concat(SHA256(type||body) for each non-empty body)). This verifies the derived-from-
# bodies path matches the EIP-7685 commitment.
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

echo "==> emit zisk_assemble_execution_requests ELF"
lake exe codegen --program zisk_assemble_execution_requests --halt linux93 \
  -o gen-out/zisk_assemble_execution_requests

REPO_ROOT="$(pwd)"

# run_case <name> <n_deposit> <n_withdrawal> <n_consolidation>
run_case() {
  local name="$1" nd="$2" nw="$3" nc="$4"
  local in_file="$REPO_ROOT/gen-out/zisk_aer_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_aer_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_aer_${name}.expected"

  ND="$nd" NW="$nw" NC="$nc" python3 -c "
import struct, sys, os, hashlib
nd=int(os.environ['ND']); nw=int(os.environ['NW']); nc=int(os.environ['NC'])
# DepositRequest=192, WithdrawalRequest=76, ConsolidationRequest=116 fixed-size SSZ elements.
deposit       = bytes((0x11 + i) & 0xff for i in range(192*nd))
withdrawal    = bytes((0x44 + i) & 0xff for i in range(76*nw))
consolidation = bytes((0x77 + i) & 0xff for i in range(116*nc))

def sha(b): return hashlib.sha256(b).digest()
digests = b''
if len(deposit)       > 0: digests += sha(b'\\x00' + deposit)
if len(withdrawal)    > 0: digests += sha(b'\\x01' + withdrawal)
if len(consolidation) > 0: digests += sha(b'\\x02' + consolidation)
req_hash = sha(digests)
total = 12 + len(deposit) + len(withdrawal) + len(consolidation)

with open(sys.argv[1],'wb') as f:
    f.write(struct.pack('<Q', len(deposit)))
    f.write(struct.pack('<Q', len(withdrawal)))
    f.write(struct.pack('<Q', len(consolidation)))
    body = deposit + withdrawal + consolidation
    f.write(body)
    pad = (-(32+len(body))) % 8
    if pad: f.write(b'\\x00'*pad)
with open(sys.argv[2],'wb') as f:
    f.write(struct.pack('<Q', 0))       # status
    f.write(struct.pack('<Q', total))   # total length
    f.write(req_hash)                   # 32-byte derived requests_hash
    f.write(struct.pack('<Q', 0))       # requests_hash_verify(correct) -> 0 match
    f.write(struct.pack('<Q', 1))       # requests_hash_verify(corrupted) -> 1 mismatch
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_assemble_execution_requests.elf \
    -i "$in_file" -o "$out_file" -n 12000000 \
    >"$REPO_ROOT/gen-out/zisk_aer_${name}.emu.log" 2>&1 || true

  local actual expected
  actual="$(xxd -p -l 64 "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l 64 "$exp_file" 2>/dev/null | tr -d '\n')"
  if [[ "$actual" == "$expected" ]]; then
    printf "  %-18s OK\n" "$name"; return 0
  fi
  printf "  %-18s FAIL\n    got=%s\n    exp=%s\n" "$name" "$actual" "$expected"; return 1
}

FAILED=0
# all three request types present -> hash over 3 per-body digests.
run_case "all_three"     1 1 1 || FAILED=1
# deposits only (withdrawals/consolidations empty -> skipped) -> hash over 1 digest.
run_case "deposit_only"  2 0 0 || FAILED=1
# withdrawals + consolidations, no deposits.
run_case "no_deposit"    0 1 2 || FAILED=1
# all empty -> total=12, requests_hash = SHA256(b'').
run_case "empty"         0 0 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: assemble_execution_requests + execution_requests_hash derive the EIP-7685 commitment"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
