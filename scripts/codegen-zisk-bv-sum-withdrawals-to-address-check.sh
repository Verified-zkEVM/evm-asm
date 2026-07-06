#!/usr/bin/env bash
# codegen-zisk-bv-sum-withdrawals-to-address-check.sh
#
# Validate bv_sum_withdrawals_to_address: sum of (amount_gwei * 1e9) wei over all
# SSZ withdrawals (44 bytes each) whose 20-byte address equals a target address.
# This is the EIP-4895 withdrawal-credit helper for the withdrawal-aware
# coinbase/recipient post-balance checks (bead evm-asm-uyu11.1).
set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_bv_sum_withdrawals_to_address ELF"
lake exe codegen --program zisk_bv_sum_withdrawals_to_address --halt linux93 \
  -o gen-out/zisk_bv_sum_withdrawals_to_address

read_u64() { od -An -tu8 -j "$2" -N 8 "$1" | tr -d ' \n'; }

# run_case <name> <target_addr_hex> <withdrawals_py> <exp_status>
run_case() {
  local name="$1" target="$2" wds_py="$3" exp_status="$4"
  local in_file="$REPO_ROOT/gen-out/zisk_bv_sum_withdrawals_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_bv_sum_withdrawals_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_bv_sum_withdrawals_${name}.exp"

  python3 - "$in_file" "$exp_file" "$target" <<PY
import struct, sys
in_path, exp_path, target_hex = sys.argv[1:4]
target = bytes.fromhex(target_hex)
assert len(target) == 20
# wds: list of (address_hex_20, amount_gwei)
wds = $wds_py
buf = bytearray()
buf += target                      # user +0 : target address (20)
buf += b"\x00" * 4                 # pad to +24
buf += struct.pack("<Q", len(wds)) # user +24 : count
for addr_hex, amt in wds:          # user +32 : 44-byte SSZ withdrawals
    a = bytes.fromhex(addr_hex); assert len(a) == 20
    buf += struct.pack("<Q", 0)        # index
    buf += struct.pack("<Q", 0)        # validator_index
    buf += a                            # address (20) @ +16
    buf += struct.pack("<Q", amt)      # amount Gwei LE @ +36
if len(buf) % 8:                       # ziskemu requires input size % 8 == 0
    buf += b"\x00" * (8 - len(buf) % 8)
with open(in_path, "wb") as f:
    f.write(buf)
expected_wei = sum(amt for addr_hex, amt in wds if bytes.fromhex(addr_hex) == target) * 10**9
with open(exp_path, "w") as f:
    f.write(expected_wei.to_bytes(32, "big").hex())
PY

  if ! "$ZISKEMU" -e gen-out/zisk_bv_sum_withdrawals_to_address.elf \
        -i "$in_file" -o "$out_file" -n 50000000 >/dev/null 2>&1 </dev/null; then
    printf "  %-22s ERROR ziskemu\n" "$name"; return 1
  fi

  local st actual expected
  st="$(read_u64 "$out_file" 0)"
  actual="$(od -An -v -tx1 -j 8 -N 32 "$out_file" | tr -d ' \n')"
  expected="$(cat "$exp_file")"
  if [[ "$st" != "$exp_status" ]]; then
    printf "  %-22s FAIL status=%s/%s\n" "$name" "$st" "$exp_status"; return 1
  fi
  if [[ "$exp_status" == "0" && "$actual" != "$expected" ]]; then
    printf "  %-22s FAIL sum\n      exp %s\n      got %s\n" "$name" "$expected" "$actual"; return 1
  fi
  printf "  %-22s OK   status=%s sum=0x%s\n" "$name" "$st" "${actual: -16}"
  return 0
}

A="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
B="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
C="cccccccccccccccccccccccccccccccccccccccc"

FAILED=0
run_case "none"           "$A" "[]" 0 || FAILED=1
run_case "no_match"       "$A" "[('$B', 100), ('$C', 200)]" 0 || FAILED=1
run_case "single_match"   "$A" "[('$A', 32000000000)]" 0 || FAILED=1
run_case "multi_match"    "$A" "[('$A', 1000000000), ('$B', 5), ('$A', 2000000000), ('$A', 7)]" 0 || FAILED=1
run_case "max_amount"     "$A" "[('$A', 18446744073709551615)]" 0 || FAILED=1
run_case "mixed_order"    "$B" "[('$A', 9), ('$B', 11), ('$C', 13), ('$B', 17)]" 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: bv_sum_withdrawals_to_address sums per-address withdrawal wei (amount_gwei*1e9)"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
