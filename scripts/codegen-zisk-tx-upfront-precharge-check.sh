#!/usr/bin/env bash
# codegen-zisk-tx-upfront-precharge-check.sh -- compose tx pricing + sender pre-charge.
#
# For one encoded transaction, compute effective gas pricing, extract gas_limit,
# deduct effective_gas_price * gas_limit from the sender balance, and increment
# the sender nonce. This is the standalone buffer-level helper used before BAL
# and stateless-verdict wiring.
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else
    echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2
    exit 1
  fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_tx_upfront_precharge ELF"
lake exe codegen --program zisk_tx_upfront_precharge --halt linux93 \
  -o gen-out/zisk_tx_upfront_precharge

REPO_ROOT="$(pwd)"

# run_case <name> <tx_type> <priority> <max_fee_or_gas_price> <base_fee> <balance> <nonce> <expected_status>
run_case() {
  local name="$1" tx_type="$2" pri="$3" maxfee="$4" base="$5" balance="$6" nonce="$7" expected_status="$8"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_upfront_precharge_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_upfront_precharge_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_tx_upfront_precharge_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c '
import struct, sys, rlp

tx_type = sys.argv[3]
pri = int(sys.argv[4], 0)
maxfee = int(sys.argv[5], 0)
base = int(sys.argv[6], 0)
balance = int(sys.argv[7], 0)
nonce = int(sys.argv[8], 0)
expected_status = int(sys.argv[9], 0)

ALICE = bytes([0xaa] * 20)
R = int.from_bytes(bytes([0x11] * 32), "big")
S = int.from_bytes(bytes([0x22] * 32), "big")
gas_limit = 21000

if tx_type == "legacy":
    tx = [nonce, maxfee, gas_limit, ALICE, 10**18, b"", 27, R, S]
    tx_bytes = rlp.encode(tx)
    max_priority = maxfee
    max_fee = maxfee
elif tx_type == "eip1559":
    tx = [1, nonce, pri, maxfee, gas_limit, ALICE, 10**18, b"", [], 1, R, S]
    tx_bytes = b"\x02" + rlp.encode(tx)
    max_priority = pri
    max_fee = maxfee
elif tx_type == "malformed":
    tx_bytes = b"\x02\xc1\x01"
    max_priority = max_fee = 0
else:
    raise ValueError(tx_type)

with open(sys.argv[1], "wb") as f:
    f.write(base.to_bytes(32, "big"))
    f.write(balance.to_bytes(32, "big"))
    f.write(struct.pack("<Q", nonce))
    f.write(struct.pack("<Q", len(tx_bytes)))
    f.write(tx_bytes)
    pad = (-(88 + len(tx_bytes))) % 8
    if pad:
        f.write(b"\x00" * pad)

MOD = 1 << 256
if expected_status == 0:
    priority = min(max_priority, max_fee - base)
    effective = base + priority
    gas_fee_full = effective * gas_limit
    gas_fee = gas_fee_full % MOD
    new_balance = balance - gas_fee
    new_nonce = (nonce + 1) % (1 << 64)
    out_gas = gas_limit
elif expected_status == 20:
    priority = 0
    effective = 0
    new_balance = balance
    new_nonce = nonce
    out_gas = gas_limit if tx_type != "malformed" else 0
elif expected_status == 31:
    priority = min(max_priority, max_fee - base)
    effective = base + priority
    new_balance = balance
    new_nonce = nonce
    out_gas = gas_limit
elif expected_status == 32:
    priority = min(max_priority, max_fee - base)
    effective = base + priority
    gas_fee = (effective * gas_limit) % MOD
    # account_charge_gas_pre_exec currently leaves the wrapped subtraction in
    # the mutable balance buffer when u256_sub_be reports borrow.
    new_balance = (balance - gas_fee) % MOD
    new_nonce = nonce
    out_gas = gas_limit
elif expected_status == 10:
    priority = 0
    effective = 0
    new_balance = balance
    new_nonce = nonce
    out_gas = 0
else:
    raise ValueError(expected_status)

with open(sys.argv[2], "wb") as f:
    f.write(struct.pack("<Q", expected_status))
    f.write(new_balance.to_bytes(32, "big"))
    f.write(struct.pack("<Q", new_nonce))
    f.write(struct.pack("<Q", out_gas))
    f.write(effective.to_bytes(32, "big"))
    f.write(priority.to_bytes(32, "big"))
' "$in_file" "$exp_file" "$tx_type" "$pri" "$maxfee" "$base" "$balance" "$nonce" "$expected_status"

  "$ZISKEMU" -e gen-out/zisk_tx_upfront_precharge.elf \
    -i "$in_file" -o "$out_file" -n 2000000 \
    >"$REPO_ROOT/gen-out/zisk_tx_upfront_precharge_${name}.emu.log" 2>&1 || true

  local actual expected
  actual="$(xxd -p -l 120 "$out_file" | tr -d '\n')"
  expected="$(xxd -p -l 120 "$exp_file" | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    local status_hex gas_hex
    status_hex="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
    gas_hex="$(dd if="$out_file" bs=1 skip=48 count=8 2>/dev/null | xxd -p | tr -d '\n')"
    printf "  %-30s OK   status=0x%s gas=%s\n" "$name" "$status_hex" "$gas_hex"
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected" "$actual"
    printf "    emulator log: %s\n" "$REPO_ROOT/gen-out/zisk_tx_upfront_precharge_${name}.emu.log"
    return 1
  fi
}

GWEI=1000000000
ETH=1000000000000000000
MAX256=115792089237316195423570985008687907853269984665640564039457584007913129639935

FAILED=0
run_case "legacy_success"       legacy   0          $((50 * GWEI))  $((30 * GWEI)) "$ETH" 5 0 || FAILED=1
run_case "eip1559_equal_base"   eip1559  $((2 * GWEI)) $((50 * GWEI))  $((50 * GWEI)) "$ETH" 7 0 || FAILED=1
run_case "fee_below_base"       eip1559  $((2 * GWEI)) $((40 * GWEI))  $((50 * GWEI)) "$ETH" 7 20 || FAILED=1
run_case "insufficient_balance" legacy   0          $((50 * GWEI))  $((30 * GWEI)) 10 0 32 || FAILED=1
run_case "mul_overflow"         legacy   0          "$MAX256"       0 "$ETH" 0 31 || FAILED=1
run_case "malformed_tx"         malformed 0         0               0 "$ETH" 0 10 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_upfront_precharge composes pricing, gas extraction, and sender pre-charge"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
