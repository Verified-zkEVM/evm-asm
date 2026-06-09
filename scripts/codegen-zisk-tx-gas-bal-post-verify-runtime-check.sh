#!/usr/bin/env bash
# codegen-zisk-tx-gas-bal-post-verify-runtime-check.sh
# Execution-derived sender BAL post-balance verifier for a contract recipient:
#   sender_post = sender_pre - receipt_inc * effective_gas_price - value
# Runtime gas is hardcoded in the probe prologue (gas_limit=100000, gas_left=40000,
# refund=5000, floor=21000 -> receipt_inc=55000), and each case's expected output is
# computed against those constants.
set -euo pipefail

cd "$(dirname "$0")/.."

JOBS="${JOBS:-2}"
while [[ $# -gt 0 ]]; do
  case "$1" in
    --jobs)
      if [[ $# -lt 2 ]]; then echo "--jobs requires an argument" >&2; exit 2; fi
      JOBS="$2"; shift 2 ;;
    *)
      echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

if ! [[ "$JOBS" =~ ^[1-9][0-9]*$ ]]; then
  echo "--jobs must be a positive integer" >&2
  exit 2
fi

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

echo "==> emit zisk_tx_gas_bal_post_verify_runtime ELF"
lake exe codegen --program zisk_tx_gas_bal_post_verify_runtime --halt linux93 \
  -o gen-out/zisk_tx_gas_bal_post_verify_runtime

REPO_ROOT="$(pwd)"

wait_for_slot() {
  while (( $(jobs -pr | wc -l) >= JOBS )); do
    wait -n
  done
}

# run_case <name> <kind> <expect_status>
run_case() {
  local name="$1" kind="$2" expect_status="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_tx_gas_bal_post_verify_runtime_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_gas_bal_post_verify_runtime_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_tx_gas_bal_post_verify_runtime_${name}.expected"
  local log_file="$REPO_ROOT/gen-out/zisk_tx_gas_bal_post_verify_runtime_${name}.emu.log"

  uv run --directory execution-specs --quiet python3 -c '
import struct, sys, rlp
from ethereum.crypto.hash import keccak256

in_path, exp_path, kind = sys.argv[1:4]
pubkey = bytes(range(1, 65))
addr = keccak256(pubkey)[12:]
empty32 = bytes(32)
gas_limit = 100000
nonce = 7
base_fee = 30 * 10**9
legacy_gas_price = 50 * 10**9
tx_value = 1
balance = 10**18
mod = 1 << 256

# Mirrors the prologue gas constants: gas_left=40000, refund=5000, floor=21000.
before_refund = gas_limit - 40000              # 60000
applied_refund = min(5000, before_refund // 5) # 5000
after_refund = before_refund - applied_refund  # 55000
receipt_inc = max(after_refund, 21000)         # 55000
effective = legacy_gas_price
gas_debit = receipt_inc * effective

if kind == "contract_success":
    to = bytes([0x77] * 20)
    expected_post = balance - gas_debit - tx_value
    post_balance = expected_post
    status = 0
elif kind == "contract_mismatch":
    to = bytes([0x77] * 20)
    expected_post = balance - gas_debit - tx_value
    post_balance = expected_post + 12345       # prover lies -> reject
    status = 40
elif kind == "self_transfer":
    to = addr                                  # recipient == sender: value returns
    expected_post = balance - gas_debit
    post_balance = expected_post
    status = 0
else:
    raise ValueError(kind)

tx = rlp.encode([nonce, legacy_gas_price, gas_limit, to, tx_value, b"", 27, 1, 2])
account = rlp.encode([nonce, balance, empty32, empty32])

def account_change(a):
    balance_changes = [[0, post_balance]]
    return rlp.encode([a, [], [], balance_changes, [], []])

bal = rlp.encode([rlp.decode(account_change(addr))])

def align8(b):
    return b + b"\x00" * ((-len(b)) % 8)

payload = bytearray()
payload += struct.pack("<Q", len(tx))
payload += struct.pack("<Q", len(bal))
payload += struct.pack("<Q", 1)
payload += base_fee.to_bytes(32, "big")
payload += pubkey
payload += tx
payload = bytearray(align8(payload))
payload += bal
payload = bytearray(align8(payload))
payload += struct.pack("<Q", len(account))
payload += account
payload = bytearray(align8(payload))

with open(in_path, "wb") as f:
    f.write(payload)

expected = bytearray(192)
expected[0:8] = struct.pack("<Q", status)
expected[8:28] = addr
expected[32:64] = (balance % mod).to_bytes(32, "big")
expected[64:96] = (gas_debit % mod).to_bytes(32, "big")
expected[96:128] = (expected_post % mod).to_bytes(32, "big")
expected[128:160] = (post_balance % mod).to_bytes(32, "big")
expected[160:192] = (tx_value % mod).to_bytes(32, "big")

with open(exp_path, "wb") as f:
    f.write(expected)
' "$in_file" "$exp_file" "$kind"

  "$ZISKEMU" -e gen-out/zisk_tx_gas_bal_post_verify_runtime.elf \
    -i "$in_file" -o "$out_file" -n 2000000 \
    >"$log_file" 2>&1 || true

  local actual expected
  actual="$(xxd -p -l 192 "$out_file" | tr -d '\n')"
  expected="$(xxd -p -l 192 "$exp_file" | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-22s OK   status=%s\n" "$name" "$expect_status"
    return 0
  fi

  printf "  %-22s FAIL\n    expected: %s\n    actual:   %s\n    emulator log: %s\n" \
    "$name" "$expected" "$actual" "$log_file"
  return 1
}

echo "==> run runtime tx gas BAL post verifier cases (jobs=$JOBS)"
FAILED_DIR="$REPO_ROOT/gen-out/zisk_tx_gas_bal_post_verify_runtime_failures"
rm -rf "$FAILED_DIR"
mkdir -p "$FAILED_DIR"

for case in \
  "contract_success contract_success 0" \
  "contract_mismatch contract_mismatch 40" \
  "self_transfer self_transfer 0"
do
  wait_for_slot
  set -- $case
  (
    if ! run_case "$1" "$2" "$3"; then
      : >"$FAILED_DIR/$1"
    fi
  ) &
done

wait

echo
if compgen -G "$FAILED_DIR/*" >/dev/null; then
  echo "==> FAIL"
  exit 1
fi
echo "==> PASS: execution-derived sender BAL post-balance verifier"
