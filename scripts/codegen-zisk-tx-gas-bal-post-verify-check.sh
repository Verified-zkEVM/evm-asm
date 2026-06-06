#!/usr/bin/env bash
# codegen-zisk-tx-gas-bal-post-verify-check.sh -- sender BAL post nonce after pre-charge.
set -euo pipefail

cd "$(dirname "$0")/.."

JOBS="${JOBS:-3}"
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

echo "==> emit zisk_tx_gas_bal_post_verify ELF"
lake exe codegen --program zisk_tx_gas_bal_post_verify --halt linux93 \
  -o gen-out/zisk_tx_gas_bal_post_verify

REPO_ROOT="$(pwd)"

wait_for_slot() {
  while (( $(jobs -pr | wc -l) >= JOBS )); do
    wait -n
  done
}

# run_case <name> <kind> <expect_status>
run_case() {
  local name="$1" kind="$2" expect_status="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_tx_gas_bal_post_verify_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_gas_bal_post_verify_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_tx_gas_bal_post_verify_${name}.expected"
  local log_file="$REPO_ROOT/gen-out/zisk_tx_gas_bal_post_verify_${name}.emu.log"

  uv run --directory execution-specs --quiet python3 -c '
import struct, sys, rlp
from ethereum.crypto.hash import keccak256

in_path, exp_path, kind = sys.argv[1:4]
pubkey = bytes(range(1, 65))
addr = keccak256(pubkey)[12:]
to = bytes([0x77] * 20)
empty32 = bytes(32)
gas_limit = 21000
nonce = 7
base_fee = 30 * 10**9
legacy_gas_price = 50 * 10**9
priority = 2 * 10**9
max_fee = 50 * 10**9
tx_value = 1

if kind == "legacy_success":
    tx = rlp.encode([nonce, legacy_gas_price, gas_limit, to, tx_value, b"", 27, 1, 2])
    effective = legacy_gas_price
    balance = 10**18
    post_nonce = nonce + 1
    post_balance = balance - effective * gas_limit - tx_value
    status = 0
    precharge_status = 0
elif kind == "typed_success":
    tx = b"\x02" + rlp.encode([1, nonce, priority, max_fee, gas_limit, to, tx_value, b"", [], 1, 1, 2])
    effective = base_fee + min(priority, max_fee - base_fee)
    balance = 10**18
    post_nonce = nonce + 1
    post_balance = balance - effective * gas_limit - tx_value
    status = 0
    precharge_status = 0
elif kind == "nonce_mismatch":
    tx = rlp.encode([nonce, legacy_gas_price, gas_limit, to, tx_value, b"", 27, 1, 2])
    effective = legacy_gas_price
    balance = 10**18
    post_nonce = nonce + 2
    post_balance = balance - effective * gas_limit - tx_value
    status = 32
    precharge_status = 0
elif kind == "post_nonce_absent":
    tx = rlp.encode([nonce, legacy_gas_price, gas_limit, to, tx_value, b"", 27, 1, 2])
    effective = legacy_gas_price
    balance = 10**18
    post_nonce = None
    post_balance = balance - effective * gas_limit - tx_value
    status = 30
    precharge_status = 0
elif kind == "insufficient_balance":
    tx = rlp.encode([nonce, legacy_gas_price, gas_limit, to, tx_value, b"", 27, 1, 2])
    effective = legacy_gas_price
    balance = 10
    post_nonce = nonce
    post_balance = balance
    status = 20
    precharge_status = 32
else:
    raise ValueError(kind)

gas_fee = effective * gas_limit
mod = 1 << 256
charged_balance = (balance - gas_fee) % mod
charged_nonce = nonce + 1 if precharge_status == 0 else nonce
account = rlp.encode([nonce, balance, empty32, empty32])

def account_change(a):
    balance_changes = [[0, post_balance]]
    nonce_changes = [] if post_nonce is None else [[0, post_nonce]]
    return rlp.encode([a, [], [], balance_changes, nonce_changes, []])

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

if post_nonce is None:
    post_nonce_len = (1 << 64) - 1
else:
    post_nonce_len = max(1, (post_nonce.bit_length() + 7) // 8)
post_nonce_u64 = 0 if post_nonce is None or precharge_status != 0 else post_nonce
post_balance_len = max(1, (post_balance.bit_length() + 7) // 8)

expected = bytearray(128)
expected[0:8] = struct.pack("<Q", status)
expected[8:16] = struct.pack("<Q", 0)
expected[16:24] = struct.pack("<Q", precharge_status)
expected[24:32] = struct.pack("<Q", 0)
expected[32:40] = struct.pack("<Q", nonce)
expected[40:48] = struct.pack("<Q", charged_nonce)
expected[48:56] = struct.pack("<Q", post_nonce_len)
expected[56:64] = struct.pack("<Q", post_nonce_u64)
expected[64:72] = struct.pack("<Q", post_balance_len)
expected[72:104] = charged_balance.to_bytes(32, "big")
expected[104:124] = addr

with open(exp_path, "wb") as f:
    f.write(expected)
' "$in_file" "$exp_file" "$kind"

  "$ZISKEMU" -e gen-out/zisk_tx_gas_bal_post_verify.elf \
    -i "$in_file" -o "$out_file" -n 2000000 \
    >"$log_file" 2>&1 || true

  local actual expected
  actual="$(xxd -p -l 128 "$out_file" | tr -d '\n')"
  expected="$(xxd -p -l 128 "$exp_file" | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-22s OK   status=%s\n" "$name" "$expect_status"
    return 0
  fi

  printf "  %-22s FAIL\n    expected: %s\n    actual:   %s\n    emulator log: %s\n" \
    "$name" "$expected" "$actual" "$log_file"
  return 1
}

echo "==> run tx gas BAL post verifier cases (jobs=$JOBS)"
FAILED_DIR="$REPO_ROOT/gen-out/zisk_tx_gas_bal_post_verify_failures"
rm -rf "$FAILED_DIR"
mkdir -p "$FAILED_DIR"

for case in \
  "legacy_success legacy_success 0" \
  "typed_success typed_success 0" \
  "nonce_mismatch nonce_mismatch 32" \
  "post_nonce_absent post_nonce_absent 30" \
  "insufficient_balance insufficient_balance 20"
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

echo "==> PASS: tx_gas_bal_post_verify checks BAL sender post nonce after pre-charge"
