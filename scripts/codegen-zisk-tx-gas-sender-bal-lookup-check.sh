#!/usr/bin/env bash
# codegen-zisk-tx-gas-sender-bal-lookup-check.sh -- sender BAL pre-field lookup.
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

echo "==> emit zisk_tx_gas_sender_bal_lookup ELF"
lake exe codegen --program zisk_tx_gas_sender_bal_lookup --halt linux93 \
  -o gen-out/zisk_tx_gas_sender_bal_lookup

REPO_ROOT="$(pwd)"

wait_for_slot() {
  while (( $(jobs -pr | wc -l) >= JOBS )); do
    wait -n
  done
}

# run_case <name> <kind> <expect_status> <expect_row>
run_case() {
  local name="$1" kind="$2" expect_status="$3" expect_row="$4"
  local in_file="$REPO_ROOT/gen-out/zisk_tx_gas_sender_bal_lookup_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_gas_sender_bal_lookup_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_tx_gas_sender_bal_lookup_${name}.expected"
  local log_file="$REPO_ROOT/gen-out/zisk_tx_gas_sender_bal_lookup_${name}.emu.log"

  uv run --directory execution-specs --quiet python3 -c '
import struct, sys, rlp
from ethereum.crypto.hash import keccak256

in_path, exp_path, kind = sys.argv[1:4]
pubkey = bytes(range(1, 65))
addr = keccak256(pubkey)[12:]
other = bytes([0x77] * 20)
nonce = 7
balance = 12345678901234567890
post_balance = 12345678901234500000
post_nonce = 8
empty32 = bytes(32)
account = rlp.encode([nonce, balance, empty32, empty32])

def account_change(a):
    return rlp.encode([a, [], [], [[0, post_balance]], [[0, post_nonce]], []])

legacy_tx = rlp.encode([nonce, 10**9, 21000, other, 1, b"", 27, 1, 2])
typed_tx = b"\x02" + rlp.encode([1, nonce, 10**9, 2 * 10**9, 21000, other, 1, b"", [], 1, 1, 2])

if kind == "legacy":
    tx = legacy_tx
    bal = rlp.encode([rlp.decode(account_change(other)), rlp.decode(account_change(addr))])
    accounts = [account, account]
    status = 0
    row = 1
elif kind == "typed":
    tx = typed_tx
    bal = rlp.encode([rlp.decode(account_change(addr))])
    accounts = [account]
    status = 0
    row = 0
elif kind == "missing":
    tx = legacy_tx
    bal = rlp.encode([rlp.decode(account_change(other))])
    accounts = [account]
    status = 3
    row = (1 << 64) - 1
elif kind == "malformed":
    tx = b"\x02\x01"
    bal = rlp.encode([rlp.decode(account_change(addr))])
    accounts = [account]
    status = 1
    row = (1 << 64) - 1
else:
    raise ValueError(kind)

def align8(b):
    return b + b"\x00" * ((-len(b)) % 8)

payload = bytearray()
payload += struct.pack("<Q", len(tx))
payload += struct.pack("<Q", len(bal))
payload += struct.pack("<Q", len(accounts))
payload += pubkey
payload += tx
payload = bytearray(align8(payload))
payload += bal
payload = bytearray(align8(payload))
for acct in accounts:
    payload += struct.pack("<Q", len(acct))
for acct in accounts:
    payload += acct
    payload = bytearray(align8(payload))

with open(in_path, "wb") as f:
    f.write(payload)

expected = bytearray(168)
expected[0:8] = struct.pack("<Q", status)
expected[8:16] = struct.pack("<Q", row)
if status in (0, 3):
    expected[16:36] = addr
if status == 0:
    expected[48:80] = balance.to_bytes(32, "big")
    expected[80:88] = struct.pack("<Q", nonce)
    pb = post_balance.to_bytes((post_balance.bit_length() + 7) // 8, "big")
    pn = post_nonce.to_bytes((post_nonce.bit_length() + 7) // 8, "big")
    expected[88:96] = struct.pack("<Q", len(pb))
    expected[96:96 + len(pb)] = pb
    expected[128:136] = struct.pack("<Q", len(pn))
    expected[136:136 + len(pn)] = pn
else:
    expected[88:96] = struct.pack("<Q", (1 << 64) - 1)
    expected[128:136] = struct.pack("<Q", (1 << 64) - 1)

with open(exp_path, "wb") as f:
    f.write(expected)
' "$in_file" "$exp_file" "$kind"

  "$ZISKEMU" -e gen-out/zisk_tx_gas_sender_bal_lookup.elf \
    -i "$in_file" -o "$out_file" -n 2000000 \
    >"$log_file" 2>&1 || true

  local actual expected
  actual="$(xxd -p -l 168 "$out_file" | tr -d '\n')"
  expected="$(xxd -p -l 168 "$exp_file" | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-18s OK   status=%s row=%s\n" "$name" "$expect_status" "$expect_row"
    return 0
  fi

  printf "  %-18s FAIL\n    expected: %s\n    actual:   %s\n    emulator log: %s\n" \
    "$name" "$expected" "$actual" "$log_file"
  return 1
}

echo "==> run tx sender BAL lookup cases (jobs=$JOBS)"
FAILED_DIR="$REPO_ROOT/gen-out/zisk_tx_gas_sender_bal_lookup_failures"
rm -rf "$FAILED_DIR"
mkdir -p "$FAILED_DIR"

for case in \
  "legacy_success legacy 0 1" \
  "typed_success typed 0 0" \
  "missing_sender missing 3 -1" \
  "malformed_tx malformed 1 -1"
do
  wait_for_slot
  set -- $case
  (
    if ! run_case "$1" "$2" "$3" "$4"; then
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

echo "==> PASS: tx_gas_sender_bal_lookup locates sender BAL pre-fields"
