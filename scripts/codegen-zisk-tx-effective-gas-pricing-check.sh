#!/usr/bin/env bash
# codegen-zisk-tx-effective-gas-pricing-check.sh -- tx fee pricing parity probe.
#
# Extract fee fields from a transaction, reject invalid fee ordering, and compute:
#   priority_fee_per_gas = min(max_priority_fee_per_gas, max_fee_per_gas - base_fee_per_gas)
#   effective_gas_price  = base_fee_per_gas + priority_fee_per_gas
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

echo "==> emit zisk_tx_effective_gas_pricing ELF"
lake exe codegen --program zisk_tx_effective_gas_pricing --halt linux93 \
  -o gen-out/zisk_tx_effective_gas_pricing

REPO_ROOT="$(pwd)"

# run_case <name> <tx_type> <priority> <max_fee_or_gas_price> <base_fee> <expected_status>
run_case() {
  local name="$1" t="$2" pri="$3" maxfee="$4" base="$5" status="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_effective_gas_pricing_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_effective_gas_pricing_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_tx_effective_gas_pricing_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
tx_type = '$t'
pri = $pri
maxfee = $maxfee
base = $base
expected_status = $status
ALICE = bytes([0xaa] * 20)
R = int.from_bytes(bytes([0x11] * 32), 'big')
S = int.from_bytes(bytes([0x22] * 32), 'big')

if tx_type == 'legacy':
    tx = [1, maxfee, 21000, ALICE, 10**18, b'', 27, R, S]
    tx_bytes = rlp.encode(tx)
    max_priority = maxfee
    max_fee = maxfee
elif tx_type == 'eip2930':
    inner = [1, 7, maxfee, 21000, ALICE, 10**18, b'', [], 1, R, S]
    tx_bytes = b'\x01' + rlp.encode(inner)
    max_priority = maxfee
    max_fee = maxfee
elif tx_type == 'eip1559':
    inner = [1, 7, pri, maxfee, 21000, ALICE, 10**18, b'', [], 1, R, S]
    tx_bytes = b'\x02' + rlp.encode(inner)
    max_priority = pri
    max_fee = maxfee
elif tx_type == 'eip4844':
    blob_hash = bytes([0x01] + [0xab] * 31)
    inner = [1, 7, pri, maxfee, 21000, ALICE, 10**18, b'', [], 1, [blob_hash], 0, R, S]
    tx_bytes = b'\x03' + rlp.encode(inner)
    max_priority = pri
    max_fee = maxfee
elif tx_type == 'eip7702':
    auth_list = [[1, ALICE, 0, 27, R, S]]
    inner = [1, 7, pri, maxfee, 21000, ALICE, 10**18, b'', [], auth_list, 1, R, S]
    tx_bytes = b'\x04' + rlp.encode(inner)
    max_priority = pri
    max_fee = maxfee
else:
    raise ValueError(tx_type)

if expected_status == 0:
    assert max_fee >= max_priority
    assert max_fee >= base
    priority = min(max_priority, max_fee - base)
    effective = base + priority
else:
    priority = 0
    effective = 0

with open(sys.argv[1], 'wb') as f:
    f.write(base.to_bytes(32, 'big'))
    f.write(struct.pack('<Q', len(tx_bytes)))
    f.write(tx_bytes)
    pad = (-(40 + len(tx_bytes))) % 8
    if pad:
        f.write(b'\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(struct.pack('<Q', expected_status))
    f.write(effective.to_bytes(32, 'big'))
    f.write(priority.to_bytes(32, 'big'))
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_tx_effective_gas_pricing.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_tx_effective_gas_pricing_${name}.emu.log" 2>&1 || true

  local actual expected
  actual="$(xxd -p -l 72 "$out_file" | tr -d '\n')"
  expected="$(xxd -p -l 72 "$exp_file" | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    local actual_status actual_effective actual_priority
    actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
    actual_effective="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
    actual_priority="$(dd if="$out_file" bs=1 skip=40 count=32 2>/dev/null | xxd -p | tr -d '\n')"
    printf "  %-34s OK   status=0x%s effective=%s.. priority=%s..\n" \
      "$name" "$actual_status" "${actual_effective:0:10}" "${actual_priority:0:10}"
    return 0
  else
    printf "  %-34s FAIL\n" "$name"
    printf "    expected: %s\n    actual:   %s\n" "$expected" "$actual"
    printf "    emulator log: %s\n" "$REPO_ROOT/gen-out/zisk_tx_effective_gas_pricing_${name}.emu.log"
    return 1
  fi
}

GWEI=1000000000
FAILED=0
run_case "legacy"                 legacy   0                 "50*$GWEI"  "30*$GWEI" 0 || FAILED=1
run_case "eip2930"                eip2930  0                 "45*$GWEI"  "20*$GWEI" 0 || FAILED=1
run_case "eip1559_priority_caps"  eip1559  "2*$GWEI"         "100*$GWEI" "50*$GWEI" 0 || FAILED=1
run_case "eip1559_surplus_caps"   eip1559  "10*$GWEI"        "55*$GWEI"  "50*$GWEI" 0 || FAILED=1
run_case "eip1559_equal_base"     eip1559  "2*$GWEI"         "50*$GWEI"  "50*$GWEI" 0 || FAILED=1
run_case "eip1559_fee_below_base" eip1559  "2*$GWEI"         "40*$GWEI"  "50*$GWEI" 3 || FAILED=1
run_case "eip1559_fee_below_tip"  eip1559  "60*$GWEI"        "50*$GWEI"  "10*$GWEI" 2 || FAILED=1
run_case "eip4844"                eip4844  "3*$GWEI"         "70*$GWEI"  "50*$GWEI" 0 || FAILED=1
run_case "eip7702"                eip7702  "4*$GWEI"         "90*$GWEI"  "50*$GWEI" 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_effective_gas_pricing computes execution-spec fee outputs"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
