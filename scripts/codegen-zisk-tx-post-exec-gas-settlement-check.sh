#!/usr/bin/env bash
# codegen-zisk-tx-post-exec-gas-settlement-check.sh -- transaction gas settlement wrapper.
#
# Given tx_gas_limit and remaining_gas after execution, compute gas_used,
# refund unused gas to the sender, and credit the coinbase priority fee.
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

echo "==> emit zisk_tx_post_exec_gas_settlement ELF"
lake exe codegen --program zisk_tx_post_exec_gas_settlement --halt linux93 \
  -o gen-out/zisk_tx_post_exec_gas_settlement

REPO_ROOT="$(pwd)"

# run_case <name> <sender_bal> <coinbase_bal> <egp> <priority_fee> <tx_gas_limit> <remaining_gas>
run_case() {
  local name="$1" sb="$2" cb="$3" egp="$4" pf="$5" gl="$6" rg="$7"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_post_exec_gas_settlement_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_post_exec_gas_settlement_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_tx_post_exec_gas_settlement_${name}.expected"

  python3 -c "
import struct, sys
sb, cb, egp, pf, gl, rg = $sb, $cb, $egp, $pf, $gl, $rg
with open(sys.argv[1], 'wb') as f:
    f.write(sb.to_bytes(32, 'big'))
    f.write(cb.to_bytes(32, 'big'))
    f.write(egp.to_bytes(32, 'big'))
    f.write(pf.to_bytes(32, 'big'))
    f.write(struct.pack('<Q', gl))
    f.write(struct.pack('<Q', rg))

MOD = 1 << 256
if rg > gl:
    status = 3
    gas_used = 0
    new_sb = sb
    new_cb = cb
else:
    gas_used = gl - rg
    refund = egp * rg
    credit = pf * gas_used
    if refund >= MOD or credit >= MOD:
        status = 1
        new_sb = sb
        new_cb = cb
    else:
        new_sb = sb + refund
        new_cb = cb + credit
        if new_sb >= MOD or new_cb >= MOD:
            status = 2
            new_sb = sb
            new_cb = cb
        else:
            status = 0

with open(sys.argv[2], 'wb') as f:
    f.write(struct.pack('<Q', status))
    f.write(new_sb.to_bytes(32, 'big'))
    f.write(new_cb.to_bytes(32, 'big'))
    f.write(struct.pack('<Q', gas_used))
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_tx_post_exec_gas_settlement.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_tx_post_exec_gas_settlement_${name}.emu.log" 2>&1 || true

  local exp_status actual_status exp_status_le
  exp_status="$(od -An -tu8 -N 8 "$exp_file" | tr -d ' \n')"
  actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  exp_status_le="$(python3 -c "print(int('$exp_status').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" != "$exp_status_le" ]]; then
    printf "  %-30s FAIL  status expected %s got 0x%s\n" "$name" "$exp_status" "$actual_status"
    printf "    emulator log: %s\n" "$REPO_ROOT/gen-out/zisk_tx_post_exec_gas_settlement_${name}.emu.log"
    return 1
  fi

  if [[ "$exp_status" == "0" || "$exp_status" == "3" ]]; then
    local actual expected
    actual="$(xxd -p -l 80 "$out_file" | tr -d '\n')"
    expected="$(xxd -p -l 80 "$exp_file" | tr -d '\n')"
    if [[ "$actual" != "$expected" ]]; then
      printf "  %-30s FAIL on output comparison\n" "$name"
      printf "    expected: %s\n    actual:   %s\n" "$expected" "$actual"
      printf "    emulator log: %s\n" "$REPO_ROOT/gen-out/zisk_tx_post_exec_gas_settlement_${name}.emu.log"
      return 1
    fi
  fi

  local gas_used
  gas_used="$(od -An -tu8 -j 72 -N 8 "$out_file" | tr -d ' \n')"
  printf "  %-30s OK   status=%s gas_used=%s\n" "$name" "$exp_status" "$gas_used"
  return 0
}

GWEI=$(python3 -c "print(10**9)")
ETH=$(python3 -c "print(10**18)")
MAX256=115792089237316195423570985008687907853269984665640564039457584007913129639935

FAILED=0
run_case "typical_partial_refund" \
  $(python3 -c "print(10**18 - 50 * 10**9 * 100000)") 1000 \
  $(python3 -c "print(50 * $GWEI)") $(python3 -c "print(2 * $GWEI)") 100000 50000 \
  || FAILED=1

run_case "all_gas_used" \
  $(python3 -c "print(10**18 - 50 * 10**9 * 21000)") 0 \
  $(python3 -c "print(50 * $GWEI)") $(python3 -c "print(3 * $GWEI)") 21000 0 \
  || FAILED=1

run_case "all_gas_remaining" \
  0 0 "$GWEI" "$GWEI" 100000 100000 \
  || FAILED=1

run_case "zero_priority_fee" \
  $(python3 -c "print(10**18)") 500 \
  $(python3 -c "print(10 * $GWEI)") 0 30000 10000 \
  || FAILED=1

run_case "remaining_gt_limit" \
  "$ETH" "$ETH" "$GWEI" "$GWEI" 21000 21001 \
  || FAILED=1

run_case "mul_overflow" \
  0 0 "$MAX256" 0 21000 2 \
  || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_post_exec_gas_settlement derives gas_used and applies sender/coinbase gas settlement"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
