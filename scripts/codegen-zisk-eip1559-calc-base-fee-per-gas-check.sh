#!/usr/bin/env bash
# codegen-zisk-eip1559-calc-base-fee-per-gas-check.sh -- PR-K73.
#
# Full EIP-1559 base-fee formula.
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

echo "==> emit zisk_eip1559_calc_base_fee_per_gas ELF"
lake exe codegen --program zisk_eip1559_calc_base_fee_per_gas --halt linux93 \
  -o gen-out/zisk_eip1559_calc_base_fee_per_gas

REPO_ROOT="$(pwd)"

# run_case <name> <parent_gas_limit> <parent_gas_used> <parent_base_fee>
run_case() {
  local name="$1" pgl="$2" pgu="$3" pbf="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_eip1559_calc_base_fee_per_gas_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_eip1559_calc_base_fee_per_gas_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_eip1559_calc_base_fee_per_gas_${name}.expected"

  python3 -c "
import struct, sys
pgl = $pgl; pgu = $pgu; pbf = $pbf
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', pgl))
    f.write(struct.pack('<Q', pgu))
    f.write(pbf.to_bytes(32, 'big'))

# Python ref
target = pgl // 2
if pgu == target:
    exp = pbf
elif pgu > target:
    delta = pgu - target
    pfgd = pbf * delta
    tfgd = pfgd // target
    bfd = max(tfgd // 8, 1)
    exp = pbf + bfd
else:
    delta = target - pgu
    pfgd = pbf * delta
    tfgd = pfgd // target
    bfd = tfgd // 8
    exp = pbf - bfd

with open(sys.argv[2], 'wb') as f:
    f.write(struct.pack('<Q', 0))
    f.write(exp.to_bytes(32, 'big'))
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_eip1559_calc_base_fee_per_gas.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_eip1559_calc_base_fee_per_gas_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 40 "$out_file" | tr -d '\n')"
  local expected; expected="$(xxd -p -l 40 "$exp_file" | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    local exp_dec; exp_dec="$(python3 -c "
pgl, pgu, pbf = $pgl, $pgu, $pbf
target = pgl // 2
if pgu == target: print(pbf)
elif pgu > target:
    delta = pgu - target; pfgd = pbf*delta; tfgd = pfgd//target; bfd = max(tfgd//8, 1)
    print(pbf + bfd)
else:
    delta = target - pgu; pfgd = pbf*delta; tfgd = pfgd//target; bfd = tfgd//8
    print(pbf - bfd)
")"
    printf "  %-30s OK   expected=%s\n" "$name" "${exp_dec:0:24}..."
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected" "$actual"
    return 1
  fi
}

GWEI=$(python3 -c "print(10**9)")

FAILED=0
# gas_used == target → unchanged base fee
run_case "eq_target"            30000000 15000000 $(python3 -c "print(50 * $GWEI)") || FAILED=1
# gas_used > target (above path)
run_case "above_small"          30000000 15000001 $(python3 -c "print(50 * $GWEI)") || FAILED=1  # delta tiny
run_case "above_full"           30000000 30000000 $(python3 -c "print(50 * $GWEI)") || FAILED=1  # double block
run_case "above_mid"            30000000 22500000 $(python3 -c "print(50 * $GWEI)") || FAILED=1
# gas_used < target (below path)
run_case "below_small"          30000000 14999999 $(python3 -c "print(50 * $GWEI)") || FAILED=1  # delta tiny
run_case "below_empty"          30000000 0        $(python3 -c "print(50 * $GWEI)") || FAILED=1
run_case "below_empty_huge_gas" 9223372036854775807 0 11                              || FAILED=1
run_case "below_mid"            30000000 7500000  $(python3 -c "print(50 * $GWEI)") || FAILED=1
# max(_,1) edge: gas_used just above target with small base_fee
run_case "max_floor_kicks_in"   30000000 15000001 1                                  || FAILED=1
# Realistic: 100 gwei base fee, full block
run_case "100gwei_full_block"   30000000 30000000 $(python3 -c "print(100 * $GWEI)") || FAILED=1
# Realistic: 1 gwei base fee, half-empty
run_case "1gwei_half_empty"     30000000 5000000  "$GWEI"                            || FAILED=1
# Edge: base_fee = 0 → both paths produce 0
run_case "zero_base_above"      30000000 20000000 0                                  || FAILED=1
run_case "zero_base_below"      30000000 5000000  0                                  || FAILED=1
# Realistic Holesky shape: 30M gas_limit, 8 gwei base fee, 60% used
run_case "holesky_60_used"      30000000 18000000 $(python3 -c "print(8 * $GWEI)")   || FAILED=1
# Realistic Holesky shape: 30M gas_limit, 8 gwei base fee, 30% used
run_case "holesky_30_used"      30000000 9000000  $(python3 -c "print(8 * $GWEI)")   || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: eip1559_calc_base_fee_per_gas matches Python's calculate_base_fee_per_gas"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
