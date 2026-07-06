#!/usr/bin/env bash
# codegen-zisk-header-validate-base-fee-check.sh -- PR-K74.
#
# Verify header.base_fee_per_gas matches the value computed from
# the parent header by EIP-1559's base-fee formula.
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

echo "==> emit zisk_header_validate_base_fee ELF"
lake exe codegen --program zisk_header_validate_base_fee --halt linux93 \
  -o gen-out/zisk_header_validate_base_fee

REPO_ROOT="$(pwd)"

# python_calc_expected <parent_gas_limit> <parent_gas_used> <parent_bf>
python_calc_expected() {
  python3 -c "
pgl, pgu, pbf = $1, $2, $3
target = pgl // 2
if pgu == target: print(pbf)
elif pgu > target:
    delta = pgu - target; pfgd = pbf*delta; tfgd = pfgd//target; bfd = max(tfgd//8, 1)
    print(pbf + bfd)
else:
    delta = target - pgu; pfgd = pbf*delta; tfgd = pfgd//target; bfd = tfgd//8
    print(pbf - bfd)
"
}

# run_case <name> <expected_status> <header_bf> <pgl> <pgu> <pbf>
run_case() {
  local name="$1" expected_status="$2" hbf="$3" pgl="$4" pgu="$5" pbf="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_header_validate_base_fee_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_header_validate_base_fee_${name}.output"

  python3 -c "
import struct, sys
hbf, pgl, pgu, pbf = $hbf, $pgl, $pgu, $pbf
with open(sys.argv[1], 'wb') as f:
    f.write(hbf.to_bytes(32, 'big'))
    f.write(struct.pack('<Q', pgl))
    f.write(struct.pack('<Q', pgu))
    f.write(pbf.to_bytes(32, 'big'))
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_header_validate_base_fee.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_header_validate_base_fee_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local exp_le; exp_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"

  if [[ "$actual" == "$exp_le" ]]; then
    printf "  %-30s OK   status=%d\n" "$name" "$expected_status"
    return 0
  else
    printf "  %-30s FAIL  expected status=%d got 0x%s\n" "$name" "$expected_status" "$actual"
    return 1
  fi
}

GWEI=$(python3 -c "print(10**9)")

FAILED=0
# Pass cases: header_bf == expected
PBF50=$(python3 -c "print(50 * $GWEI)")
EXP_FULL_BLOCK=$(python_calc_expected 30000000 30000000 "$PBF50")
run_case "pass_full_block"        0 "$EXP_FULL_BLOCK" 30000000 30000000 "$PBF50" || FAILED=1

EXP_HALF_EMPTY=$(python_calc_expected 30000000 7500000 "$PBF50")
run_case "pass_half_empty"        0 "$EXP_HALF_EMPTY" 30000000 7500000  "$PBF50" || FAILED=1

EXP_HUGE_ZERO_USED=$(python_calc_expected 9223372036854775807 0 11)
run_case "pass_huge_zero_used"    0 "$EXP_HUGE_ZERO_USED" 9223372036854775807 0 11 || FAILED=1

EXP_AT_TARGET=$(python_calc_expected 30000000 15000000 "$PBF50")
run_case "pass_at_target"         0 "$EXP_AT_TARGET" 30000000 15000000 "$PBF50" || FAILED=1

# Pass: realistic Holesky 60% used at 8 gwei
PBF8=$(python3 -c "print(8 * $GWEI)")
EXP_HOLESKY=$(python_calc_expected 30000000 18000000 "$PBF8")
run_case "pass_holesky_60_used"   0 "$EXP_HOLESKY" 30000000 18000000 "$PBF8" || FAILED=1

# Pass: zero base_fee
EXP_ZERO=$(python_calc_expected 30000000 15000000 0)
run_case "pass_zero_base"         0 "$EXP_ZERO" 30000000 15000000 0 || FAILED=1

# Reject: header_bf claims one less than expected
WRONG_LESS=$((EXP_FULL_BLOCK - 1))
run_case "reject_one_less"        1 "$WRONG_LESS" 30000000 30000000 "$PBF50" || FAILED=1

# Reject: header_bf claims one more
WRONG_MORE=$((EXP_FULL_BLOCK + 1))
run_case "reject_one_more"        1 "$WRONG_MORE" 30000000 30000000 "$PBF50" || FAILED=1

# Reject: header_bf = 0 when expected > 0
run_case "reject_zero_when_pos"   1 0            30000000 30000000 "$PBF50" || FAILED=1

# Reject: header_bf claims parent's value (no adjustment)
run_case "reject_no_adjustment"   1 "$PBF50"     30000000 30000000 "$PBF50" || FAILED=1

# Reject: header_bf wildly off
run_case "reject_huge_diff"       1 1            30000000 7500000  "$PBF50" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: header_validate_base_fee enforces EIP-1559 base-fee continuity"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
