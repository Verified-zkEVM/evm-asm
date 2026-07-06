#!/usr/bin/env bash
# Run a focused frontier check for pure stack opcode families.
#
# The runtime side is driven by `opcodeTestCases` in
# EvmAsm/Codegen/Tests/Cases.lean via `lake exe codegen --list-test-cases`.
# The EEST side delegates fixture discovery to codegen-eest-stateless-check.sh,
# so newly added matching fixtures are picked up by the existing manifest loop.
set -euo pipefail

cd "$(dirname "$0")/.."

RUN_RUNTIME=1
RUN_EEST=1
LIMIT=5
JOBS="${EEST_JOBS:-auto}"
MAX_FAILURES=1
EEST_FILTERS=()

usage() {
  cat <<'USAGE'
Usage:
  scripts/codegen-core-opcode-frontier-check.sh [options]

Options:
  --runtime / --no-runtime       run or skip opcode runtime cases (default: run)
  --eest / --no-eest             run or skip representative EEST filters (default: run)
  --filter SUBSTR                add an EEST fixture/test-label substring filter
                                 (default: frontier/opcodes/all_opcodes)
  --limit N                      per-filter EEST fixture cap (default: 5)
  --jobs N|auto                  ziskemu jobs for EEST runner (default: $EEST_JOBS or auto)
  --max-failures N               stop each EEST filter after N failures (default: 1)
  -h, --help                     show this help
USAGE
}

require_arg() {
  local opt="$1"
  if [[ $# -lt 2 || -z "${2:-}" ]]; then
    echo "$opt requires an argument" >&2
    usage >&2
    exit 1
  fi
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) usage; exit 0 ;;
    --runtime) RUN_RUNTIME=1; shift ;;
    --no-runtime) RUN_RUNTIME=0; shift ;;
    --eest) RUN_EEST=1; shift ;;
    --no-eest) RUN_EEST=0; shift ;;
    --filter) require_arg "$1" "${2:-}"; EEST_FILTERS+=("$2"); shift 2 ;;
    --limit) require_arg "$1" "${2:-}"; LIMIT="$2"; shift 2 ;;
    --jobs) require_arg "$1" "${2:-}"; JOBS="$2"; shift 2 ;;
    --max-failures|--stop-after-failures)
      require_arg "$1" "${2:-}"; MAX_FAILURES="$2"; shift 2 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ "${#EEST_FILTERS[@]}" -eq 0 ]]; then
  EEST_FILTERS=(frontier/opcodes/all_opcodes)
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

LIST_FILE="gen-out/.core-opcode-frontier-list"
lake exe codegen --list-test-cases >"$LIST_FILE"
cut -f1 "$LIST_FILE" >"${LIST_FILE}.names"

REQUIRED_CASES=(
  "ADD:add_basic"
  "SUB:sub_basic"
  "MUL:mul_basic"
  "DIV:div_basic"
  "MOD:mod_basic"
  "ADDMOD:addmod_basic"
  "ADDMOD:addmod_div_zero"
  "ADDMOD:addmod_carry_pow256_mod_7"
  "ADDMOD:addmod_carry_pow256_mod_2_128_plus_1"
  "ADDMOD:addmod_carry_reduced_sum_subtracts_n"
  "MULMOD:mulmod_zero_modulus"
  "MULMOD:mulmod_small_nonzero"
  "MULMOD:mulmod_high_product_nonzero"
  "EXP:exp_basic"
  "EXP:exp_zero"
  "EXP:exp_zero_zero"
  "EXP:exp_zero_positive"
  "EXP:exp_zero_high_exponent"
  "EXP:exp_one_large_exponent"
  "EXP:exp_max_word_squared"
  "EXP:exp_two_255_squared"
  "SDIV:sdiv_basic"
  "SMOD:smod_negative"
  "SIGNEXTEND:signextend_basic"
  "LT:lt_basic"
  "GT:gt_basic"
  "SLT:slt_basic"
  "SGT:sgt_basic"
  "EQ:eq_basic"
  "ISZERO:iszero_basic"
  "AND:and_basic"
  "OR:or_basic"
  "XOR:xor_basic"
  "NOT:not_basic"
  "BYTE:byte_basic"
  "SHL:shl_basic"
  "SHR:shr_basic"
  "SAR:sar_basic_positive"
  "SAR:sar_basic_negative"
  "CLZ:clz_zero"
  "POP:pop_basic"
  "PUSH0:push0_basic"
  "PUSH32:push32_basic"
  "DUP1:dup1_basic"
  "DUP16:dup16_basic"
  "SWAP1:swap1_basic"
  "SWAP16:swap16_basic"
  "PC:pc_at_zero"
  "MSIZE:mload_updates_msize"
  "GAS:gas_opcode_sufficient"
)

PARTIAL_MEMBERS=()

RUNTIME_FEATURE_SCRIPTS=(
  "BALANCE:scripts/codegen-zisk-runtime-balance-check.sh"
  "EXTCODESIZE:scripts/codegen-zisk-runtime-extcodesize-check.sh"
)

echo "==> checking representative runtime coverage"
MISSING=()
for entry in "${REQUIRED_CASES[@]}"; do
  opcode="${entry%%:*}"
  test_case="${entry#*:}"
  if grep -Fxq "$test_case" "${LIST_FILE}.names"; then
    printf '  %-10s %s\n' "$opcode" "$test_case"
  else
    printf '  %-10s missing %s\n' "$opcode" "$test_case" >&2
    MISSING+=("$entry")
  fi
done

if [[ "${#PARTIAL_MEMBERS[@]}" -gt 0 ]]; then
  echo "==> explicitly partial or separately tracked members"
  for entry in "${PARTIAL_MEMBERS[@]}"; do
    opcode="${entry%%:*}"
    reason="${entry#*:}"
    printf '  %-10s %s\n' "$opcode" "$reason"
  done
fi

if [[ "${#MISSING[@]}" -ne 0 ]]; then
  echo "==> missing required core opcode runtime representatives" >&2
  exit 1
fi

if [[ "$RUN_RUNTIME" -eq 1 ]]; then
  echo "==> running opcode runtime registry"
  scripts/codegen-opcodes-runtime-check.sh

  echo "==> running standalone runtime feature checks"
  for entry in "${RUNTIME_FEATURE_SCRIPTS[@]}"; do
    feature="${entry%%:*}"
    script="${entry#*:}"
    printf "  %-10s %s\n" "$feature" "$script"
    "$script"
  done
fi

if [[ "$RUN_EEST" -eq 1 ]]; then
  echo "==> running representative EEST frontier filters"
  for filter in "${EEST_FILTERS[@]}"; do
    echo "==> EEST filter: $filter"
    scripts/codegen-eest-stateless-check.sh \
      --filter "$filter" \
      --limit "$LIMIT" \
      --jobs "$JOBS" \
      --max-failures "$MAX_FAILURES" \
      --quiet-passes
  done
fi

echo "==> core opcode frontier check passed"
