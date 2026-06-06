#!/usr/bin/env bash
# Verify optional runtime transaction intrinsic-gas validation.
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

echo "==> emit runtime_dispatcher ELF"
lake exe codegen --program runtime_dispatcher --halt linux93 -o gen-out/runtime_dispatcher

REPO_ROOT="$(pwd)"

# run_case <name> <gas> <is_creation> <calldata_hex> <expected_result_hex> <expected_halt_kind>
run_case() {
  local name="$1" gas="$2" is_creation="$3" calldata="$4" expected="$5" expected_halt="$6"
  local in_file="$REPO_ROOT/gen-out/runtime_tx_intrinsic_${name}.input"
  local out_file="$REPO_ROOT/gen-out/runtime_tx_intrinsic_${name}.output"

  local args=(--validate-tx-gas --gas "$gas" --calldata "$calldata")
  if [[ "$is_creation" == "1" ]]; then
    args+=(--tx-is-creation)
  fi

  scripts/pack-bytecode.py "${args[@]}" "0x5a, 0x00" "$in_file"

  "$ZISKEMU" -e gen-out/runtime_dispatcher.elf -i "$in_file" \
    -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/runtime_tx_intrinsic_${name}.emu.log" 2>&1 || true

  local actual actual_halt
  actual="$(xxd -p -c 64 -l 32 "$out_file" | tr -d '\n')"
  actual_halt="$(xxd -p -c 64 -s 32 -l 8 "$out_file" | tr -d '\n')"

  if [[ "$actual" == "$expected" && "$actual_halt" == "$expected_halt" ]]; then
    printf "  %-28s OK   gas=%s creation=%s calldata_len=%d\n" \
      "$name" "$gas" "$is_creation" "$(( ${#calldata} / 2 ))"
    return 0
  fi

  printf "  %-28s FAIL\n" "$name"
  printf "    expected out=%s halt=%s\n" "$expected" "$expected_halt"
  printf "    actual   out=%s halt=%s\n" "$actual" "$actual_halt"
  return 1
}

FAILED=0

# GAS costs 2 before pushing remaining gas. With tx gas 21005 and empty
# calldata, intrinsic is 21000, so GAS observes 3.
run_case "empty_call_remainder" \
  21005 0 "" \
  "0300000000000000000000000000000000000000000000000000000000000000" \
  "0000000000000000" || FAILED=1

# One gas below the empty-call intrinsic cost rejects before opcode execution.
run_case "empty_call_reject" \
  20999 0 "" \
  "0000000000000000000000000000000000000000000000000000000000000000" \
  "0600000000000000" || FAILED=1

# Nonzero calldata byte has intrinsic 21016 but EIP-7623 floor 21040.
run_case "nonzero_calldata_floor_reject" \
  21039 0 "ff" \
  "0000000000000000000000000000000000000000000000000000000000000000" \
  "0600000000000000" || FAILED=1

# If the floor is covered, execution still starts from tx.gas - intrinsic.
# 21042 - 21016 - GAS(2) = 24.
run_case "nonzero_calldata_floor_accept" \
  21042 0 "ff" \
  "1800000000000000000000000000000000000000000000000000000000000000" \
  "0000000000000000" || FAILED=1

# Creation adds 32000 intrinsic gas. 53005 - 53000 - GAS(2) = 3.
run_case "creation_remainder" \
  53005 1 "" \
  "0300000000000000000000000000000000000000000000000000000000000000" \
  "0000000000000000" || FAILED=1

# Creation initcode also pays CODE_INIT_PER_WORD = 2 per 32-byte word.
# len=33 zeros => data=132, initcode words=2 -> +4, so
# 53139 - 53136 - GAS(2) = 1.
run_case "creation_initcode_word_cost" \
  53139 1 "000000000000000000000000000000000000000000000000000000000000000000" \
  "0100000000000000000000000000000000000000000000000000000000000000" \
  "0000000000000000" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: runtime dispatcher validates/deducts opt-in tx intrinsic/floor gas"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
