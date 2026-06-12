#!/usr/bin/env bash
# Verify the runtime dispatcher gas-result capture path.
#
# Runs one staged transaction through the callable runtime dispatcher and
# checks the captured per-transaction gas results (gas_left, refund_counter,
# calldata_floor_gas_cost, halt_kind) surfaced at the OUTPUT+160 window — the
# values consumed by `block_verdict_gas_result_arena_prepare`.
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

echo "==> emit runtime_dispatcher_gas_capture_probe ELF"
lake exe codegen --program runtime_dispatcher_gas_capture_probe --halt linux93 \
  -o gen-out/runtime_dispatcher_gas_capture_probe

REPO_ROOT="$(pwd)"

le64_hex() {
  python3 -c "print(int('$1').to_bytes(8, 'little').hex())"
}

# run_case <name> <gas> <calldata_hex> <bytecode> \
#          <exp_gas_left> <exp_refund> <exp_floor> <exp_halt>
run_case() {
  local name="$1" gas="$2" calldata="$3" bytecode="$4"
  local exp_gas_left="$5" exp_refund="$6" exp_floor="$7" exp_halt="$8"
  local in_file="$REPO_ROOT/gen-out/runtime_gas_capture_${name}.input"
  local out_file="$REPO_ROOT/gen-out/runtime_gas_capture_${name}.output"
  local log_file="$REPO_ROOT/gen-out/runtime_gas_capture_${name}.emu.log"

  scripts/pack-bytecode.py --validate-tx-gas --gas "$gas" --calldata "$calldata" \
    "$bytecode" "$in_file"

  "$ZISKEMU" -e gen-out/runtime_dispatcher_gas_capture_probe.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$log_file" 2>&1 || true

  local a_gl a_rf a_fl a_hk a_mk
  a_gl="$(dd if="$out_file" bs=1 skip=160 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  a_rf="$(dd if="$out_file" bs=1 skip=168 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  a_fl="$(dd if="$out_file" bs=1 skip=176 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  a_hk="$(dd if="$out_file" bs=1 skip=184 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  a_mk="$(dd if="$out_file" bs=1 skip=192 count=8 2>/dev/null | xxd -p | tr -d '\n')"

  local e_gl e_rf e_fl e_hk e_mk
  e_gl="$(le64_hex "$exp_gas_left")"
  e_rf="$(le64_hex "$exp_refund")"
  e_fl="$(le64_hex "$exp_floor")"
  e_hk="$(le64_hex "$exp_halt")"
  e_mk="$(printf '%016x' 0xca97c0de | python3 -c "import sys;print(bytes.fromhex(sys.stdin.read().strip())[::-1].hex())")"

  if [[ "$a_gl" == "$e_gl" && "$a_rf" == "$e_rf" && "$a_fl" == "$e_fl" && \
        "$a_hk" == "$e_hk" && "$a_mk" == "$e_mk" ]]; then
    printf "  %-26s OK   gas_left=%s refund=%s floor=%s halt=%s\n" \
      "$name" "$exp_gas_left" "$exp_refund" "$exp_floor" "$exp_halt"
    return 0
  fi

  printf "  %-26s FAIL\n" "$name"
  printf "    expected gl=%s rf=%s fl=%s hk=%s marker=%s\n" \
    "$e_gl" "$e_rf" "$e_fl" "$e_hk" "$e_mk"
  printf "    actual   gl=%s rf=%s fl=%s hk=%s marker=%s\n" \
    "$a_gl" "$a_rf" "$a_fl" "$a_hk" "$a_mk"
  printf "    emulator log: %s\n" "$log_file"
  return 1
}

FAILED=0

# Empty-calldata simple STOP. intrinsic = floor = 21000. STOP costs 0, so
# gas_left = 21005 - 21000 = 5; halt_kind 0 (normal STOP); refund 0.
run_case "stop_empty" 21005 "" "0x00" \
  5 0 21000 0 || FAILED=1

# GAS then STOP. GAS costs 2 before STOP, so gas_left = 5 - 2 = 3.
run_case "gas_stop_empty" 21005 "" "0x5a, 0x00" \
  3 0 21000 0 || FAILED=1

# Nonzero calldata raises the EIP-7976 floor: every calldata byte counts 4
# tokens x TX_DATA_TOKEN_FLOOR(16) = 64 uniformly (mlp31 / #8701), so one byte
# gives floor 21064; the intrinsic data cost stays 4 tokens x 4 = 16 (21016).
# Execution starts from tx.gas - intrinsic; STOP costs 0, so
# gas_left = 21100 - 21016 = 84. Captured floor is 21064.
# (The pre-mlp31 expectation 21042/26/21040 made the tx floor-short after
# #8701 — the validate-tx-gas gate now correctly OOG-rejects gas 21042.)
run_case "stop_nonzero_calldata" 21100 "ff" "0x00" \
  84 0 21064 0 || FAILED=1

# REVERT (0xfd) with empty memory returns halt_kind 2 and keeps gas_left from
# the post-execution gasRemaining. PUSH1 0, PUSH1 0, REVERT: two PUSH1 (3 each)
# then REVERT (0 static). gas_left = 5 - 6 underflows the per-opcode gas check
# -> OOG (halt_kind 6, gas_left 0). Use a larger gas budget to reach REVERT.
# 21000 intrinsic + 6 push gas + slack: gas 21010 -> gas_left = 10 - 6 = 4.
run_case "revert_empty" 21010 "" "0x60, 0x00, 0x60, 0x00, 0xfd" \
  4 0 21000 2 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: runtime dispatcher captures per-tx gas results into capture arrays"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
