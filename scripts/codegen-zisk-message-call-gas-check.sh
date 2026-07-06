#!/usr/bin/env bash
# codegen-zisk-message-call-gas-check.sh -- EIP-150 message CALL gas helper.
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

echo "==> emit zisk_message_call_gas ELF"
lake exe codegen --program zisk_message_call_gas --halt linux93 \
  -o gen-out/zisk_message_call_gas

REPO_ROOT="$(pwd)"

# run_case <name> <value_nonzero> <requested> <gas_left> <memory_cost> <extra_gas>
run_case() {
  local name="$1" value_nonzero="$2" requested="$3" gas_left="$4" memory_cost="$5" extra_gas="$6"
  local in_file="$REPO_ROOT/gen-out/zisk_message_call_gas_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_message_call_gas_${name}.output"
  local expected_file="$REPO_ROOT/gen-out/zisk_message_call_gas_${name}.expected"

  python3 - "$in_file" "$expected_file" "$value_nonzero" "$requested" \
    "$gas_left" "$memory_cost" "$extra_gas" <<'EOF_PY'
import struct
import sys

(
    in_file,
    expected_file,
    value_nonzero_s,
    requested_s,
    gas_left_s,
    memory_cost_s,
    extra_gas_s,
) = sys.argv[1:]

U64 = 1 << 64
value_nonzero = int(value_nonzero_s, 0)
requested = int(requested_s, 0)
gas_left = int(gas_left_s, 0)
memory_cost = int(memory_cost_s, 0)
extra_gas = int(extra_gas_s, 0)

with open(in_file, "wb") as f:
    for value in (value_nonzero, requested, gas_left, memory_cost, extra_gas):
        f.write(struct.pack("<Q", value))

status = 0
cost = 0
sub_call = 0
capped = 0
mem_extra = memory_cost + extra_gas
if mem_extra >= U64:
    status = 1
else:
    stipend = 2300 if value_nonzero else 0
    if gas_left < mem_extra:
        capped = requested
    else:
        available = gas_left - mem_extra
        max_call = available - available // 64
        capped = min(requested, max_call)
    if capped + extra_gas >= U64 or capped + stipend >= U64:
        status = 2
        capped = 0
    else:
        cost = capped + extra_gas
        sub_call = capped + stipend

with open(expected_file, "wb") as f:
    for value in (status, cost, sub_call, capped):
        f.write(struct.pack("<Q", value))
EOF_PY

  "$ZISKEMU" -e gen-out/zisk_message_call_gas.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_message_call_gas_${name}.emu.log" 2>&1 || true

  local actual expected
  actual="$(dd if="$out_file" bs=1 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  expected="$(xxd -p -l 32 "$expected_file" | tr -d '\n')"
  if [[ "$actual" == "$expected" ]]; then
    printf "  %-28s OK\n" "$name"
    return 0
  fi
  printf "  %-28s FAIL\n    expected: %s\n    actual:   %s\n" \
    "$name" "$expected" "$actual"
  return 1
}

MAX_U64=18446744073709551615

FAILED=0
run_case "zero_value_no_cap" 0 10000 100000 100 0 || FAILED=1
run_case "value_stipend_no_cap" 1 10000 100000 100 9000 || FAILED=1
run_case "eip150_cap" 0 100000 64000 0 0 || FAILED=1
run_case "insufficient_left_branch" 1 50000 1000 600 500 || FAILED=1
run_case "input_overflow" 0 1 0 "$MAX_U64" 1 || FAILED=1
run_case "output_overflow" 0 "$MAX_U64" 0 0 1 || FAILED=1

if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: message_call_gas matches execution-specs EIP-150 formula"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
