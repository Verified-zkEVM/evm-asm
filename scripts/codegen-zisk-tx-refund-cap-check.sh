#!/usr/bin/env bash
# codegen-zisk-tx-refund-cap-check.sh -- EIP-3529 transaction refund cap.
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

echo "==> emit zisk_tx_refund_cap ELF"
lake exe codegen --program zisk_tx_refund_cap --halt linux93 \
  -o gen-out/zisk_tx_refund_cap

run_case() {
  local name="$1" tx_gas="$2" gas_left="$3" refund_counter="$4" expected="$5"
  local in_file="gen-out/zisk_tx_refund_cap_${name}.input"
  local out_file="gen-out/zisk_tx_refund_cap_${name}.output"
  local log_file="gen-out/zisk_tx_refund_cap_${name}.emu.log"

  python3 - "$in_file" "$tx_gas" "$gas_left" "$refund_counter" <<'PY'
import struct
import sys

path = sys.argv[1]
vals = [int(x, 0) for x in sys.argv[2:]]
with open(path, "wb") as f:
    for value in vals:
        f.write(struct.pack("<Q", value))
PY

  "$ZISKEMU" -e gen-out/zisk_tx_refund_cap.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$log_file" 2>&1

  local actual
  actual="$(xxd -p -c 256 -l 40 "$out_file" | tr -d '\n')"

  echo "==> $name"
  echo "expected:"
  echo "  $expected"
  echo "actual:"
  echo "  $actual"

  if [[ "$actual" != "$expected" ]]; then
    echo "FAIL: $name" >&2
    return 1
  fi
}

expected_hex() {
  python3 - "$@" <<'PY'
import struct
import sys

tx_gas, gas_left, refund_counter = (int(x, 0) for x in sys.argv[1:])
if gas_left > tx_gas:
    parts = [1, 0, 0, 0, 0]
else:
    before = tx_gas - gas_left
    cap = before // 5
    applied = min(cap, refund_counter)
    after = before - applied
    parts = [0, before, cap, applied, after]
print(b"".join(struct.pack("<Q", x) for x in parts).hex())
PY
}

FAILED=0
run_case "cap_limits_refund" 100000 20000 50000 \
  "$(expected_hex 100000 20000 50000)" || FAILED=1
run_case "counter_limits_refund" 100000 20000 10000 \
  "$(expected_hex 100000 20000 10000)" || FAILED=1
run_case "zero_gas_used" 21000 21000 1234 \
  "$(expected_hex 21000 21000 1234)" || FAILED=1
run_case "invalid_gas_left" 21000 21001 1 \
  "$(expected_hex 21000 21001 1)" || FAILED=1

if [[ "$FAILED" -ne 0 ]]; then
  exit 1
fi

echo "==> PASS: tx refund cap matches Amsterdam process_transaction formula"
