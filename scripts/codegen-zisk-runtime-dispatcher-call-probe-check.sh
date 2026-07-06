#!/usr/bin/env bash
# Verify the callable runtime dispatcher returns to its caller.
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

echo "==> emit runtime_dispatcher_call_probe ELF"
lake exe codegen --program runtime_dispatcher_call_probe --halt linux93 \
  -o gen-out/runtime_dispatcher_call_probe

REPO_ROOT="$(pwd)"
IN_FILE="$REPO_ROOT/gen-out/runtime_dispatcher_call_probe.input"
OUT_FILE="$REPO_ROOT/gen-out/runtime_dispatcher_call_probe.output"

# GAS; STOP. The standalone runtime default gas is 30,000,000, and GAS
# charges its own static cost of 2 before pushing the remaining gas.
scripts/pack-bytecode.py "0x5a, 0x00" "$IN_FILE"

"$ZISKEMU" -e gen-out/runtime_dispatcher_call_probe.elf \
  -i "$IN_FILE" -o "$OUT_FILE" -n 500000 \
  >"$REPO_ROOT/gen-out/runtime_dispatcher_call_probe.emu.log" 2>&1 || true

actual_word="$(xxd -p -c 64 -l 32 "$OUT_FILE" | tr -d '\n')"
actual_halt="$(xxd -p -c 64 -s 32 -l 8 "$OUT_FILE" | tr -d '\n')"
actual_marker="$(xxd -p -c 64 -s 248 -l 8 "$OUT_FILE" | tr -d '\n')"
actual_gas="$(xxd -p -c 64 -s 240 -l 8 "$OUT_FILE" | tr -d '\n')"

expected_word="$(python3 - <<'PY'
print((30_000_000 - 2).to_bytes(32, "little").hex())
PY
)"
expected_halt="0000000000000000"
expected_marker="1eab11c000000000"
expected_gas="$(python3 - <<'PY'
print((30_000_000 - 2).to_bytes(8, "little").hex())
PY
)"

FAILED=0
if [[ "$actual_word" != "$expected_word" ]]; then
  echo "result word mismatch"
  echo "  expected: $expected_word"
  echo "  actual:   $actual_word"
  FAILED=1
fi
if [[ "$actual_halt" != "$expected_halt" ]]; then
  echo "halt_kind mismatch"
  echo "  expected: $expected_halt"
  echo "  actual:   $actual_halt"
  FAILED=1
fi
if [[ "$actual_marker" != "$expected_marker" ]]; then
  echo "return marker mismatch"
  echo "  expected: $expected_marker"
  echo "  actual:   $actual_marker"
  FAILED=1
fi
if [[ "$actual_gas" != "$expected_gas" ]]; then
  echo "final gasRemaining mismatch"
  echo "  expected: $expected_gas"
  echo "  actual:   $actual_gas"
  FAILED=1
fi

if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: callable runtime dispatcher returns to caller"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
