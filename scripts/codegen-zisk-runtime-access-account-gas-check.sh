#!/usr/bin/env bash
# codegen-zisk-runtime-access-account-gas-check.sh -- shared warm/cold access gas probe.
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

echo "==> emit zisk_runtime_access_account_gas ELF"
lake exe codegen --program zisk_runtime_access_account_gas --halt linux93 \
  -o gen-out/zisk_runtime_access_account_gas

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" selector="$2" expected_hex="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_runtime_access_account_gas_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_runtime_access_account_gas_${name}.output"

  python3 -c "import struct, sys; open(sys.argv[1], 'wb').write(struct.pack('<Q', int(sys.argv[2])))" \
    "$in_file" "$selector"

  "$ZISKEMU" -e gen-out/zisk_runtime_access_account_gas.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_runtime_access_account_gas_${name}.emu.log" 2>&1 || true

  local actual
  actual="$(xxd -p -l $(( ${#expected_hex} / 2 )) "$out_file" | tr -d '\n')"
  if [[ "$actual" == "$expected_hex" ]]; then
    printf "  %-24s OK\n" "$name"
    return 0
  else
    printf "  %-24s FAIL\n" "$name"
    printf "    expected: %s\n    actual:   %s\n" "$expected_hex" "$actual"
    printf "    emulator log: %s\n" "$REPO_ROOT/gen-out/zisk_runtime_access_account_gas_${name}.emu.log"
    return 1
  fi
}

FAILED=0

# Success sequence:
#   cold A inserts and charges 2500: status=1, gas=500, count=1
#   warm A charges 0:                 status=0, gas=500, count=1
#   active precompile 0x04 warm:      status=0, gas=500, count=1
SUCCESS_EXPECTED="$(
python3 - <<'PY'
import struct
vals = [1, 500, 1, 0, 500, 1, 0, 500, 1]
print(b''.join(struct.pack('<Q', v) for v in vals).hex())
PY
)"
run_case "cold_warm_precompile" 0 "$SUCCESS_EXPECTED" || FAILED=1

# Under-gas cold access jumps to .exit_outofgas, matching dispatcher halt_kind=6.
OOG_EXPECTED="$(
python3 - <<'PY'
import struct
print((b'\x00' * 32 + struct.pack('<Q', 6)).hex())
PY
)"
run_case "cold_under_gas_oog" 1 "$OOG_EXPECTED" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: runtime_access_account_charge handles warm/cold/precompile/OOG"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
