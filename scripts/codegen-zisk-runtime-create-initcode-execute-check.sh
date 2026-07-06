#!/usr/bin/env bash
# codegen-zisk-runtime-create-initcode-execute-check.sh
#
# Exercise the bounded CREATE/CREATE2 initcode executor over the staged child
# frame. This is intentionally a small deterministic frontier: STOP, RETURN,
# REVERT, and INVALID/unsupported failure.
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

RUN_DIR="${RUN_DIR:-gen-out/runtime_create_initcode_execute}"
case "$RUN_DIR" in
  /*) ;;
  *) RUN_DIR="$PWD/$RUN_DIR" ;;
esac
mkdir -p "$RUN_DIR" gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit runtime_create_initcode_execute ELF"
lake exe codegen --program runtime_create_initcode_execute --halt linux93 -o gen-out/runtime_create_initcode_execute

make_case() {
  local name="$1" status="$2" ret_hex="$3" code_hex="$4" init_hex="$5"
  python3 - "$RUN_DIR/$name" "$status" "$ret_hex" "$code_hex" "$init_hex" <<'INNERPY'
import struct, sys
from pathlib import Path

out = Path(sys.argv[1])
status = int(sys.argv[2])
ret = bytes.fromhex(sys.argv[3])
code = bytes.fromhex(sys.argv[4])
initcode = bytes.fromhex(sys.argv[5])
value = (0).to_bytes(32, 'big')

payload = (
    struct.pack('<Q', 0)
    + struct.pack('<Q', 0)
    + struct.pack('<Q', len(initcode))
    + value
    + initcode
)
expected = (
    struct.pack('<Q', status)
    + struct.pack('<Q', len(ret))
    + struct.pack('<Q', len(code))
    + ret[:32].ljust(32, b'\x00')
    + code[:32].ljust(32, b'\x00')
)
out.mkdir(parents=True, exist_ok=True)
out.joinpath('input.bin').write_bytes(payload.ljust((len(payload) + 7) // 8 * 8, b'\x00'))
out.joinpath('expected.bin').write_bytes(expected)
INNERPY
}

FAILED=0
RETURN_WORD="000000000000000000000000000000000000000000000000000000000000002a"
LONG_PUSH0="$(python3 - <<'PY'
print('5f' * 1025)
PY
)"
CASES=(
  "stop 2 - - 00"
  "return_word 2 - $RETURN_WORD 602a60005260206000f3"
  "revert_byte 3 ab - 60ab60005360016000fd"
  "invalid 4 - - fe"
  "stack_bound_failure 4 - - $LONG_PUSH0"
)

for spec in "${CASES[@]}"; do
  read -r name status ret_hex code_hex init_hex <<<"$spec"
  [[ "$ret_hex" == "-" ]] && ret_hex=""
  [[ "$code_hex" == "-" ]] && code_hex=""
  make_case "$name" "$status" "$ret_hex" "$code_hex" "$init_hex"

  echo "==> ziskemu $name"
  if ! "$ZISKEMU" -e gen-out/runtime_create_initcode_execute.elf \
    -i "$RUN_DIR/$name/input.bin" \
    -o "$RUN_DIR/$name/output.bin" \
    -n 12000000 \
    >"$RUN_DIR/$name/emu.log" 2>&1; then
    FAILED=1
  fi

  exp_size="$(stat -c%s "$RUN_DIR/$name/expected.bin")"
  actual="$(xxd -p -l "$exp_size" "$RUN_DIR/$name/output.bin" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$RUN_DIR/$name/expected.bin" | tr -d '\n')"
  if [[ "$actual" == "$expected" ]]; then
    printf "  %-12s OK\n" "$name"
  else
    printf "  %-12s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected" "$actual"
    FAILED=1
  fi
done

if [[ "$FAILED" -ne 0 ]]; then
  echo "==> FAIL: runtime CREATE initcode execution" >&2
  exit 1
fi

echo "==> PASS: runtime CREATE initcode execution"
