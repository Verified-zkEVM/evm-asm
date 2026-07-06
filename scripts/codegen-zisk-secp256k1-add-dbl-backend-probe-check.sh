#!/usr/bin/env bash
# Probe whether current ziskemu exposes secp256k1 add/double primitives to bare codegen ELFs.
set -euo pipefail

REQUIRE_READY=0
if [[ "${1:-}" == "--require-ready" ]]; then
  REQUIRE_READY=1
  shift
elif [[ $# -ne 0 ]]; then
  echo "usage: $0 [--require-ready]" >&2
  exit 1
fi

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

cat > gen-out/zisk_secp256k1_add_dbl.expected.hex <<'EOF_EXPECTED'
0000000000000000e59e705cb909acab a73cef8c4b8e775c d87cc0956e404530 6d7ded41947f04c6 2ae5cf50a9316423 e1d066326532f6f7 eeae6c461984c5a3 39c33da6fe68e11a 0000000000000000 e59e705cb909acab a73cef8c4b8e775c d87cc0956e404530 6d7ded41947f04c6 2ae5cf50a9316423 e1d066326532f6f7 eeae6c461984c5a3 39c33da6fe68e11a
EOF_EXPECTED
tr -d ' \n' < gen-out/zisk_secp256k1_add_dbl.expected.hex > gen-out/zisk_secp256k1_add_dbl.expected.compact.hex
EXPECTED_HEX="$(cat gen-out/zisk_secp256k1_add_dbl.expected.compact.hex)"
EXPECTED_BYTES=$(( ${#EXPECTED_HEX} / 2 ))

echo "==> lake build codegen"
lake build codegen

try_probe() {
  local program="$1"
  local label="$2"
  local base="gen-out/${program}"
  local codegen_log="${base}.codegen.log"
  local emu_log="${base}.emu.log"
  local out_file="${base}.output"

  echo
  echo "==> emit ${program} ELF (${label})"
  set +e
  lake exe codegen --program "$program" --halt linux93 -o "$base" >"$codegen_log" 2>&1
  local codegen_status=$?
  set -e
  if [[ $codegen_status -ne 0 ]]; then
    echo "==> NOT READY: ${label} symbols did not link from bare codegen ELF"
    sed -n '1,80p' "$codegen_log"
    return 2
  fi

  echo "==> ziskemu run (${label})"
  set +e
  "$ZISKEMU" -e "${base}.elf" -o "$out_file" -n 1000000 >"$emu_log" 2>&1
  local emu_status=$?
  set -e
  if [[ $emu_status -ne 0 ]]; then
    echo "==> NOT READY: ${label} route linked but ziskemu did not complete"
    echo "emulator exit: $emu_status"
    sed -n '1,80p' "$emu_log"
    return 2
  fi

  if [[ ! -f "$out_file" ]]; then
    echo "==> NOT READY: ${label} route completed without writing probe output"
    return 2
  fi

  local actual_hex
  actual_hex="$(xxd -p -l "$EXPECTED_BYTES" "$out_file" | tr -d '\n')"
  if [[ "$actual_hex" == "$EXPECTED_HEX" ]]; then
    echo "==> PASS: ${label} add(G,G) and dbl(G) returned 2G"
    return 0
  fi

  echo "==> FAIL: ${label} route returned an unexpected result"
  echo "    expected: $EXPECTED_HEX"
  echo "    actual:   $actual_hex"
  echo "    ziskemu log: $emu_log"
  return 1
}

READY=0
FAIL=0

try_probe zisk_secp256k1_add_dbl_syscall_probe "documented syscall_secp256k1_add/dbl" || status=$?
status=${status:-0}
if [[ $status -eq 0 ]]; then
  READY=1
elif [[ $status -eq 1 ]]; then
  FAIL=1
fi
unset status

try_probe zisk_secp256k1_add_dbl_opcode_probe "emulator-private _opcode_secp256k1_add/dbl" || status=$?
status=${status:-0}
if [[ $status -eq 0 ]]; then
  READY=1
elif [[ $status -eq 1 ]]; then
  FAIL=1
fi
unset status

if [[ $FAIL -ne 0 ]]; then
  exit 1
fi

if [[ $READY -eq 0 ]]; then
  echo
  echo "==> NOT READY: ziskemu 0.16.0 has secp256k1 add/double host primitives, but no tested bare-codegen symbol route is exposed"
  if [[ $REQUIRE_READY -eq 1 ]]; then
    exit 1
  fi
  exit 0
fi

exit 0
