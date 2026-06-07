#!/usr/bin/env bash
# codegen-zisk-secp256k1-curve-check.sh -- affine secp256k1 point helper probe.
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

program="zisk_secp256k1_curve_point_ops"
echo "==> emit ${program} ELF"
lake exe codegen --program "$program" --halt linux93 -o "gen-out/${program}"

out_file="gen-out/${program}.output"
exp_file="gen-out/${program}.expected"
log_file="gen-out/${program}.emu.log"

python3 - "$exp_file" <<'PYSCRIPT'
import struct
import sys

point2 = bytes.fromhex(
    'c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5'
    '1ae168fea63dc339a3c58419466ceaeef7f632653266d0e1236431a950cfe52a'
)
expected = struct.pack('<Q', 0) + point2 + struct.pack('<Q', 0) + point2
with open(sys.argv[1], 'wb') as f:
    f.write(expected)
PYSCRIPT

"$ZISKEMU" -e "gen-out/${program}.elf" -o "$out_file" -n 1000000000 >"$log_file" 2>&1 || true

exp_size="$(stat -c%s "$exp_file")"
actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

if [[ "$actual" == "$expected" ]]; then
  echo "==> PASS: secp256k1 point double(G) and add(G,G) match 2G"
  exit 0
else
  echo "==> FAIL: secp256k1 point helper probe mismatch"
  echo "    expected: $expected"
  echo "    actual:   $actual"
  echo "    ziskemu log: $log_file"
  exit 1
fi
