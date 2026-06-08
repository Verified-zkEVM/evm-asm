#!/usr/bin/env bash
# codegen-zisk-secp256k1-scalar-check.sh -- secp256k1 scalar-field (mod group
# order n) inverse probe. Validates secf_inv_mod_n against Python pow(x, n-2, n).
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

PROGRAM=zisk_secp256k1_field_inv_n

echo "==> emit ${PROGRAM} ELF"
lake exe codegen --program "$PROGRAM" --halt linux93 -o "gen-out/${PROGRAM}"

REPO_ROOT="$(pwd)"
# secp256k1 group order n.
N_HEX="fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141"

run_case() {
  local name="$1" a="$2"
  local in_file="$REPO_ROOT/gen-out/${PROGRAM}_${name}.input"
  local out_file="$REPO_ROOT/gen-out/${PROGRAM}_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/${PROGRAM}_${name}.expected"
  local log_file="$REPO_ROOT/gen-out/${PROGRAM}_${name}.emu.log"

  python3 - "$a" "$N_HEX" "$in_file" "$exp_file" <<'PYSCRIPT'
import struct
import sys

a_s, n_hex, in_path, exp_path = sys.argv[1:]
N = int(n_hex, 16)
a = int(a_s, 0)

def u256(x):
    return (x % (1 << 256)).to_bytes(32, 'big')

with open(in_path, 'wb') as f:
    f.write(u256(a))

if a % N == 0:
    expected = struct.pack('<Q', 1) + bytes(32)
else:
    expected = struct.pack('<Q', 0) + u256(pow(a, N - 2, N))

with open(exp_path, 'wb') as f:
    f.write(expected)
PYSCRIPT

  "$ZISKEMU" -e "gen-out/${PROGRAM}.elf" -i "$in_file" -o "$out_file" -n 1000000000 >"$log_file" 2>&1 || true

  local exp_size actual expected
  exp_size="$(stat -c%s "$exp_file")"
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-40s OK\n" "${PROGRAM}/${name}"
    return 0
  else
    printf "  %-40s FAIL\n    expected: %s\n    actual:   %s\n" "${PROGRAM}/${name}" "$expected" "$actual"
    return 1
  fi
}

NM1_DEC="$(python3 -c 'print(int("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141",16)-1)')"
RAND_A="$(python3 -c 'print(int("123456789abcdef00112233445566778899aabbccddeeff0102030405060708",16))')"
# A value >= n to confirm input reduction mod n happens before inversion.
ABOVE_N="$(python3 -c 'print(int("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364142",16))')"

FAILED=0

run_case one 1 || FAILED=1
run_case n_minus_one "$NM1_DEC" || FAILED=1
run_case random_fixed "$RAND_A" || FAILED=1
run_case above_n "$ABOVE_N" || FAILED=1
run_case zero 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: secp256k1 scalar inverse probe matches Python pow(x, n-2, n) modulo the group order"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
