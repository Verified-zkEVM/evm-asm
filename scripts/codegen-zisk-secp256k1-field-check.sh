#!/usr/bin/env bash
# codegen-zisk-secp256k1-field-check.sh -- secp256k1 p-field foundation probes.
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

PROGRAMS=(
  zisk_secp256k1_field_cmp_p
  zisk_secp256k1_field_reduce_once
  zisk_secp256k1_field_add
  zisk_secp256k1_field_sub
  zisk_secp256k1_field_mul
  zisk_secp256k1_field_square
  zisk_secp256k1_field_inv
  zisk_secp256k1_field_sqrt
)

for program in "${PROGRAMS[@]}"; do
  echo "==> emit ${program} ELF"
  lake exe codegen --program "$program" --halt linux93 -o "gen-out/${program}"
done

REPO_ROOT="$(pwd)"
P_HEX="fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f"

run_case() {
  local program="$1" name="$2" op="$3" a="$4" b="${5:-0}"
  local in_file="$REPO_ROOT/gen-out/${program}_${name}.input"
  local out_file="$REPO_ROOT/gen-out/${program}_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/${program}_${name}.expected"
  local log_file="$REPO_ROOT/gen-out/${program}_${name}.emu.log"

  python3 - "$op" "$a" "$b" "$P_HEX" "$in_file" "$exp_file" <<'PYSCRIPT'
import struct
import sys

op, a_s, b_s, p_hex, in_path, exp_path = sys.argv[1:]
P = int(p_hex, 16)
a = int(a_s, 0)
b = int(b_s, 0)

def u256(x):
    return (x % (1 << 256)).to_bytes(32, 'big')

with open(in_path, 'wb') as f:
    f.write(u256(a))
    if op in {'add', 'sub', 'mul'}:
        f.write(u256(b))

if op == 'cmp':
    cmp_status = 0 if a < P else (1 if a == P else 2)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', cmp_status)
elif op == 'reduce':
    reduced = a - P if a >= P else a
    flag = 1 if a >= P else 0
    expected = struct.pack('<Q', 0) + struct.pack('<Q', flag) + u256(reduced)
elif op == 'add':
    expected = struct.pack('<Q', 0) + u256((a + b) % P)
elif op == 'sub':
    expected = struct.pack('<Q', 0) + u256((a - b) % P)
elif op == 'mul':
    expected = struct.pack('<Q', 0) + u256((a * b) % P)
elif op == 'square':
    expected = struct.pack('<Q', 0) + u256((a * a) % P)
elif op == 'inv':
    if a % P == 0:
        expected = struct.pack('<Q', 1) + bytes(32)
    else:
        expected = struct.pack('<Q', 0) + u256(pow(a, P - 2, P))
elif op == 'sqrt':
    x = a % P
    y = pow(x, (P + 1) // 4, P)
    if (y * y) % P == x:
        expected = struct.pack('<Q', 0) + u256(y)
    else:
        expected = struct.pack('<Q', 1) + bytes(32)
else:
    raise SystemExit(f'unknown op: {op}')

with open(exp_path, 'wb') as f:
    f.write(expected)
PYSCRIPT

  local steps=2000000
  if [[ "$op" == "inv" || "$op" == "sqrt" ]]; then
    steps=1000000000
  fi

  "$ZISKEMU" -e "gen-out/${program}.elf" -i "$in_file" -o "$out_file" -n "$steps" >"$log_file" 2>&1 || true

  local exp_size actual expected
  exp_size="$(stat -c%s "$exp_file")"
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-44s OK\n" "${program}/${name}"
    return 0
  else
    printf "  %-44s FAIL\n    expected: %s\n    actual:   %s\n" "${program}/${name}" "$expected" "$actual"
    return 1
  fi
}

P_DEC="$(python3 - <<'PYSCRIPT'
P = int('fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f', 16)
print(P)
PYSCRIPT
)"
PM1_DEC="$(python3 - <<'PYSCRIPT'
P = int('fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f', 16)
print(P - 1)
PYSCRIPT
)"
PP1_DEC="$(python3 - <<'PYSCRIPT'
P = int('fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f', 16)
print(P + 1)
PYSCRIPT
)"
MAX_DEC="$(python3 - <<'PYSCRIPT'
print((1 << 256) - 1)
PYSCRIPT
)"
RAND_A="$(python3 - <<'PYSCRIPT'
print(int('123456789abcdef00112233445566778899aabbccddeeff0102030405060708', 16))
PYSCRIPT
)"
RAND_B="$(python3 - <<'PYSCRIPT'
print(int('deadbeefcafebabe00112233445566778899aabbccddeeff0102030405060', 16))
PYSCRIPT
)"
GENERATOR_RHS="$(python3 - <<'PYSCRIPT'
P = int('fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f', 16)
Gx = int('79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798', 16)
print((pow(Gx, 3, P) + 7) % P)
PYSCRIPT
)"
NON_RESIDUE="$(python3 - <<'PYSCRIPT'
P = int('fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f', 16)
print(next(x for x in range(2, 100) if pow(x, (P - 1) // 2, P) == P - 1))
PYSCRIPT
)"
P_PLUS_FIVE="$(python3 - <<'PYSCRIPT'
P = int('fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f', 16)
print(P + 5)
PYSCRIPT
)"

FAILED=0

run_case zisk_secp256k1_field_cmp_p zero cmp 0 || FAILED=1
run_case zisk_secp256k1_field_cmp_p p_minus_one cmp "$PM1_DEC" || FAILED=1
run_case zisk_secp256k1_field_cmp_p p_equal cmp "$P_DEC" || FAILED=1
run_case zisk_secp256k1_field_cmp_p p_plus_one cmp "$PP1_DEC" || FAILED=1
run_case zisk_secp256k1_field_cmp_p max cmp "$MAX_DEC" || FAILED=1

run_case zisk_secp256k1_field_reduce_once zero reduce 0 || FAILED=1
run_case zisk_secp256k1_field_reduce_once p_minus_one reduce "$PM1_DEC" || FAILED=1
run_case zisk_secp256k1_field_reduce_once p_equal reduce "$P_DEC" || FAILED=1
run_case zisk_secp256k1_field_reduce_once p_plus_five reduce "$P_PLUS_FIVE" || FAILED=1

run_case zisk_secp256k1_field_add one_plus_two add 1 2 || FAILED=1
run_case zisk_secp256k1_field_add p_minus_one_plus_one add "$PM1_DEC" 1 || FAILED=1
run_case zisk_secp256k1_field_add p_minus_one_twice add "$PM1_DEC" "$PM1_DEC" || FAILED=1
run_case zisk_secp256k1_field_add random_fixed add "$RAND_A" "$RAND_B" || FAILED=1

run_case zisk_secp256k1_field_sub five_minus_three sub 5 3 || FAILED=1
run_case zisk_secp256k1_field_sub zero_minus_one sub 0 1 || FAILED=1
run_case zisk_secp256k1_field_sub one_minus_p_minus_one sub 1 "$PM1_DEC" || FAILED=1
run_case zisk_secp256k1_field_sub random_fixed sub "$RAND_A" "$RAND_B" || FAILED=1


run_case zisk_secp256k1_field_mul zero_times_random mul 0 "$RAND_A" || FAILED=1
run_case zisk_secp256k1_field_mul one_times_random mul 1 "$RAND_A" || FAILED=1
run_case zisk_secp256k1_field_mul p_minus_one_squared mul "$PM1_DEC" "$PM1_DEC" || FAILED=1
run_case zisk_secp256k1_field_mul carry_heavy mul "$MAX_DEC" "$MAX_DEC" || FAILED=1
run_case zisk_secp256k1_field_mul random_fixed mul "$RAND_A" "$RAND_B" || FAILED=1

run_case zisk_secp256k1_field_square zero square 0 || FAILED=1
run_case zisk_secp256k1_field_square one square 1 || FAILED=1
run_case zisk_secp256k1_field_square p_minus_one square "$PM1_DEC" || FAILED=1
run_case zisk_secp256k1_field_square carry_heavy square "$MAX_DEC" || FAILED=1
run_case zisk_secp256k1_field_square random_fixed square "$RAND_A" || FAILED=1

run_case zisk_secp256k1_field_inv one inv 1 || FAILED=1
run_case zisk_secp256k1_field_inv random_fixed inv "$RAND_A" || FAILED=1
run_case zisk_secp256k1_field_inv zero inv 0 || FAILED=1

run_case zisk_secp256k1_field_sqrt four sqrt 4 || FAILED=1
run_case zisk_secp256k1_field_sqrt generator_rhs sqrt "$GENERATOR_RHS" || FAILED=1
run_case zisk_secp256k1_field_sqrt non_residue sqrt "$NON_RESIDUE" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: secp256k1 field compare/reduce/add/sub/mul/square/inv/sqrt probes match Python modulo p"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
