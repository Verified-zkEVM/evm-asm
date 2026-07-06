#!/usr/bin/env bash
# codegen-zisk-secp256k1-recover-check.sh -- secp256k1 curve-level R-point
# recovery probe (bead evm-asm-mcogi.5.3.4).
#
# Decompresses R = (x, y) from a signature r value and recovery id and checks
# the result against an independent Python secp256k1 reference (the same
# decompression execution-specs secp256k1_recover relies on). Covers a valid
# generator-point vector for both y parities, a non-residue r (status 1), and
# an out-of-range candidate x (status 2).
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

PROGRAM=zisk_secp256k1_recover_r
echo "==> emit ${PROGRAM} ELF"
lake exe codegen --program "$PROGRAM" --halt linux93 -o "gen-out/${PROGRAM}"

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" r="$2" recid="$3"
  local in_file="$REPO_ROOT/gen-out/${PROGRAM}_${name}.input"
  local out_file="$REPO_ROOT/gen-out/${PROGRAM}_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/${PROGRAM}_${name}.expected"
  local log_file="$REPO_ROOT/gen-out/${PROGRAM}_${name}.emu.log"

  python3 - "$r" "$recid" "$in_file" "$exp_file" <<'PYSCRIPT'
import struct
import sys

r_s, recid_s, in_path, exp_path = sys.argv[1:]
r = int(r_s, 0)
recid = int(recid_s, 0)

P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
B = 7


def u256(x):
    return (x % (1 << 256)).to_bytes(32, 'big')


# Input layout mirrors the field probes: operand r at file offset 0
# (guest address 0x40000008), recid as little-endian u64 at file offset 32
# (guest address 0x40000028, read via `ld a1, 40(a3)`).
with open(in_path, 'wb') as f:
    f.write(u256(r))
    f.write(struct.pack('<Q', recid))

# Reference decompression.
x = r + (N if (recid & 2) else 0)
if x >= P:
    expected = struct.pack('<Q', 2)
else:
    rhs = (pow(x, 3, P) + B) % P
    y = pow(rhs, (P + 1) // 4, P)
    if (y * y) % P != rhs:
        expected = struct.pack('<Q', 1)
    else:
        if (y & 1) != (recid & 1):
            y = (P - y) % P
        expected = struct.pack('<Q', 0) + u256(x) + u256(y)

with open(exp_path, 'wb') as f:
    f.write(expected)
PYSCRIPT

  "$ZISKEMU" -e "gen-out/${PROGRAM}.elf" -i "$in_file" -o "$out_file" \
    -n 1000000000 >"$log_file" 2>&1 || true

  local exp_size actual expected
  exp_size="$(stat -c%s "$exp_file")"
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-44s OK\n" "${PROGRAM}/${name}"
    return 0
  else
    printf "  %-44s FAIL\n    expected: %s\n    actual:   %s\n" \
      "${PROGRAM}/${name}" "$expected" "$actual"
    return 1
  fi
}

GX="0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"
# A small r whose x^3+7 is a quadratic non-residue mod p (status 1).
NON_RESIDUE_R="$(python3 - <<'PYSCRIPT'
P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
B = 7
for r in range(1, 10000):
    rhs = (pow(r, 3, P) + B) % P
    if pow(rhs, (P - 1) // 2, P) == P - 1:
        print(r)
        break
PYSCRIPT
)"
# Candidate x = r + n exceeds p when recid bit 1 is set on a large r (status 2).
P_MINUS_ONE="$(python3 - <<'PYSCRIPT'
print(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F - 1)
PYSCRIPT
)"

FAILED=0

# Generator point: r = Gx recovers R = G for parity 0, the conjugate for parity 1.
run_case generator_parity0 "$GX" 0 || FAILED=1
run_case generator_parity1 "$GX" 1 || FAILED=1
# Non-residue r: no curve point, status 1.
run_case non_residue "$NON_RESIDUE_R" 0 || FAILED=1
# recid high bit pushes x = r + n past p: status 2.
run_case out_of_range "$P_MINUS_ONE" 2 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: secp256k1 recover_r probes match Python reference decompression"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
