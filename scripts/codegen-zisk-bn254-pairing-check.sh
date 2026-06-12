#!/usr/bin/env bash
# codegen-zisk-bn254-pairing-check.sh -- BN254 (alt_bn128) ecPairing kernel
# probe (EIP-197).
#
# Validates `zkvm_bn254_pairing` against py_ecc (the exact library
# execution-specs computes the pairing with): canonical vectors (empty
# input, e(G1,G2) != 1, e(P,Q)·e(-P,Q) = 1, infinity inputs), bilinearity
# with small and near-order scalars, and the rejection paths (off-curve
# G1/G2, coordinate >= p, G2 outside the order-n subgroup).
#
# Runs are gated at -n 1000000000 steps (the stateless budget); the
# kernel measures ~40M steps fixed (final exponentiation + denominator
# inverse) plus ~22M per pair.
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

PYBIN="execution-specs/.venv/bin/python3"
if ! "$PYBIN" -c "import py_ecc" >/dev/null 2>&1; then
  echo "py_ecc not importable from $PYBIN (execution-specs venv)" >&2
  exit 1
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

program="zisk_bn254_pairing_real"
echo "==> emit ${program} ELF"
lake exe codegen --program "$program" --halt linux93 -o "gen-out/${program}"

ZISKEMU="$ZISKEMU" "$PYBIN" - <<'PYSCRIPT'
import os
import subprocess
import sys

from py_ecc.optimized_bn128 import optimized_curve as oc

ZISKEMU = os.environ['ZISKEMU']
P = 21888242871839275222246405745257275088696311157297823662689037894645226208583
FQ2 = oc.FQ2
G1, G2 = oc.G1, oc.G2

def g1be(pt):
    if pt is None:
        return b'\x00' * 64
    x, y = oc.normalize(pt)
    return int(x).to_bytes(32, 'big') + int(y).to_bytes(32, 'big')

def g2be(pt):
    if pt is None:
        return b'\x00' * 128
    x, y = oc.normalize(pt)
    return (int(x.coeffs[1]).to_bytes(32, 'big') + int(x.coeffs[0]).to_bytes(32, 'big') +
            int(y.coeffs[1]).to_bytes(32, 'big') + int(y.coeffs[0]).to_bytes(32, 'big'))

def runraw(k, data):
    inp = 'gen-out/bn254_pairing_check.input'
    out = 'gen-out/bn254_pairing_check.output'
    with open(inp, 'wb') as f:
        f.write(k.to_bytes(8, 'little') + data)
    subprocess.run([ZISKEMU, '-e', f'gen-out/zisk_bn254_pairing_real.elf',
                    '-i', inp, '-o', out, '-n', '1000000000'],
                   capture_output=True, check=False)
    blob = open(out, 'rb').read()
    return int.from_bytes(blob[0:8], 'little'), blob[8]

def fp_sqrt(a):
    r = pow(a, (P + 1) // 4, P)
    return r if r * r % P == a % P else None

def fp2_sqrt(c):
    a, b = int(c.coeffs[0]), int(c.coeffs[1])
    if b == 0:
        r = fp_sqrt(a)
        if r is not None:
            return FQ2([r, 0])
        r = fp_sqrt((-a) % P)
        return FQ2([0, r]) if r is not None else None
    norm = fp_sqrt((a * a + b * b) % P)
    if norm is None:
        return None
    inv2 = pow(2, P - 2, P)
    for n in (norm, (-norm) % P):
        x0 = fp_sqrt((a + n) * inv2 % P)
        if x0 is None:
            continue
        cand = FQ2([x0, b * pow(2 * x0, P - 2, P) % P])
        if cand * cand == c:
            return cand
    return None

fails = 0

def check(name, got, want):
    global fails
    if got[:len(want)] == want:
        print(f'    ok: {name}')
    else:
        print(f'==> FAIL: {name}  got={got} want={want}')
        fails += 1

check('empty input -> true',         runraw(0, b''), (0, 1))
check('e(G1,G2) != 1',               runraw(1, g1be(G1) + g2be(G2)), (0, 0))
check('e(G1,G2) e(-G1,G2) == 1',     runraw(2, g1be(G1) + g2be(G2) + g1be(oc.neg(G1)) + g2be(G2)), (0, 1))
check('e(G1,inf) == 1',              runraw(1, g1be(G1) + b'\x00' * 128), (0, 1))
check('e(inf,G2) == 1',              runraw(1, b'\x00' * 64 + g2be(G2)), (0, 1))
pairs = (g1be(oc.multiply(G1, 5)) + g2be(oc.multiply(G2, 7)) +
         g1be(oc.neg(oc.multiply(G1, 35))) + g2be(G2))
check('e(5G1,7G2) e(-35G1,G2) == 1', runraw(2, pairs), (0, 1))
n = oc.curve_order
a, b = 0x1234567890abcdef, n - 3
pairs = (g1be(oc.multiply(G1, a)) + g2be(oc.multiply(G2, b)) +
         g1be(oc.neg(oc.multiply(G1, (a * b) % n))) + g2be(G2))
check('near-order bilinearity == 1', runraw(2, pairs), (0, 1))
bad = (1).to_bytes(32, 'big') + (1).to_bytes(32, 'big')
check('off-curve G1 rejected',  runraw(1, bad + g2be(G2)), (1,))
check('G2 coord = p rejected',  runraw(1, g1be(G1) + P.to_bytes(32, 'big') + g2be(G2)[32:]), (1,))
g2 = bytearray(g2be(G2)); g2[-1] ^= 1
check('off-twist G2 rejected',  runraw(1, g1be(G1) + bytes(g2)), (1,))
x = FQ2([1, 0]); pt = None
while pt is None:
    y = fp2_sqrt(x * x * x + oc.b2)
    if y is not None:
        cand = (x, y, FQ2([1, 0]))
        if not oc.is_inf(oc.multiply(cand, oc.curve_order)):
            pt = cand
    x = x + FQ2([1, 0])
check('non-subgroup G2 rejected', runraw(1, g1be(G1) + g2be(pt)), (1,))

if fails:
    print(f'==> FAIL: {fails} BN254 pairing case(s) mismatched')
    sys.exit(1)
print('==> PASS: BN254 ecPairing kernel matches the EIP-197 / py_ecc reference')
PYSCRIPT
