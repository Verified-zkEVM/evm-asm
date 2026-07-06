#!/usr/bin/env bash
# codegen-zisk-bls12-pairing-check.sh -- BLS12-381 pairing kernel probe.
#
# Validates the real `zkvm_bls12_pairing` EIP-2537 kernel against
# py_ecc (the exact library execution-specs computes BLS pairings
# with): e(P, Q)·e(-P, Q) = 1 and bilinearity identities, infinity
# handling, wire-format rejections, and the REAL subgroup checks on
# both sides. Each run is gated at -n 4000000000 steps (the final
# exponentiation dominates at ~4571-bit exponents).
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

echo "==> emit zisk_bls12_pairing_real ELF"
lake exe codegen --program zisk_bls12_pairing_real --halt linux93 \
  -o gen-out/zisk_bls12_pairing_real

ZISKEMU="$ZISKEMU" PYBIN="execution-specs/.venv/bin/python3" \
  execution-specs/.venv/bin/python3 - <<'PYSCRIPT'
import os
import struct
import subprocess
import sys

from py_ecc.optimized_bls12_381 import (
    G1, G2, add, multiply, neg, normalize, curve_order,
)

ZISKEMU = os.environ['ZISKEMU']
P = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

def wire_g1(pt):
    if pt is None:
        return b'\x00' * 128
    x, y = normalize(pt)
    return (b'\x00' * 16 + x.n.to_bytes(48, 'big') +
            b'\x00' * 16 + y.n.to_bytes(48, 'big'))

def wire_g2(pt):
    if pt is None:
        return b'\x00' * 256
    x, y = normalize(pt)
    out = b''
    for c in (x.coeffs[0], x.coeffs[1], y.coeffs[0], y.coeffs[1]):
        out += b'\x00' * 16 + int(c).to_bytes(48, 'big')
    return out

def run(pairs_blob, k, steps=4000000000):
    inp = 'gen-out/bls12_pairing_check.input'
    out = 'gen-out/bls12_pairing_check.output'
    blob = struct.pack('<Q', k) + pairs_blob
    blob += b'\x00' * (-len(blob) % 8)
    with open(inp, 'wb') as f:
        f.write(blob)
    r = subprocess.run(
        [ZISKEMU, '-e', 'gen-out/zisk_bls12_pairing_real.elf', '-i', inp,
         '-o', out, '-n', str(steps)],
        capture_output=True, check=False)
    blob = open(out, 'rb').read()
    if len(blob) < 9:
        return (None, None)
    return int.from_bytes(blob[0:8], 'little'), blob[8]

fails = 0

def check(name, got, want):
    global fails
    if got == want:
        print(f'    ok: {name}')
    else:
        print(f'==> FAIL: {name}')
        print(f'    got:  {got}')
        print(f'    want: {want}')
        fails += 1

P2g1 = multiply(G1, 2)
Q2g2 = multiply(G2, 2)

# e(P,Q)·e(-P,Q) = 1 -> true
check('e(G1,G2)*e(-G1,G2) = 1 (true)',
      run(wire_g1(G1) + wire_g2(G2) + wire_g1(neg(G1)) + wire_g2(G2), 2),
      (0, 1))
# e(2P,Q)·e(-P,2Q)... bilinearity: e(2G1,G2)*e(neg(G1),2G2) = e(G1,G2)^2 * e(G1,G2)^-2 = 1
check('e(2G1,G2)*e(-G1,2G2) = 1 (true)',
      run(wire_g1(P2g1) + wire_g2(G2) + wire_g1(neg(G1)) + wire_g2(Q2g2), 2),
      (0, 1))
# single pair: e(G1,G2) != 1 -> false
check('e(G1,G2) alone (false)',
      run(wire_g1(G1) + wire_g2(G2), 1),
      (0, 0))
# infinity pairs contribute 1
check('e(inf,G2) = 1 (true)',
      run(wire_g1(None) + wire_g2(G2), 1),
      (0, 1))
check('e(G1,inf) = 1 (true)',
      run(wire_g1(G1) + wire_g2(None), 1),
      (0, 1))
check('e(inf,G2)*e(G1,G2) (false)',
      run(wire_g1(None) + wire_g2(G2) + wire_g1(G1) + wire_g2(G2), 2),
      (0, 0))
# rejections
bad_pad = b'\x01' + (wire_g1(G1) + wire_g2(G2))[1:]
check('nonzero pad rejected', run(bad_pad, 1)[0], 1)
bad_range = (b'\x00' * 16 + P.to_bytes(48, 'big') +
             wire_g1(G1)[64:]) + wire_g2(G2)
check('x >= p rejected', run(bad_range, 1)[0], 1)
off_curve = (b'\x00' * 16 + (1).to_bytes(48, 'big')) * 2 + wire_g2(G2)
check('off-curve G1 rejected', run(off_curve, 1)[0], 1)

# off-subgroup G1 (real cofactor): scan a curve point with n*P != inf
def sqrt_p(a):
    a %= P
    r = pow(a, (P + 1) // 4, P)
    return r if r * r % P == a else None

x = 1
Qoff = None
while Qoff is None:
    y = sqrt_p(x * x * x + 4)
    if y is not None:
        from py_ecc.optimized_bls12_381 import FQ
        cand = (FQ(x), FQ(y), FQ(1))
        if multiply(cand, curve_order)[2] != FQ(0):
            Qoff = cand
    x += 1
check('off-subgroup G1 rejected', run(wire_g1(Qoff) + wire_g2(G2), 1)[0], 1)

if fails:
    print(f'==> FAIL: {fails} BLS12-381 pairing case(s) mismatched')
    sys.exit(1)
print('==> PASS: BLS12-381 pairing kernel matches the py_ecc reference')
PYSCRIPT
