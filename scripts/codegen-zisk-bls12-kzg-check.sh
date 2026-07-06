#!/usr/bin/env bash
# codegen-zisk-bls12-kzg-check.sh -- KZG point-evaluation kernel probe.
#
# Validates the real `zkvm_kzg_point_eval` EIP-4844 kernel against
# execution-specs `ethereum.crypto.kzg.verify_kzg_proof` (the exact
# reference the precompile calls): constant-polynomial proofs (the only
# family constructible without the G1 trusted setup -- proof = the
# infinity point, commitment = [c]_1), proof-false rows, compressed-G1
# decompression rejections (c_flag, infinity payload, x >= p,
# non-residue x), the off-subgroup rejection, and the z/y canonicality
# gates. Each verifying run is gated at -n 4000000000 steps (the 2-pair
# pairing final exponentiation dominates).
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

echo "==> emit zisk_bls12_kzg_point_eval_real ELF"
lake exe codegen --program zisk_bls12_kzg_point_eval_real --halt linux93 \
  -o gen-out/zisk_bls12_kzg_point_eval_real

ZISKEMU="$ZISKEMU" \
  execution-specs/.venv/bin/python3 - <<'PYSCRIPT'
import os
import subprocess
import sys

from py_ecc.bls.g2_primitives import G1_to_pubkey
from py_ecc.optimized_bls12_381 import (
    FQ, G1, multiply, curve_order,
)
from ethereum.crypto.kzg import verify_kzg_proof, BLS_MODULUS

ZISKEMU = os.environ['ZISKEMU']
P = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
N = int(BLS_MODULUS)
INF48 = b'\xc0' + b'\x00' * 47

def compress_g1(pt):
    return G1_to_pubkey(pt)

def run(z, y, commitment, proof, steps=4000000000):
    inp = 'gen-out/bls12_kzg_check.input'
    out = 'gen-out/bls12_kzg_check.output'
    blob = z + y + commitment + proof
    assert len(blob) == 160
    with open(inp, 'wb') as f:
        f.write(blob)
    subprocess.run(
        [ZISKEMU, '-e', 'gen-out/zisk_bls12_kzg_point_eval_real.elf',
         '-i', inp, '-o', out, '-n', str(steps)],
        capture_output=True, check=False)
    blob = open(out, 'rb').read()
    if len(blob) < 9:
        return (None, None)
    return int.from_bytes(blob[0:8], 'little'), blob[8]

def ref(z, y, commitment, proof):
    try:
        return (0, 1 if verify_kzg_proof(commitment, z, y, proof) else 0)
    except Exception:
        return 'invalid'

fails = 0

def check(name, z, y, commitment, proof):
    global fails
    got = run(z, y, commitment, proof)
    want = ref(z, y, commitment, proof)
    # the kernel reports invalid encodings as status 1; the reference
    # raises -- both are KZGProofError at the precompile layer
    ok = (got[0] == 1) if want == 'invalid' else (got == want)
    if ok:
        print(f'    ok: {name} (got {got}, ref {want})')
    else:
        print(f'==> FAIL: {name}')
        print(f'    got:  {got}')
        print(f'    want: {want}')
        fails += 1

def fe(v):
    return int(v).to_bytes(32, 'big')

# constant polynomial p(X) = c: commitment = [c]_1, proof = infinity,
# valid iff y == c (the quotient polynomial is 0)
C7 = compress_g1(multiply(G1, 7))
check('p(X)=7 at z=123, y=7 (true)', fe(123), fe(7), C7, INF48)
check('p(X)=7 at z=0, y=7 (true)', fe(0), fe(7), C7, INF48)
check('p(X)=7, y=8 (false)', fe(123), fe(8), C7, INF48)
check('p(X)=0 (inf commitment), y=0 (true)', fe(5), fe(0), INF48, INF48)
check('p(X)=0 (inf commitment), y=1 (false)', fe(5), fe(1), INF48, INF48)
# a wrong finite proof: pairing must come out false, not crash
check('finite wrong proof (false)', fe(123), fe(7), C7, compress_g1(G1))
# scalar canonicality (bytes_to_bls_field asserts < BLS_MODULUS)
check('z = BLS_MODULUS rejected', fe(N), fe(7), C7, INF48)
check('y = 2^255 rejected', fe(1 << 255), fe(7), C7, INF48)
# compressed-G1 rejections
check('c_flag=0 commitment rejected', fe(1), fe(7), b'\x00' * 48, INF48)
bad_inf = bytearray(INF48); bad_inf[47] = 1
check('non-canonical infinity rejected', fe(1), fe(7), bytes(bad_inf), INF48)
bad_x = bytearray(48)
bad_x[0] = 0x80 | (P >> 376)
rest = (P & ((1 << 376) - 1)).to_bytes(47, 'big')
bad_x[1:] = rest
check('x = p rejected', fe(1), fe(7), bytes(bad_x), INF48)
# smallest x with x^3 + 4 a quadratic non-residue mod p
x = 1
while pow((x * x * x + 4) % P, (P - 1) // 2, P) == 1:
    x += 1
nr = bytearray(48)
nr[0] = 0x80
nr[40:] = x.to_bytes(8, 'big')
check(f'non-residue x={x} rejected', fe(1), fe(7), bytes(nr), INF48)
# off-subgroup commitment (compress a curve point with n*P != inf)
x = 1
off = None
while off is None:
    rhs = (x * x * x + 4) % P
    yc = pow(rhs, (P + 1) // 4, P)
    if yc * yc % P == rhs:
        cand = (FQ(x), FQ(yc), FQ(1))
        if multiply(cand, curve_order)[2] != FQ(0):
            off = cand
    x += 1
check('off-subgroup commitment rejected', fe(1), fe(7), compress_g1(off), INF48)
check('off-subgroup proof rejected', fe(1), fe(7), C7, compress_g1(off))

if fails:
    print(f'==> FAIL: {fails} KZG point-evaluation case(s) mismatched')
    sys.exit(1)
print('==> PASS: KZG point-evaluation kernel matches the execution-specs reference')
PYSCRIPT
