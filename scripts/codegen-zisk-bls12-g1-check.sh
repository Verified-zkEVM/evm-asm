#!/usr/bin/env bash
# codegen-zisk-bls12-g1-check.sh -- BLS12-381 G1 ADD/MSM kernel probes.
#
# Validates the real `zkvm_bls12_g1_add` / `zkvm_bls12_g1_msm` EIP-2537
# precompile kernels against a pure-Python reference: wire decode
# (64-byte padded field elements: pad-zero + coord < p), on-curve
# (y^2 = x^3 + 4), infinity (all-zero) handling, the accelerator-excluded
# affine cases (doubling, P + (-P)), the REAL order-n subgroup check for
# MSM inputs (the G1 cofactor is not 1 — x*G with x = cofactor-cleared
# vs a curve point OUTSIDE the subgroup), and raw 32-byte scalars.
#
# Each run is gated at -n 1000000000 steps, so a perf regression past
# the stateless step budget fails the check.
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

for program in zisk_bls12_g1_add_real zisk_bls12_g1_msm_real; do
  echo "==> emit ${program} ELF"
  lake exe codegen --program "$program" --halt linux93 -o "gen-out/${program}"
done

ZISKEMU="$ZISKEMU" python3 - <<'PYSCRIPT'
import os
import struct
import subprocess
import sys

ZISKEMU = os.environ['ZISKEMU']

P = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
N = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

GX = 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb
GY = 0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1

def inv(a):
    return pow(a, P - 2, P)

def add(p, q):
    if p is None: return q
    if q is None: return p
    x1, y1 = p; x2, y2 = q
    if x1 == x2:
        if (y1 + y2) % P == 0: return None
        l = (3 * x1 * x1) * inv(2 * y1) % P
    else:
        l = (y2 - y1) * inv(x2 - x1) % P
    x3 = (l * l - x1 - x2) % P
    return (x3, (l * (x1 - x3) - y1) % P)

def mul(p, k):
    r = None
    for i in range(k.bit_length() - 1, -1, -1):
        r = add(r, r)
        if (k >> i) & 1:
            r = add(r, p)
    return r

def wire_felt(v):
    return b'\x00' * 16 + v.to_bytes(48, 'big')

def wire_pt(pt):
    if pt is None:
        return b'\x00' * 128
    return wire_felt(pt[0]) + wire_felt(pt[1])

def compact(pt):
    if pt is None:
        return b'\x00' * 96
    return pt[0].to_bytes(48, 'big') + pt[1].to_bytes(48, 'big')

G = (GX, GY)
G2 = add(G, G)
G3 = add(G2, G)
K = 0x2a8f1c64d5e7b30912d83f6a4be09c7755aa31e0cd4f29886bb07d5a93e16f04

# A curve point OUTSIDE the order-n subgroup: y^2 = x^3 + 4 with x
# small; search for a solution and verify n*Q != inf.
def sqrt_p(a):
    # p % 4 == 3
    r = pow(a, (P + 1) // 4, P)
    return r if r * r % P == a else None

Q_off = None
x = 1
while Q_off is None:
    y = sqrt_p((x * x * x + 4) % P)
    if y is not None:
        cand = (x, y)
        if mul(cand, N) is not None:
            Q_off = cand
    x += 1

def run(elf, data):
    inp = 'gen-out/bls12_g1_check.input'
    out = 'gen-out/bls12_g1_check.output'
    blob = data + b'\x00' * (-len(data) % 8)
    with open(inp, 'wb') as f:
        f.write(blob)
    subprocess.run(
        [ZISKEMU, '-e', f'gen-out/{elf}.elf', '-i', inp, '-o', out,
         '-n', '1000000000'],
        capture_output=True, check=False)
    blob = open(out, 'rb').read()
    return int.from_bytes(blob[0:8], 'little'), blob[8:104]

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

A = 'zisk_bls12_g1_add_real'
check('add G+2G = 3G (accelerator path)',   run(A, wire_pt(G) + wire_pt(G2)), (0, compact(G3)))
check('add G+G = 2G (double path)',         run(A, wire_pt(G) + wire_pt(G)), (0, compact(G2)))
check('add inf+G = G',                      run(A, wire_pt(None) + wire_pt(G)), (0, compact(G)))
check('add G+inf = G',                      run(A, wire_pt(G) + wire_pt(None)), (0, compact(G)))
check('add inf+inf = inf',                  run(A, wire_pt(None) * 2), (0, compact(None)))
check('add G+(-G) = inf',                   run(A, wire_pt(G) + wire_pt((GX, P - GY))), (0, compact(None)))
check('add off-subgroup point accepted (no subgroup check)',
      run(A, wire_pt(Q_off) + wire_pt(Q_off))[0], 0)
bad_pad = b'\x01' + b'\x00' * 15 + GX.to_bytes(48, 'big') + wire_felt(GY)
check('add nonzero pad rejected',  run(A, bad_pad + wire_pt(G))[0], 1)
check('add x=p rejected',          run(A, wire_felt(P) + wire_felt(GY) + wire_pt(G))[0], 1)
check('add off-curve rejected',    run(A, wire_felt(1) + wire_felt(1) + wire_pt(G))[0], 1)

def msm_input(pairs):
    blob = struct.pack('<Q', len(pairs))
    for pt, k in pairs:
        blob += wire_pt(pt) + k.to_bytes(32, 'big')
    return blob

M = 'zisk_bls12_g1_msm_real'
check('msm G*2 = 2G',               run(M, msm_input([(G, 2)])), (0, compact(G2)))
check('msm G*0 = inf',              run(M, msm_input([(G, 0)])), (0, compact(None)))
check('msm inf*5 = inf',            run(M, msm_input([(None, 5)])), (0, compact(None)))
check('msm G*k (random scalar)',    run(M, msm_input([(G, K)])), (0, compact(mul(G, K))))
check('msm G*n = inf (order)',      run(M, msm_input([(G, N)])), (0, compact(None)))
check('msm 2G*3 + G*2 = 8G',        run(M, msm_input([(G2, 3), (G, 2)])), (0, compact(mul(G, 8))))
check('msm G*5 + (-G)*5 = inf',     run(M, msm_input([(G, 5), ((GX, P - GY), 5)])), (0, compact(None)))
check('msm off-subgroup rejected',  run(M, msm_input([(Q_off, 2)]))[0], 1)
check('msm off-curve rejected',     run(M, msm_input([((1, 1), 2)]))[0], 1)

if fails:
    print(f'==> FAIL: {fails} BLS12-381 G1 kernel case(s) mismatched')
    sys.exit(1)
print('==> PASS: BLS12-381 G1 ADD/MSM kernels match the EIP-2537 reference')
PYSCRIPT
