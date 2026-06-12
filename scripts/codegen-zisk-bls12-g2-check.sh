#!/usr/bin/env bash
# codegen-zisk-bls12-g2-check.sh -- BLS12-381 G2 ADD/MSM kernel probes.
#
# Validates the real `zkvm_bls12_g2_add` / `zkvm_bls12_g2_msm` EIP-2537
# kernels against a pure-Python Fp2 reference: wire decode (4 padded
# field elements per point), on-curve y^2 = x^3 + 4(u+1), infinity,
# software chord/tangent over Fp2 (the complex accelerators provide
# Fp2 add/sub/mul; the inverse is a Fermat chain on Arith384Mod),
# the REAL order-n subgroup check for MSM inputs, and raw scalars.
#
# Each run is gated at -n 1000000000 steps.
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

for program in zisk_bls12_g2_add_real zisk_bls12_g2_msm_real; do
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

# Fp2 = Fp[u]/(u^2+1); elements are (c0, c1) tuples
def f2add(a, b): return ((a[0]+b[0]) % P, (a[1]+b[1]) % P)
def f2sub(a, b): return ((a[0]-b[0]) % P, (a[1]-b[1]) % P)
def f2mul(a, b):
    return ((a[0]*b[0] - a[1]*b[1]) % P, (a[0]*b[1] + a[1]*b[0]) % P)
def f2neg(a): return ((-a[0]) % P, (-a[1]) % P)
def f2inv(a):
    n = (a[0]*a[0] + a[1]*a[1]) % P
    ninv = pow(n, P-2, P)
    return (a[0]*ninv % P, (-a[1]) % P * ninv % P)

B2 = (4, 4)

def add(p, q):
    if p is None: return q
    if q is None: return p
    x1, y1 = p; x2, y2 = q
    if x1 == x2:
        if f2add(y1, y2) == (0, 0): return None
        l = f2mul(f2mul((3,0), f2mul(x1, x1)), f2inv(f2add(y1, y1)))
    else:
        l = f2mul(f2sub(y2, y1), f2inv(f2sub(x2, x1)))
    x3 = f2sub(f2sub(f2mul(l, l), x1), x2)
    return (x3, f2sub(f2mul(l, f2sub(x1, x3)), y1))

def mul(p, k):
    r = None
    for i in range(max(k.bit_length(), 1) - 1, -1, -1):
        r = add(r, r)
        if (k >> i) & 1:
            r = add(r, p)
    return r

# G2 generator (EIP-2537 / py_ecc G2)
G2X = (0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8,
       0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e)
G2Y = (0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801,
       0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be)
G = (G2X, G2Y)
G2pt = add(G, G)
G3pt = add(G2pt, G)
K = 0x33d8fa3e98a567a9c45ed4718e23bb6dd23172a0ce91d3b27d061f40d23a8b75

def wire_felt(v):
    return b'\x00' * 16 + v.to_bytes(48, 'big')

def wire_pt(pt):
    if pt is None:
        return b'\x00' * 256
    return (wire_felt(pt[0][0]) + wire_felt(pt[0][1]) +
            wire_felt(pt[1][0]) + wire_felt(pt[1][1]))

def compact(pt):
    if pt is None:
        return b'\x00' * 192
    return (pt[0][0].to_bytes(48, 'big') + pt[0][1].to_bytes(48, 'big') +
            pt[1][0].to_bytes(48, 'big') + pt[1][1].to_bytes(48, 'big'))

# An off-subgroup G2 curve point: scan x, taking the explicit Fp2 sqrt
# for Fp[i] with p % 4 == 3: for c = a + bi, s = sqrt(a^2+b^2),
# t = (a+s)/2 (or (a-s)/2), y = sqrt(t) + i*b/(2*sqrt(t)). A random
# curve point is off-subgroup with overwhelming probability (huge h2).
def sqrt_p(a):
    a %= P
    r = pow(a, (P + 1) // 4, P)
    return r if r * r % P == a else None

def fp2_sqrt(c):
    a, b = c
    if b == 0:
        r = sqrt_p(a)
        return (r, 0) if r is not None else None
    s = sqrt_p((a*a + b*b) % P)
    if s is None:
        return None
    inv2 = pow(2, P - 2, P)
    for t in ((a + s) * inv2 % P, (a - s) * inv2 % P):
        u = sqrt_p(t)
        if u is not None and u != 0:
            y = (u, b * pow(2 * u, P - 2, P) % P)
            if f2mul(y, y) == c:
                return y
    return None

Q_off = None
xc = 1
while Q_off is None and xc < 100:
    x = (xc, 1)
    rhs = f2add(f2mul(f2mul(x, x), x), B2)
    y = fp2_sqrt(rhs)
    if y is not None and mul((x, y), N) is not None:
        Q_off = (x, y)
    xc += 1

def run(elf, data):
    inp = 'gen-out/bls12_g2_check.input'
    out = 'gen-out/bls12_g2_check.output'
    blob = data + b'\x00' * (-len(data) % 8)
    with open(inp, 'wb') as f:
        f.write(blob)
    subprocess.run(
        [ZISKEMU, '-e', f'gen-out/{elf}.elf', '-i', inp, '-o', out,
         '-n', '1000000000'],
        capture_output=True, check=False)
    blob = open(out, 'rb').read()
    return int.from_bytes(blob[0:8], 'little'), blob[8:200]

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

A = 'zisk_bls12_g2_add_real'
check('g2add G+2G = 3G',            run(A, wire_pt(G) + wire_pt(G2pt)), (0, compact(G3pt)))
check('g2add G+G = 2G (double)',    run(A, wire_pt(G) + wire_pt(G)), (0, compact(G2pt)))
check('g2add inf+G = G',            run(A, wire_pt(None) + wire_pt(G)), (0, compact(G)))
check('g2add G+inf = G',            run(A, wire_pt(G) + wire_pt(None)), (0, compact(G)))
check('g2add inf+inf = inf',        run(A, wire_pt(None) * 2), (0, compact(None)))
negG = (G[0], f2neg(G[1]))
check('g2add G+(-G) = inf',         run(A, wire_pt(G) + wire_pt(negG)), (0, compact(None)))
bad_pad = b'\x01' + wire_pt(G)[1:]
check('g2add nonzero pad rejected', run(A, bad_pad + wire_pt(G))[0], 1)
bad_range = wire_felt(P) + wire_pt(G)[64:]
check('g2add x.c0=p rejected',      run(A, bad_range + wire_pt(G))[0], 1)
off_curve = wire_felt(1) + wire_felt(1) + wire_felt(1) + wire_felt(1)
check('g2add off-curve rejected',   run(A, off_curve + wire_pt(G))[0], 1)

def msm_input(pairs):
    blob = struct.pack('<Q', len(pairs))
    for pt, k in pairs:
        blob += wire_pt(pt) + k.to_bytes(32, 'big')
    return blob

M = 'zisk_bls12_g2_msm_real'
check('g2msm G*2 = 2G',             run(M, msm_input([(G, 2)])), (0, compact(G2pt)))
check('g2msm G*0 = inf',            run(M, msm_input([(G, 0)])), (0, compact(None)))
check('g2msm inf*5 = inf',          run(M, msm_input([(None, 5)])), (0, compact(None)))
check('g2msm G*k (random scalar)',  run(M, msm_input([(G, K)])), (0, compact(mul(G, K))))
check('g2msm G*n = inf (order)',    run(M, msm_input([(G, N)])), (0, compact(None)))
check('g2msm 2G*3 + G*2 = 8G',      run(M, msm_input([(G2pt, 3), (G, 2)])), (0, compact(mul(G, 8))))
check('g2msm off-curve rejected',   run(M, msm_input([(((1,1),(1,1)), 2)]))[0], 1)
if Q_off is not None:
    check('g2msm off-subgroup rejected', run(M, msm_input([(Q_off, 2)]))[0], 1)
else:
    print('    skip: no off-subgroup witness found (sqrt scan exhausted)')

if fails:
    print(f'==> FAIL: {fails} BLS12-381 G2 kernel case(s) mismatched')
    sys.exit(1)
print('==> PASS: BLS12-381 G2 ADD/MSM kernels match the EIP-2537 reference')
PYSCRIPT
