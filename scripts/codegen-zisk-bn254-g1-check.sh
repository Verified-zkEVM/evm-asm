#!/usr/bin/env bash
# codegen-zisk-bn254-g1-check.sh -- BN254 (alt_bn128) ecAdd/ecMul kernel probes.
#
# Validates the real `zkvm_bn254_g1_add` / `zkvm_bn254_g1_mul` precompile
# kernels (EIP-196 semantics: coordinate range + on-curve validation,
# (0,0) infinity encoding, raw 256-bit scalar) against a pure-Python
# reference on the canonical (1,2) generator vectors plus the edge cases
# the ziskemu Bn254CurveAdd/Dbl accelerators exclude (infinity inputs,
# equal-x doubling, P + (-P), off-curve and out-of-range rejections).
#
# Each run is gated at -n 1000000000 steps, so a perf regression past the
# stateless step budget fails the check.
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

for program in zisk_bn254_g1_add_real zisk_bn254_g1_mul_real; do
  echo "==> emit ${program} ELF"
  lake exe codegen --program "$program" --halt linux93 -o "gen-out/${program}"
done

ZISKEMU="$ZISKEMU" python3 - <<'PYSCRIPT'
import os
import subprocess
import sys

P = 21888242871839275222246405745257275088696311157297823662689037894645226208583
N = 21888242871839275222246405745257275088548364400416034343698204186575808495617

def inv(a):
    return pow(a, P - 2, P)

def add(p, q):
    if p is None:
        return q
    if q is None:
        return p
    x1, y1 = p
    x2, y2 = q
    if x1 == x2:
        if (y1 + y2) % P == 0:
            return None
        l = (3 * x1 * x1) * inv(2 * y1) % P
    else:
        l = (y2 - y1) * inv(x2 - x1) % P
    x3 = (l * l - x1 - x2) % P
    return (x3, (l * (x1 - x3) - y1) % P)

def mul(p, k):
    r = None
    for i in range(255, -1, -1):
        r = add(r, r)
        if (k >> i) & 1:
            r = add(r, p)
    return r

def enc(pt):
    if pt is None:
        return b'\x00' * 64
    return pt[0].to_bytes(32, 'big') + pt[1].to_bytes(32, 'big')

ZISKEMU = os.environ['ZISKEMU']
G = (1, 2)
G2 = add(G, G)
G3 = add(G2, G)
K = 0x183227397098d014dc2822db40c0ac2ecbc0b548b438e5469e10460b6c3e7ea4

def run(elf, data):
    inp = 'gen-out/bn254_g1_check.input'
    out = 'gen-out/bn254_g1_check.output'
    with open(inp, 'wb') as f:
        f.write(data)
    subprocess.run(
        [ZISKEMU, '-e', f'gen-out/{elf}.elf', '-i', inp, '-o', out,
         '-n', '1000000000'],
        capture_output=True, check=False)
    blob = open(out, 'rb').read()
    return int.from_bytes(blob[0:8], 'little'), blob[8:72]

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

A = 'zisk_bn254_g1_add_real'
check('add (1,2)+(1,2) = 2G (double path)', run(A, enc(G) + enc(G)), (0, enc(G2)))
check('add G+2G = 3G (accelerator path)',   run(A, enc(G) + enc(G2)), (0, enc(G3)))
check('add inf+G = G',                      run(A, b'\x00' * 64 + enc(G)), (0, enc(G)))
check('add G+inf = G',                      run(A, enc(G) + b'\x00' * 64), (0, enc(G)))
check('add inf+inf = inf',                  run(A, b'\x00' * 128), (0, b'\x00' * 64))
check('add G+(-G) = inf',                   run(A, enc(G) + enc((1, P - 2))), (0, b'\x00' * 64))
bad = (1).to_bytes(32, 'big') + (1).to_bytes(32, 'big')
check('add off-curve p1 rejected',  run(A, bad + enc(G))[0], 1)
check('add off-curve p2 rejected',  run(A, enc(G) + bad)[0], 1)
check('add x=p rejected',           run(A, P.to_bytes(32, 'big') + (2).to_bytes(32, 'big') + enc(G))[0], 1)
check('add y=p rejected',           run(A, (1).to_bytes(32, 'big') + P.to_bytes(32, 'big') + enc(G))[0], 1)

M = 'zisk_bn254_g1_mul_real'
check('mul G*2 = 2G',               run(M, enc(G) + (2).to_bytes(32, 'big')), (0, enc(G2)))
check('mul G*0 = inf',              run(M, enc(G) + (0).to_bytes(32, 'big')), (0, b'\x00' * 64))
check('mul inf*5 = inf',            run(M, b'\x00' * 64 + (5).to_bytes(32, 'big')), (0, b'\x00' * 64))
check('mul G*k (random 256-bit k)', run(M, enc(G) + K.to_bytes(32, 'big')), (0, enc(mul(G, K))))
check('mul G*(2^256-1)',            run(M, enc(G) + (2**256 - 1).to_bytes(32, 'big')), (0, enc(mul(G, 2**256 - 1))))
check('mul G*order = inf',          run(M, enc(G) + N.to_bytes(32, 'big')), (0, b'\x00' * 64))
check('mul G*(order+1) = G',        run(M, enc(G) + (N + 1).to_bytes(32, 'big')), (0, enc(G)))
check('mul off-curve rejected',     run(M, bad + (2).to_bytes(32, 'big'))[0], 1)

if fails:
    print(f'==> FAIL: {fails} BN254 G1 kernel case(s) mismatched')
    sys.exit(1)
print('==> PASS: BN254 ecAdd/ecMul kernels match the EIP-196 reference')
PYSCRIPT
