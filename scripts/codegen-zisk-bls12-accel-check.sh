#!/usr/bin/env bash
# codegen-zisk-bls12-accel-check.sh -- BLS12-381 ziskemu accelerator probe.
#
# Validates the five BLS12-381-relevant ziskemu syscalls against a
# pure-Python reference:
#
#   * Bls12_381CurveAdd  (csrs 0x80C): G + 2G  = 3G
#   * Bls12_381CurveDbl  (csrs 0x80D): 2*G
#   * Arith384Mod        (csrs 0x80B): (a*b + c) mod p
#   * Bls12_381ComplexAdd/Sub/Mul (csrs 0x80E/0x80F/0x810): Fp2, u^2 = -1
#
# This is the syscall-level gate for the EIP-2537 precompile work
# (0x0b..0x11): if a ziskemu upgrade regresses any of these routes the
# failure shows up here, not as an opaque EEST row.
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

echo "==> emit zisk_bls12_accel_ops ELF"
lake exe codegen --program zisk_bls12_accel_ops --halt linux93 \
  -o gen-out/zisk_bls12_accel_ops

ZISKEMU="$ZISKEMU" python3 - <<'PYSCRIPT'
import os
import struct
import subprocess
import sys

ZISKEMU = os.environ['ZISKEMU']

P = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

# BLS12-381 G1 generator
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

def le48(v):
    return v.to_bytes(48, 'little')

def le_pt(pt):
    return le48(pt[0]) + le48(pt[1])

def le_fp2(c0, c1):
    return le48(c0) + le48(c1)

G = (GX, GY)
G2 = add(G, G)
G3 = add(G2, G)

# Arith384Mod vector: pseudo-random reduced field elements
a = pow(5, 1000, P)
b = pow(7, 999, P)
c = pow(11, 998, P)
d_want = (a * b + c) % P

# Fp2 vectors (u^2 = -1): F1 = a + b*u, F2 = c + d2*u
d2 = pow(13, 997, P)
add_want = ((a + c) % P, (b + d2) % P)
sub_want = ((a - c) % P, (b - d2) % P)
mul_want = ((a * c - b * d2) % P, (a * d2 + b * c) % P)

# Probe input: mode u64 + raw values from 0x40000008 = file byte 0 (the
# bn254 probe convention); ziskemu's -o dump is capped at 256 bytes, so
# the probe runs once per mode. Files must be 8-byte multiples.
payload = le_pt(G) + le_pt(G2) + le48(a) + le48(b) + le48(c) + le_fp2(a, b) + le_fp2(c, d2)

def run(mode):
    blob = struct.pack('<Q', mode) + payload
    blob += b'\x00' * (-len(blob) % 8)
    with open('gen-out/zisk_bls12_accel.input', 'wb') as f:
        f.write(blob)
    r = subprocess.run(
        [ZISKEMU, '-e', 'gen-out/zisk_bls12_accel_ops.elf',
         '-i', 'gen-out/zisk_bls12_accel.input',
         '-o', 'gen-out/zisk_bls12_accel.output',
         '-n', '10000000'],
        capture_output=True, check=False)
    out = open('gen-out/zisk_bls12_accel.output', 'rb').read()
    if len(out) < 240:
        print(f'==> FAIL: mode {mode} produced {len(out)} bytes (rc={r.returncode})')
        print(r.stderr.decode(errors="replace")[-2000:])
        sys.exit(1)
    return out

def rd48(out, off):
    return int.from_bytes(out[off:off+48], 'little')

def rd2(out, off):
    return (rd48(out, off), rd48(out, off + 48))

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

m0 = run(0)
check('Bls12_381CurveAdd  G + 2G = 3G', rd2(m0, 0), G3)
check('Bls12_381CurveDbl  2*G = 2G',    rd2(m0, 96), G2)
m1 = run(1)
check('Arith384Mod        (a*b+c)%p',   rd48(m1, 0), d_want)
check('Bls12_381ComplexAdd F1+F2',      rd2(m1, 48), add_want)
check('Bls12_381ComplexSub F1-F2',      rd2(m1, 144), sub_want)
m2 = run(2)
check('Bls12_381ComplexMul F1*F2',      rd2(m2, 0), mul_want)

if fails:
    print(f'==> FAIL: {fails} BLS12-381 accelerator route(s) mismatched')
    sys.exit(1)
print('==> PASS: all five BLS12-381 ziskemu accelerator routes verified')
PYSCRIPT
