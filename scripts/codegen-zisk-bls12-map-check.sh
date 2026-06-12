#!/usr/bin/env bash
# codegen-zisk-bls12-map-check.sh -- BLS12-381 map_fp_to_g1 / map_fp2_to_g2.
#
# Validates the real `zkvm_bls12_map_fp_to_g1` / `zkvm_bls12_map_fp2_to_g2`
# EIP-2537 kernels against py_ecc (map_to_curve_G1/G2 + clear_cofactor),
# including the SSWU exceptional/non-square branches, sgn0 matching,
# t = 0, and wire rejections.
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

for program in zisk_bls12_map_fp_to_g1_real zisk_bls12_map_fp2_to_g2_real; do
  echo "==> emit ${program} ELF"
  lake exe codegen --program "$program" --halt linux93 -o "gen-out/${program}"
done

ZISKEMU="$ZISKEMU" execution-specs/.venv/bin/python3 - <<'PYSCRIPT'
import os
import subprocess
import sys

from py_ecc.bls.hash_to_curve import (
    clear_cofactor_G1, clear_cofactor_G2, map_to_curve_G1, map_to_curve_G2,
)
from py_ecc.optimized_bls12_381 import FQ, FQ2, normalize

ZISKEMU = os.environ['ZISKEMU']
P = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

def wire_fp(v):
    return b'\x00' * 16 + int(v).to_bytes(48, 'big')

def run(elf, data, out_len):
    inp = 'gen-out/bls12_map_check.input'
    out = 'gen-out/bls12_map_check.output'
    blob = data + b'\x00' * (-len(data) % 8)
    with open(inp, 'wb') as f:
        f.write(blob)
    subprocess.run(
        [ZISKEMU, '-e', f'gen-out/{elf}.elf', '-i', inp, '-o', out,
         '-n', '1000000000'],
        capture_output=True, check=False)
    blob = open(out, 'rb').read()
    return int.from_bytes(blob[0:8], 'little'), blob[8:8+out_len]

def compact_g1(pt):
    if pt[2] == FQ(0):
        return b'\x00' * 96
    x, y = normalize(pt)
    return x.n.to_bytes(48, 'big') + y.n.to_bytes(48, 'big')

def compact_g2(pt):
    if pt[2] == FQ2([0, 0]):
        return b'\x00' * 192
    x, y = normalize(pt)
    return (int(x.coeffs[0]).to_bytes(48, 'big') + int(x.coeffs[1]).to_bytes(48, 'big') +
            int(y.coeffs[0]).to_bytes(48, 'big') + int(y.coeffs[1]).to_bytes(48, 'big'))

fails = 0
def check(name, got, want):
    global fails
    if got == want:
        print(f'    ok: {name}')
    else:
        print(f'==> FAIL: {name}')
        print(f'    got:  {got if not isinstance(got, tuple) else (got[0], got[1].hex())}')
        print(f'    want: {want if not isinstance(want, tuple) else (want[0], want[1].hex())}')
        fails += 1

G1E = 'zisk_bls12_map_fp_to_g1_real'
for t in [0, 1, 2, 5, 0xdeadbeef, P - 1, pow(7, 99, P)]:
    want = compact_g1(clear_cofactor_G1(map_to_curve_G1(FQ(t))))
    check(f'map_fp_to_g1 t={hex(t)[:14]}', run(G1E, wire_fp(t), 96), (0, want))
check('map_fp_to_g1 nonzero pad rejected',
      run(G1E, b'\x01' + wire_fp(1)[1:], 96)[0], 1)
check('map_fp_to_g1 t=p rejected', run(G1E, wire_fp(P), 96)[0], 1)

G2E = 'zisk_bls12_map_fp2_to_g2_real'
for c0, c1 in [(0, 0), (1, 0), (0, 1), (2, 3), (P - 1, P - 2), (pow(5, 77, P), pow(3, 88, P))]:
    want = compact_g2(clear_cofactor_G2(map_to_curve_G2(FQ2([c0, c1]))))
    check(f'map_fp2_to_g2 t=({hex(c0)[:10]},{hex(c1)[:10]})',
          run(G2E, wire_fp(c0) + wire_fp(c1), 192), (0, want))
check('map_fp2_to_g2 nonzero pad rejected',
      run(G2E, b'\x01' + (wire_fp(1) + wire_fp(0))[1:], 192)[0], 1)
check('map_fp2_to_g2 c1=p rejected', run(G2E, wire_fp(1) + wire_fp(P), 192)[0], 1)

if fails:
    print(f'==> FAIL: {fails} BLS12-381 map case(s) mismatched')
    sys.exit(1)
print('==> PASS: BLS12-381 map kernels match the py_ecc reference')
PYSCRIPT
