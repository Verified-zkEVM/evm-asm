#!/usr/bin/env bash
# codegen-zisk-p256verify-check.sh -- P256VERIFY (EIP-7951) kernel probe.
#
# Validates the real `zkvm_secp256r1_verify` ECDSA-secp256r1 kernel
# against the execution-specs reference (`secp256r1_verify` +
# `is_on_curve_secp256r1`, i.e. the `cryptography` library): freshly
# signed valid signatures, the n-s malleability twin (valid under
# EIP-7951 -- no low-s rule), wrong-hash/wrong-key rejections, the
# r/s/qx/qy bounds gates, the (0,0) and off-curve pubkey gates, and
# the u1 = 0 corner (msg hash a multiple of n).
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

echo "==> emit zisk_p256verify_real ELF"
lake exe codegen --program zisk_p256verify_real --halt linux93 \
  -o gen-out/zisk_p256verify_real

ZISKEMU="$ZISKEMU" \
  execution-specs/.venv/bin/python3 - <<'PYSCRIPT'
import os
import subprocess
import sys

from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.primitives.asymmetric.utils import (
    decode_dss_signature, Prehashed,
)
from cryptography.hazmat.primitives import hashes

from ethereum_types.numeric import U256
from ethereum.crypto.elliptic_curve import (
    SECP256R1N, SECP256R1P, is_on_curve_secp256r1, secp256r1_verify,
)
from ethereum.crypto.hash import Hash32
from ethereum.exceptions import InvalidSignatureError

ZISKEMU = os.environ['ZISKEMU']
N = int(SECP256R1N)
P = int(SECP256R1P)

def run(payload, steps=1000000000):
    assert len(payload) == 160
    inp = 'gen-out/p256verify_check.input'
    out = 'gen-out/p256verify_check.output'
    with open(inp, 'wb') as f:
        f.write(payload)
    subprocess.run(
        [ZISKEMU, '-e', 'gen-out/zisk_p256verify_real.elf', '-i', inp,
         '-o', out, '-n', str(steps)],
        capture_output=True, check=False)
    blob = open(out, 'rb').read()
    if len(blob) < 9:
        return (None, None)
    return int.from_bytes(blob[0:8], 'little'), blob[8]

def ref(payload):
    """Mirror p256verify.py's gates + secp256r1_verify."""
    h = payload[0:32]
    r = int.from_bytes(payload[32:64], 'big')
    s = int.from_bytes(payload[64:96], 'big')
    qx = int.from_bytes(payload[96:128], 'big')
    qy = int.from_bytes(payload[128:160], 'big')
    if r <= 0 or r >= N or s <= 0 or s >= N:
        return 0
    if qx >= P or qy >= P:
        return 0
    if qx == 0 and qy == 0:
        return 0
    if not is_on_curve_secp256r1(U256(qx), U256(qy)):
        return 0
    try:
        secp256r1_verify(U256(r), U256(s), U256(qx), U256(qy), Hash32(h))
    except InvalidSignatureError:
        return 0
    return 1

fails = 0

def check(name, payload):
    global fails
    status, got = run(payload)
    want = ref(payload)
    if status == 0 and got == want:
        print(f'    ok: {name} (verified={want})')
    else:
        print(f'==> FAIL: {name}')
        print(f'    status: {status}  got: {got}  want: {want}')
        fails += 1

def payload(h, r, s, qx, qy):
    return (h + r.to_bytes(32, 'big') + s.to_bytes(32, 'big') +
            qx.to_bytes(32, 'big') + qy.to_bytes(32, 'big'))

def sign(key, h):
    sig = key.sign(h, ec.ECDSA(Prehashed(hashes.SHA256())))
    return decode_dss_signature(sig)

key = ec.derive_private_key(0xc0ffee, ec.SECP256R1())
pub = key.public_key().public_numbers()
QX, QY = pub.x, pub.y

H1 = bytes.fromhex(
    '6162630000000000000000000000000000000000000000000000000000000000')
r1, s1 = sign(key, H1)

check('valid signature', payload(H1, r1, s1, QX, QY))
check('malleable twin s -> n-s (valid per EIP-7951)',
      payload(H1, r1, N - s1, QX, QY))
check('wrong hash', payload(b'\x55' * 32, r1, s1, QX, QY))
key2 = ec.derive_private_key(0xdeadbeef, ec.SECP256R1())
pub2 = key2.public_key().public_numbers()
check('wrong pubkey', payload(H1, r1, s1, pub2.x, pub2.y))
check('r = 0 rejected', payload(H1, 0, s1, QX, QY))
check('r = n rejected', payload(H1, N, s1, QX, QY))
check('s = 0 rejected', payload(H1, r1, 0, QX, QY))
check('s = n rejected', payload(H1, r1, N, QX, QY))
check('qx = p rejected', payload(H1, r1, s1, P, QY))
check('qy >= p rejected', payload(H1, r1, s1, QX, P + 1 if P + 1 < 2**256 else P))
check('(0,0) pubkey rejected', payload(H1, r1, s1, 0, 0))
check('off-curve pubkey rejected', payload(H1, r1, s1, QX, (QY + 1) % P))
# u1 = 0 corner: a hash that is a multiple of n (e mod n == 0)
HN = N.to_bytes(32, 'big')
rn, sn = sign(key, HN)
check('hash = n (u1 = 0, valid)', payload(HN, rn, sn, QX, QY))
check('hash = n, tampered s (invalid)',
      payload(HN, rn, sn ^ 0x2, QX, QY))

if fails:
    print(f'==> FAIL: {fails} P256VERIFY case(s) mismatched')
    sys.exit(1)
print('==> PASS: P256VERIFY kernel matches the execution-specs reference')
PYSCRIPT
