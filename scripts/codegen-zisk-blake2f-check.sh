#!/usr/bin/env bash
# codegen-zisk-blake2f-check.sh -- BLAKE2F compression kernel probe.
#
# Validates the real `zkvm_blake2f` EIP-152 kernel (ziskemu Blake2bRound
# accelerator, csrs 0x819) against execution-specs
# `ethereum.crypto.blake2.Blake2b.compress`: the official EIP-152 test
# vectors 4-7 (rounds=0, the standard 12-round "abc" block with f=1 and
# f=0, rounds=1) plus randomized payloads across round counts,
# including a SIGMA wrap (rounds > 10) and a large round count.
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

echo "==> emit zisk_blake2f_real ELF"
lake exe codegen --program zisk_blake2f_real --halt linux93 \
  -o gen-out/zisk_blake2f_real

ZISKEMU="$ZISKEMU" \
  execution-specs/.venv/bin/python3 - <<'PYSCRIPT'
import os
import random
import subprocess
import sys

from ethereum.crypto.blake2 import Blake2b

ZISKEMU = os.environ['ZISKEMU']

def run(payload, steps=200000000):
    assert len(payload) == 213
    inp = 'gen-out/blake2f_check.input'
    out = 'gen-out/blake2f_check.output'
    blob = payload + b'\x00' * (-len(payload) % 8)
    with open(inp, 'wb') as f:
        f.write(blob)
    subprocess.run(
        [ZISKEMU, '-e', 'gen-out/zisk_blake2f_real.elf', '-i', inp,
         '-o', out, '-n', str(steps)],
        capture_output=True, check=False)
    blob = open(out, 'rb').read()
    if len(blob) < 72:
        return (None, None)
    return int.from_bytes(blob[0:8], 'little'), blob[8:72]

def ref(payload):
    b2 = Blake2b()
    rounds, h, m, t_0, t_1, f = b2.get_blake2_parameters(payload)
    return bytes(b2.compress(rounds, h, m, t_0, t_1, f))

fails = 0

def check(name, payload):
    global fails
    status, got = run(payload)
    want = ref(payload)
    if status == 0 and got == want:
        print(f'    ok: {name}')
    else:
        print(f'==> FAIL: {name}')
        print(f'    status: {status}')
        print(f'    got:  {got.hex() if got else got}')
        print(f'    want: {want.hex()}')
        fails += 1

# the official EIP-152 "abc" payload (vectors 4-7 share h/m/t/f tails)
ABC_TAIL = bytes.fromhex(
    '48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5'
    'd182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b'
    '6162630000000000000000000000000000000000000000000000000000000000'
    '0000000000000000000000000000000000000000000000000000000000000000'
    '0000000000000000000000000000000000000000000000000000000000000000'
    '0000000000000000000000000000000000000000000000000000000000000000'
    '0300000000000000'
    '0000000000000000')

def payload(rounds, tail, f):
    return rounds.to_bytes(4, 'big') + tail + bytes([f])

check('EIP-152 vector 4 (rounds=0, f=1)', payload(0, ABC_TAIL, 1))
check('EIP-152 vector 5 (rounds=12, f=1)', payload(12, ABC_TAIL, 1))
check('EIP-152 vector 6 (rounds=12, f=0)', payload(12, ABC_TAIL, 0))
check('EIP-152 vector 7 (rounds=1, f=1)', payload(1, ABC_TAIL, 1))

rng = random.Random(152)
for rounds in (2, 9, 10, 11, 23, 100, 100000):
    tail = bytes(rng.randrange(256) for _ in range(208))
    f = rng.randrange(2)
    check(f'random payload rounds={rounds} f={f}', payload(rounds, tail, f))

if fails:
    print(f'==> FAIL: {fails} BLAKE2F case(s) mismatched')
    sys.exit(1)
print('==> PASS: BLAKE2F kernel matches the execution-specs reference')
PYSCRIPT
