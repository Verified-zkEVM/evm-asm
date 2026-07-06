#!/usr/bin/env bash
# codegen-zisk-ripemd160-check.sh -- software RIPEMD-160 kernel probe.
#
# Validates the pure-software `zkvm_ripemd160` precompile kernel (0x03)
# against the standard RIPEMD-160 test vectors plus Merkle-Damgård
# padding-boundary lengths (55/56/63/64/65) and a 1 MB multi-block
# input. ZisK has no RIPEMD-160 accelerator, so this exercises the
# table-driven two-line compression in Programs/Ripemd160.lean.
#
# The probe reads byte length from INPUT_ADDR + 8 (ziskemu's
# length-prefix slot), points at INPUT_ADDR + 16, calls
# zkvm_ripemd160, and writes the 32-byte left-padded digest
# (12 zero bytes ++ 20-byte hash, the EVM returndata encoding)
# at OUTPUT_ADDR. Each run is gated at -n 1000000000 steps so a
# perf regression past the stateless step budget fails the check.
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

echo "==> emit zisk_ripemd160_from_input ELF"
lake exe codegen --program zisk_ripemd160_from_input --halt linux93 \
  -o gen-out/zisk_ripemd160_from_input

ZISKEMU="$ZISKEMU" python3 - <<'PYSCRIPT'
import hashlib
import os
import struct
import subprocess
import sys

ZISKEMU = os.environ['ZISKEMU']

vectors = [
    b"",
    b"a",
    b"abc",
    b"message digest",
    b"abcdefghijklmnopqrstuvwxyz",
    b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
    b"a" * 55,            # last single-block length
    b"a" * 56,            # first two-block padding length
    b"a" * 63,
    b"a" * 64,            # exact block
    b"a" * 65,
    b"1234567890" * 8,
    bytes(range(256)),
    b"a" * 1000000,       # RIPEMD-160 million-'a' vector, multi-block
]

fails = 0
for data in vectors:
    want = '00' * 12 + hashlib.new('ripemd160', data).hexdigest()
    blob = struct.pack('<Q', len(data)) + data
    blob += b'\x00' * (-len(blob) % 8)   # ziskemu wants 8-byte-multiple inputs
    with open('gen-out/zisk_ripemd160_check.input', 'wb') as f:
        f.write(blob)
    subprocess.run(
        [ZISKEMU, '-e', 'gen-out/zisk_ripemd160_from_input.elf',
         '-i', 'gen-out/zisk_ripemd160_check.input',
         '-o', 'gen-out/zisk_ripemd160_check.output',
         '-n', '1000000000'],
        capture_output=True, check=False)
    got = open('gen-out/zisk_ripemd160_check.output', 'rb').read()[:32].hex()
    if got == want:
        print(f'    ok: len={len(data)}')
    else:
        print(f'==> FAIL: len={len(data)}')
        print(f'    got:  {got}')
        print(f'    want: {want}')
        fails += 1

if fails:
    print(f'==> FAIL: {fails} RIPEMD-160 vector(s) mismatched')
    sys.exit(1)
print('==> PASS: zkvm_ripemd160 matches the RIPEMD-160 reference vectors')
PYSCRIPT
