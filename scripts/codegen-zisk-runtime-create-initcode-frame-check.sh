#!/usr/bin/env bash
# codegen-zisk-runtime-create-initcode-frame-check.sh
#
# Exercise CREATE / CREATE2 child-frame staging through the focused runtime
# probe. The probe computes the target address with the same helpers used by
# runtime CREATE/CREATE2, stages the initcode frame, and writes the staged
# fields to public output for comparison.
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

RUN_DIR="${RUN_DIR:-gen-out/runtime_create_initcode_frame}"
case "$RUN_DIR" in
  /*) ;;
  *) RUN_DIR="$PWD/$RUN_DIR" ;;
esac
mkdir -p "$RUN_DIR" gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit runtime_create_initcode_frame ELF"
lake exe codegen --program runtime_create_initcode_frame --halt linux93 -o gen-out/runtime_create_initcode_frame

make_case() {
  local name="$1" kind="$2" offset="$3" nonce="$4" value_hex="$5" init_hex="$6" salt_hex="$7"
  uv run --directory execution-specs --quiet python3 - \
    "$RUN_DIR/$name" "$kind" "$offset" "$nonce" "$value_hex" "$init_hex" "$salt_hex" <<'INNERPY'
import struct, sys
from pathlib import Path
import rlp
from Crypto.Hash import keccak

out = Path(sys.argv[1])
kind = int(sys.argv[2])
offset = int(sys.argv[3])
nonce = int(sys.argv[4])
value = bytes.fromhex(sys.argv[5])
initcode = bytes.fromhex(sys.argv[6])
salt = bytes.fromhex(sys.argv[7])
creator = bytes.fromhex('1234567890abcdef1234567890abcdef12345678')

assert kind in (0, 1)
assert len(value) == 32
assert len(salt) == 32

def k256(b: bytes) -> bytes:
    h = keccak.new(digest_bits=256)
    h.update(b)
    return h.digest()

def create_address(sender: bytes, account_nonce: int) -> bytes:
    return k256(rlp.encode([sender, account_nonce]))[12:]

def create2_address(sender: bytes, salt_bytes: bytes, init: bytes) -> bytes:
    return k256(b'\xff' + sender + salt_bytes + k256(init))[12:]

target = create_address(creator, nonce) if kind == 0 else create2_address(creator, salt, initcode)

payload = (
    struct.pack('<Q', kind)
    + struct.pack('<Q', offset)
    + struct.pack('<Q', len(initcode))
    + struct.pack('<Q', nonce)
    + creator
    + salt
    + value
    + initcode
)
expected = (
    struct.pack('<Q', 1)
    + struct.pack('<Q', kind)
    + struct.pack('<Q', len(initcode))
    + target + b'\x00' * 12
    + creator + b'\x00' * 12
    + value
    + initcode[:32].ljust(32, b'\x00')
)

out.mkdir(parents=True, exist_ok=True)
out.joinpath('input.bin').write_bytes(payload.ljust((len(payload) + 7) // 8 * 8, b'\x00'))
out.joinpath('expected.bin').write_bytes(expected)
INNERPY
}

FAILED=0
CASES=(
  "create 0 7 3 000000000000000000000000000000000000000000000000000000000000002a 602a60005260206000f3 0000000000000000000000000000000000000000000000000000000000000000"
  "create2 1 19 0 0000000000000000000000000000000000000000000000000000000000000101 600160005560216000f3 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
)

for spec in "${CASES[@]}"; do
  read -r name kind offset nonce value_hex init_hex salt_hex <<<"$spec"
  make_case "$name" "$kind" "$offset" "$nonce" "$value_hex" "$init_hex" "$salt_hex"

  echo "==> ziskemu $name"
  if ! "$ZISKEMU" -e gen-out/runtime_create_initcode_frame.elf \
    -i "$RUN_DIR/$name/input.bin" \
    -o "$RUN_DIR/$name/output.bin" \
    -n 12000000 \
    >"$RUN_DIR/$name/emu.log" 2>&1; then
    FAILED=1
  fi

  exp_size="$(stat -c%s "$RUN_DIR/$name/expected.bin")"
  actual="$(xxd -p -l "$exp_size" "$RUN_DIR/$name/output.bin" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$RUN_DIR/$name/expected.bin" | tr -d '\n')"
  if [[ "$actual" == "$expected" ]]; then
    printf "  %-12s OK\n" "$name"
  else
    printf "  %-12s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected" "$actual"
    FAILED=1
  fi
done

if [[ "$FAILED" -ne 0 ]]; then
  echo "==> FAIL: runtime CREATE initcode frame staging" >&2
  exit 1
fi

echo "==> PASS: runtime CREATE initcode frame staging"
