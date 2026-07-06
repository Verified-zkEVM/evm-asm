#!/usr/bin/env bash
# codegen-zisk-runtime-account-witness-context-check.sh
#
# Validate the runtime dispatcher's account-witness input context without
# wiring any EXTCODE opcode handler. The probe reuses runtime setup and then
# calls extcodehash_at_header_state_root with the bytecode segment interpreted
# as the 20-byte address payload.
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

RUN_DIR="${RUN_DIR:-gen-out/runtime_account_witness_context}"
case "$RUN_DIR" in
  /*) ;;
  *) RUN_DIR="$PWD/$RUN_DIR" ;;
esac
mkdir -p "$RUN_DIR" gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit runtime_account_witness_extcodehash ELF"
lake exe codegen --program runtime_account_witness_extcodehash \
  --halt linux93 \
  -o gen-out/runtime_account_witness_extcodehash

make_case() {
  local name="$1" mode="$2" lookup="$3" stored="$4" nonce="$5" balance="$6" code_hex="$7"
  uv run --directory execution-specs --quiet python3 - "$RUN_DIR/$name" "$mode" "$lookup" "$stored" "$nonce" "$balance" "$code_hex" <<'INNERPY'
import struct, sys
from pathlib import Path
import rlp
from Crypto.Hash import keccak

out = Path(sys.argv[1])
mode, lookup_hex, stored_hex = sys.argv[2], sys.argv[3], sys.argv[4]
nonce, balance = int(sys.argv[5]), int(sys.argv[6])
code = bytes.fromhex(sys.argv[7])
lookup = bytes.fromhex(lookup_hex)
stored = bytes.fromhex(stored_hex)

def k256(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

def hp_encode(nibbles, is_leaf):
    flag = 2 if is_leaf else 0
    if len(nibbles) % 2 == 1:
        flag |= 1
        result = bytes([flag * 0x10 + nibbles[0]])
        nibbles = nibbles[1:]
    else:
        result = bytes([flag * 0x10])
    for i in range(0, len(nibbles), 2):
        result += bytes([nibbles[i] * 0x10 + nibbles[i + 1]])
    return result

def bytes_to_nibbles(b):
    out = []
    for byte in b:
        out.extend([byte >> 4, byte & 0xf])
    return out

def leaf_node(path_nibbles, value):
    return rlp.encode([hp_encode(path_nibbles, True), value])

def build_ssz_section(elements):
    if not elements:
        return b''
    section = b''
    offset = 4 * len(elements)
    for e in elements:
        section += struct.pack('<I', offset)
        offset += len(e)
    return section + b''.join(elements)

def encode_header(state_root):
    fields = [
        b'\x11'*32, b'\x22'*32, b'\x33'*20, state_root, b'\x55'*32,
        b'\x66'*32, b'\x00'*256, b'', b'\x01', b'\x83\xff\xff\xff',
        b'', b'\x83\x01\x02\x03', b'', b'\x77'*32, b'\x00'*8,
    ]
    return rlp.encode(fields)

EMPTY_TRIE = bytes.fromhex('56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')
EMPTY_CODE_HASH = bytes.fromhex('c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470')

def encode_account(nonce, balance, storage_root, code_hash):
    return rlp.encode([nonce, balance, storage_root, code_hash])

if mode == 'missing':
    account = encode_account(nonce, balance, EMPTY_TRIE, k256(code))
    expected_hash = b'\0' * 32
elif mode == 'empty':
    account = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    expected_hash = b'\0' * 32
else:
    account = encode_account(nonce, balance, EMPTY_TRIE, k256(code))
    expected_hash = k256(code)

path = bytes_to_nibbles(k256(stored))
leaf = leaf_node(path, account)
state_root = k256(leaf)
header = encode_header(state_root)
witness_state = build_ssz_section([leaf])
out.mkdir(parents=True, exist_ok=True)
out.joinpath('header.bin').write_bytes(header)
out.joinpath('state.bin').write_bytes(witness_state)
out.joinpath('expected.bin').write_bytes(struct.pack('<Q', 0) + expected_hash)
out.joinpath('address.csv').write_text(', '.join(f'0x{x:02x}' for x in lookup))
INNERPY
}

ALICE="$(printf 'aa%.0s' $(seq 1 20))"
BOB="$(printf 'bb%.0s' $(seq 1 20))"
FAILED=0

make_case present present "$ALICE" "$ALICE" 7 11 "6001600201"
make_case empty empty "$ALICE" "$ALICE" 0 0 ""
make_case missing missing "$BOB" "$ALICE" 7 11 "6000"

for name in present empty missing; do
  echo "==> pack $name"
  scripts/pack-bytecode.py \
    --state-header-rlp "@$RUN_DIR/$name/header.bin" \
    --witness-state "@$RUN_DIR/$name/state.bin" \
    "$(cat "$RUN_DIR/$name/address.csv")" \
    "$RUN_DIR/$name/input.bin"

  echo "==> ziskemu $name"
  if ! "$ZISKEMU" -e gen-out/runtime_account_witness_extcodehash.elf \
    -i "$RUN_DIR/$name/input.bin" \
    -o "$RUN_DIR/$name/output.bin" \
    -n 4000000 \
    >"$RUN_DIR/$name/emu.log" 2>&1; then
    FAILED=1
  fi

  actual="$(xxd -p -l 40 "$RUN_DIR/$name/output.bin" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l 40 "$RUN_DIR/$name/expected.bin" | tr -d '\n')"
  if [[ "$actual" == "$expected" ]]; then
    printf "  %-10s OK\n" "$name"
  else
    printf "  %-10s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected" "$actual"
    FAILED=1
  fi
done

if [[ "$FAILED" -ne 0 ]]; then
  echo "==> FAIL: runtime account-witness context" >&2
  exit 1
fi

echo "==> PASS: runtime account-witness context"
