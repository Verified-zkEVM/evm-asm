#!/usr/bin/env bash
# codegen-zisk-runtime-create-collision-check.sh
#
# Exercise CREATE / CREATE2 EIP-684 code-or-nonce collision handling through
# the runtime dispatcher with account-witness context populated by
# pack-bytecode.py.
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

RUN_DIR="${RUN_DIR:-gen-out/runtime_create_collision}"
case "$RUN_DIR" in
  /*) ;;
  *) RUN_DIR="$PWD/$RUN_DIR" ;;
esac
mkdir -p "$RUN_DIR" gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit runtime_dispatcher ELF"
lake exe codegen --program runtime_dispatcher --halt linux93 -o gen-out/runtime_dispatcher

make_case() {
  local name="$1" opcode="$2" collision="$3"
  uv run --directory execution-specs --quiet python3 - "$RUN_DIR/$name" "$opcode" "$collision" <<'INNERPY'
import struct, sys
from pathlib import Path
import rlp
from Crypto.Hash import keccak

out = Path(sys.argv[1])
opcode = sys.argv[2]
collision = sys.argv[3]
creator = bytes.fromhex('1234567890abcdef1234567890abcdef12345678')

EMPTY_TRIE = bytes.fromhex('56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')
EMPTY_CODE_HASH = bytes.fromhex('c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470')


def k256(b):
    h = keccak.new(digest_bits=256)
    h.update(b)
    return h.digest()


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


def encode_account(nonce, balance, storage_root, code_hash):
    return rlp.encode([nonce, balance, storage_root, code_hash])


def push_word_u8(v):
    return [0x60, v]


def create_bytecode():
    # PUSH1 size=0; PUSH1 offset=0; PUSH1 value=0; CREATE; STOP.
    return push_word_u8(0) + push_word_u8(0) + push_word_u8(0) + [0xf0, 0x00]


def create_value_bytecode(value):
    # PUSH1 size=0; PUSH1 offset=0; PUSH1 value=<value>; CREATE; STOP.
    return push_word_u8(0) + push_word_u8(0) + push_word_u8(value) + [0xf0, 0x00]


def create2_bytecode():
    # PUSH1 salt=1; PUSH1 size=0; PUSH1 offset=0; PUSH1 value=0; CREATE2; STOP.
    return push_word_u8(1) + push_word_u8(0) + push_word_u8(0) + push_word_u8(0) + [0xf5, 0x00]


def create_address(sender, nonce):
    return k256(rlp.encode([sender, nonce]))[12:]


def create2_address(sender, salt, initcode):
    return k256(b'\xff' + sender + salt.to_bytes(32, 'big') + k256(initcode))[12:]

if opcode == 'create' and collision == 'insufficient':
    bytecode = create_value_bytecode(1)
    target = create_address(creator, 0)
elif opcode == 'create':
    bytecode = create_bytecode()
    target = create_address(creator, 0)
elif opcode == 'create2':
    bytecode = create2_bytecode()
    target = create2_address(creator, 1, b'')
else:
    raise ValueError(opcode)

if collision == 'absent':
    account = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    leaf = leaf_node(bytes_to_nibbles(k256(creator)), account)
    header = encode_header(k256(leaf))
    witness_state = build_ssz_section([leaf])
    expected_address = target
elif collision == 'insufficient':
    account = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    leaf = leaf_node(bytes_to_nibbles(k256(creator)), account)
    header = encode_header(k256(leaf))
    witness_state = build_ssz_section([leaf])
    expected_address = b'\x00' * 20
elif collision == 'nonce_max':
    account = encode_account(2**64 - 1, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    leaf = leaf_node(bytes_to_nibbles(k256(creator)), account)
    header = encode_header(k256(leaf))
    witness_state = build_ssz_section([leaf])
    expected_address = b'\x00' * 20
elif collision == 'nonce':
    account = encode_account(1, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    leaf = leaf_node(bytes_to_nibbles(k256(target)), account)
    header = encode_header(k256(leaf))
    witness_state = build_ssz_section([leaf])
    expected_address = b'\x00' * 20
elif collision == 'code':
    account = encode_account(0, 0, EMPTY_TRIE, k256(b'\x60\x00'))
    leaf = leaf_node(bytes_to_nibbles(k256(target)), account)
    header = encode_header(k256(leaf))
    witness_state = build_ssz_section([leaf])
    expected_address = b'\x00' * 20
else:
    raise ValueError(collision)

expected_word = expected_address[::-1] + b'\x00' * 12
halt_kind = struct.pack('<Q', 0)

out.mkdir(parents=True, exist_ok=True)
out.joinpath('header.bin').write_bytes(header)
out.joinpath('state.bin').write_bytes(witness_state)
out.joinpath('expected.bin').write_bytes(expected_word + halt_kind)
out.joinpath('bytecode.csv').write_text(', '.join(f'0x{x:02x}' for x in bytecode))
INNERPY
}

FAILED=0
CASES=(
  "create_absent_target create absent"
  "create_nonce_collision create nonce"
  "create_code_collision create code"
  "create_insufficient_balance create insufficient"
  "create_nonce_exhaustion create nonce_max"
  "create2_absent_target create2 absent"
  "create2_nonce_collision create2 nonce"
  "create2_nonce_exhaustion create2 nonce_max"
)

for spec in "${CASES[@]}"; do
  read -r name opcode collision <<<"$spec"
  make_case "$name" "$opcode" "$collision"

  echo "==> pack $name"
  scripts/pack-bytecode.py \
    --env "address=0x1234567890abcdef1234567890abcdef12345678" \
    --state-header-rlp "@$RUN_DIR/$name/header.bin" \
    --witness-state "@$RUN_DIR/$name/state.bin" \
    "$(cat "$RUN_DIR/$name/bytecode.csv")" \
    "$RUN_DIR/$name/input.bin"

  echo "==> ziskemu $name"
  if ! "$ZISKEMU" -e gen-out/runtime_dispatcher.elf \
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
    printf "  %-26s OK\n" "$name"
  else
    printf "  %-26s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected" "$actual"
    FAILED=1
  fi
done

if [[ "$FAILED" -ne 0 ]]; then
  echo "==> FAIL: runtime CREATE collision handling" >&2
  exit 1
fi

echo "==> PASS: runtime CREATE collision handling"
