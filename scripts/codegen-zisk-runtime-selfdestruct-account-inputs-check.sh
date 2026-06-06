#!/usr/bin/env bash
# codegen-zisk-runtime-selfdestruct-account-inputs-check.sh
#
# Validate the runtime SELFDESTRUCT account-input loader against the optional
# account-witness context produced by scripts/pack-bytecode.py.
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

RUN_DIR="${RUN_DIR:-gen-out/runtime_selfdestruct_account_inputs}"
case "$RUN_DIR" in
  /*) ;;
  *) RUN_DIR="$PWD/$RUN_DIR" ;;
esac
mkdir -p "$RUN_DIR" gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit runtime_selfdestruct_account_inputs ELF"
lake exe codegen --program runtime_selfdestruct_account_inputs \
  --halt linux93 \
  -o gen-out/runtime_selfdestruct_account_inputs

make_case() {
  local name="$1" origin="$2" beneficiary="$3" created_in_tx="$4" origin_nonce="$5" origin_balance="$6" origin_code_hex="$7" beneficiary_nonce="$8" beneficiary_balance="$9" beneficiary_code_hex="${10}"
  uv run --directory execution-specs --quiet python3 - \
    "$RUN_DIR/$name" "$origin" "$beneficiary" "$created_in_tx" \
    "$origin_nonce" "$origin_balance" "$origin_code_hex" \
    "$beneficiary_nonce" "$beneficiary_balance" "$beneficiary_code_hex" <<'INNERPY'
import struct, sys
from pathlib import Path
import rlp
from Crypto.Hash import keccak

out = Path(sys.argv[1])
origin = bytes.fromhex(sys.argv[2])
beneficiary = bytes.fromhex(sys.argv[3])
created_in_tx = int(sys.argv[4])
origin_nonce, origin_balance = int(sys.argv[5]), int(sys.argv[6])
origin_code = bytes.fromhex(sys.argv[7])
beneficiary_nonce, beneficiary_balance = int(sys.argv[8]), int(sys.argv[9])
beneficiary_code = bytes.fromhex(sys.argv[10])

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

def extension_node(path_nibbles, child_ref):
    return rlp.encode([hp_encode(path_nibbles, False), child_ref])

def branch_node(slots, value=b''):
    return rlp.encode(slots + [value])

def node_ref(node):
    return node if len(node) < 32 else k256(node)

def build_ssz_section(elements):
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

def account(nonce, balance, code):
    return rlp.encode([nonce, balance, EMPTY_TRIE, k256(code)])

origin_account = account(origin_nonce, origin_balance, origin_code)
beneficiary_account = account(beneficiary_nonce, beneficiary_balance, beneficiary_code)
origin_path = bytes_to_nibbles(k256(origin))
beneficiary_path = bytes_to_nibbles(k256(beneficiary))

if origin == beneficiary:
    leaf = leaf_node(origin_path, origin_account)
    root_node = leaf
    witness_nodes = [leaf]
elif origin_path == beneficiary_path:
    raise SystemExit("origin and beneficiary have colliding account trie paths")
else:
    common = 0
    while (common < len(origin_path) and common < len(beneficiary_path) and
           origin_path[common] == beneficiary_path[common]):
        common += 1
    origin_leaf = leaf_node(origin_path[common + 1:], origin_account)
    beneficiary_leaf = leaf_node(beneficiary_path[common + 1:], beneficiary_account)
    slots = [b''] * 16
    slots[origin_path[common]] = node_ref(origin_leaf)
    slots[beneficiary_path[common]] = node_ref(beneficiary_leaf)
    branch = branch_node(slots)
    if common == 0:
        root_node = branch
        witness_nodes = [branch, origin_leaf, beneficiary_leaf]
    else:
        root_node = extension_node(origin_path[:common], node_ref(branch))
        witness_nodes = [root_node, branch, origin_leaf, beneficiary_leaf]

state_root = k256(root_node)
header = encode_header(state_root)
witness_state = build_ssz_section(witness_nodes)

if origin == beneficiary and created_in_tx:
    origin_expected = account(origin_nonce, 0, origin_code)
    beneficiary_expected = origin_expected
elif origin == beneficiary:
    origin_expected = origin_account
    beneficiary_expected = origin_account
elif origin_balance == 0:
    origin_expected = origin_account
    beneficiary_expected = beneficiary_account
else:
    origin_expected = account(origin_nonce, 0, origin_code)
    beneficiary_expected = account(
        beneficiary_nonce,
        origin_balance + beneficiary_balance,
        beneficiary_code,
    )

expected = (
    struct.pack('<Q', 0) +
    struct.pack('<Q', len(origin_account)) +
    struct.pack('<Q', len(beneficiary_account)) +
    struct.pack('<Q', 32) +
    struct.pack('<Q', 0) +
    struct.pack('<Q', len(origin_expected)) +
    struct.pack('<Q', len(beneficiary_expected)) +
    b'\0' * 8 +
    origin_expected.ljust(96, b'\0') +
    beneficiary_expected.ljust(96, b'\0')
)

out.mkdir(parents=True, exist_ok=True)
out.joinpath('header.bin').write_bytes(header)
out.joinpath('state.bin').write_bytes(witness_state)
out.joinpath('expected.bin').write_bytes(expected)
out.joinpath('origin.hex').write_text(origin.hex())
out.joinpath('bytecode.csv').write_text(
    ', '.join(f'0x{x:02x}' for x in beneficiary + bytes([created_in_tx]))
)
INNERPY
}

ALICE="$(printf 'aa%.0s' $(seq 1 20))"
BOB="$(printf 'bb%.0s' $(seq 1 20))"
FAILED=0

make_case same_account "$ALICE" "$ALICE" 0 7 11 "6001600201" 7 11 "6001600201"
make_case same_created_burn "$ALICE" "$ALICE" 1 7 11 "6001600201" 7 11 "6001600201"
make_case different_beneficiary "$ALICE" "$BOB" 0 7 11 "6001600201" 3 5 "6002600301"
make_case zero_balance_different "$ALICE" "$BOB" 0 7 0 "6001600201" 3 5 "6002600301"

for name in same_account same_created_burn different_beneficiary zero_balance_different; do
  echo "==> pack $name"
  origin="$(cat "$RUN_DIR/$name/origin.hex")"
  scripts/pack-bytecode.py \
    --env "address=0x$origin" \
    --state-header-rlp "@$RUN_DIR/$name/header.bin" \
    --witness-state "@$RUN_DIR/$name/state.bin" \
    "$(cat "$RUN_DIR/$name/bytecode.csv")" \
    "$RUN_DIR/$name/input.bin"

  echo "==> ziskemu $name"
  if ! "$ZISKEMU" -e gen-out/runtime_selfdestruct_account_inputs.elf \
    -i "$RUN_DIR/$name/input.bin" \
    -o "$RUN_DIR/$name/output.bin" \
    -n 5000000 \
    >"$RUN_DIR/$name/emu.log" 2>&1; then
    FAILED=1
  fi

  actual="$(xxd -p -l 256 "$RUN_DIR/$name/output.bin" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l 256 "$RUN_DIR/$name/expected.bin" | tr -d '\n')"
  if [[ "$actual" == "$expected" ]]; then
    printf "  %-12s OK\n" "$name"
  else
    printf "  %-12s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected" "$actual"
    FAILED=1
  fi
done

if [[ "$FAILED" -ne 0 ]]; then
  echo "==> FAIL: runtime SELFDESTRUCT account inputs" >&2
  exit 1
fi

echo "==> PASS: runtime SELFDESTRUCT account inputs"
