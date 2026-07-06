#!/usr/bin/env bash
# codegen-zisk-extcodecopy-at-header-state-root-check.sh
#
# Witness-side EVM EXTCODECOPY opcode. Copies `length` bytes of
# contract code into an output buffer, with the spec-mandated
# zero-padding behavior when reads extend past the end of code.
#
# Composes K201 + K28 + K19 + a byte-by-byte zero-padded copy.
#
# Output (16 + length bytes; length capped at 32768):
#   bytes  0.. 8 : status
#       0 success (output filled, zero-padded if needed)
#       2 state-trie mpt parse error
#       3 account_decode failure
#       4 header parse fail
#       5 code_hash != EMPTY but not in witness.codes
#       6 length > 32768 (deployed-code cap)
#   bytes  8..16 : effective length
#   bytes 16..(16+length) : code bytes
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

echo "==> emit zisk_extcodecopy_at_header_state_root ELF"
lake exe codegen --program zisk_extcodecopy_at_header_state_root \
  --halt linux93 \
  -o gen-out/zisk_extcodecopy_at_header_state_root

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#
#   contract <addr> <code_hex> <code_offset> <length>
#     Account with non-trivial code; expect (0, length, expected_bytes).
#
#   empty_code <addr> <length>
#     code_hash == EMPTY_CODE_HASH; expect (0, length, all zeros).
#
#   missing_account <lookup_addr> <stored_addr> <code_hex> <length>
#     Account not at lookup_addr; expect (0, length, all zeros).
#
#   integrity_violation <addr> <code_hex> <length>
#     account.code_hash claims code, but witness.codes is empty.
#     Expect (5, 0, all zeros).
#
#   garbage_header <addr> <length>  -> (4, 0, all zeros)
#
#   over_cap <addr> <code_hex>  -> (6, 0, ...) [length=32769]
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_ecc_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_ecc_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_ecc_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp
from Crypto.Hash import keccak

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
        result += bytes([nibbles[i] * 0x10 + nibbles[i+1]])
    return result

def leaf_node(path_nibbles, value):
    return rlp.encode([hp_encode(path_nibbles, True), value])

def bytes_to_nibbles(b):
    out = []
    for byte in b:
        out.append(byte >> 4)
        out.append(byte & 0xf)
    return out

def build_ssz_section(elements):
    n = len(elements)
    if n == 0:
        return b''
    section = b''
    offset = 4 * n
    for e in elements:
        section += struct.pack('<I', offset)
        offset += len(e)
    for e in elements:
        section += e
    return section

def encode_account(nonce, balance, storage_root, code_hash):
    return rlp.encode([nonce, balance, storage_root, code_hash])

def encode_header(state_root):
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    return rlp.encode(fields)

EMPTY_TRIE = bytes.fromhex('56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')
EMPTY_CODE_HASH = bytes.fromhex('c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470')

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

def build_state_with_account(addr, account_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, account_rlp)
    return k256(leaf), build_ssz_section([leaf])

def extcodecopy_spec(code, offset, length):
    out = bytearray(length)
    for i in range(length):
        src = offset + i
        if src < len(code):
            out[i] = code[src]
    return bytes(out)

if mode == 'contract':
    addr = bytes.fromhex(parts[0])
    code = bytes.fromhex(parts[1])
    code_offset = int(parts[2])
    length = int(parts[3])
    code_hash = k256(code)
    account = encode_account(0, 0, EMPTY_TRIE, code_hash)
    state_root, witness_state = build_state_with_account(addr, account)
    witness_codes = build_ssz_section([code])
    header = encode_header(state_root)
    spec_bytes = extcodecopy_spec(code, code_offset, length)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', length) + spec_bytes
elif mode == 'empty_code':
    addr = bytes.fromhex(parts[0])
    length = int(parts[1])
    code_offset = 0
    account = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root, witness_state = build_state_with_account(addr, account)
    witness_codes = b''
    header = encode_header(state_root)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', length) + b'\\x00' * length
elif mode == 'missing_account':
    lookup_addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    code = bytes.fromhex(parts[2])
    length = int(parts[3])
    code_offset = 0
    code_hash = k256(code)
    account = encode_account(0, 0, EMPTY_TRIE, code_hash)
    state_root, witness_state = build_state_with_account(stored_addr, account)
    witness_codes = build_ssz_section([code])
    addr = lookup_addr
    header = encode_header(state_root)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', length) + b'\\x00' * length
elif mode == 'integrity_violation':
    addr = bytes.fromhex(parts[0])
    code = bytes.fromhex(parts[1])
    length = int(parts[2])
    code_offset = 0
    code_hash = k256(code)
    account = encode_account(0, 0, EMPTY_TRIE, code_hash)
    state_root, witness_state = build_state_with_account(addr, account)
    witness_codes = b''
    header = encode_header(state_root)
    expected = struct.pack('<Q', 5) + struct.pack('<Q', 0) + b'\\x00' * length
elif mode == 'garbage_header':
    addr = bytes.fromhex(parts[0])
    length = int(parts[1])
    code_offset = 0
    witness_state = b''
    witness_codes = b''
    header = b'\\x00'
    expected = struct.pack('<Q', 4) + struct.pack('<Q', 0) + b'\\x00' * length
elif mode == 'over_cap':
    addr = bytes.fromhex(parts[0])
    code = bytes.fromhex(parts[1])
    code_offset = 0
    length = 32769
    code_hash = k256(code)
    account = encode_account(0, 0, EMPTY_TRIE, code_hash)
    state_root, witness_state = build_state_with_account(addr, account)
    witness_codes = build_ssz_section([code])
    header = encode_header(state_root)
    # status 6 + zero length; bytes section reads up to 0 effective length
    expected = struct.pack('<Q', 6) + struct.pack('<Q', 0)
else:
    raise SystemExit('bad mode: ' + mode)

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(header))
        + struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', len(witness_codes))
        + struct.pack('<Q', code_offset)
        + struct.pack('<Q', length)
        + addr
        + header
        + witness_state
        + witness_codes
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_extcodecopy_at_header_state_root.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_ecc_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-30s OK   %d bytes match\n" "$name" "$exp_size"
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

ALICE="$(printf 'aa%.0s' $(seq 1 20))"
BOB="$(printf 'bb%.0s' $(seq 1 20))"

FAILED=0
# Full code (10 bytes), copy all 10 with offset 0.
run_case "full_code_offset_0"    contract "$ALICE" "60006000016000526000" 0 10 || FAILED=1
# Tail of the code (offset 6, length 4).
run_case "tail_of_code"          contract "$ALICE" "60006000016000526000" 6 4 || FAILED=1
# THE spec-defining case: read past the end with zero padding.
# code is 4 bytes long; offset=0, length=8 -> 4 bytes of code + 4 bytes of zero.
run_case "zero_pad_past_end"     contract "$ALICE" "deadbeef" 0 8 || FAILED=1
# Offset beyond code length -> all zeros.
run_case "offset_past_end"       contract "$ALICE" "deadbeef" 10 4 || FAILED=1
# Offset at end -> all zeros.
run_case "offset_exactly_at_end" contract "$ALICE" "deadbeef" 4 3 || FAILED=1
# Zero length -> empty output, status 0.
run_case "zero_length"           contract "$ALICE" "deadbeef" 0 0 || FAILED=1
# Empty code (EMPTY_CODE_HASH).
run_case "empty_code_hash"       empty_code "$ALICE" 8 || FAILED=1
# Missing account.
run_case "missing_account"       missing_account "$BOB" "$ALICE" "6000" 4 || FAILED=1
# Integrity violation.
run_case "integrity_violation"   integrity_violation "$ALICE" "6000" 4 || FAILED=1
# Garbage header.
run_case "garbage_header"        garbage_header "$ALICE" 4 || FAILED=1
# Length > 32768 cap.
run_case "over_cap"              over_cap "$ALICE" "6000" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: extcodecopy_at_header_state_root end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
