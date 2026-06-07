#!/usr/bin/env bash
# codegen-zisk-eip2935-blockhash-lookup-check.sh
#
# Resolve BLOCKHASH(target_block_number) via the EIP-2935 history
# contract: state[HISTORY_STORAGE_ADDRESS].storage[target % 8191].
#
# Output (40 bytes):
#   bytes  0.. 8 : status (0 / 2 / 3 / 4 / 6 / 7)
#   bytes  8..40 : block hash (u256 BE; zeros on absent/error)
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

echo "==> emit zisk_eip2935_blockhash_lookup ELF"
lake exe codegen --program zisk_eip2935_blockhash_lookup \
  --halt linux93 \
  -o gen-out/zisk_eip2935_blockhash_lookup

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#
#   stored <target_n> <stored_n> <stored_hash_hex>
#     History contract has slot (stored_n % 8191) = stored_hash.
#     If target_n == stored_n -> expect (0, stored_hash).
#     Else if (target_n % 8191) == (stored_n % 8191) -> expect (0, stored_hash) too
#     (the contract stores by slot, target may alias).
#
#   slot_miss <target_n> <stored_n> <stored_hash_hex>
#     History contract has slot stored_n_slot, target uses different slot.
#     Expect (0, zeros) per SLOAD spec.
#
#   no_history_contract <target_n>
#     History contract absent from witness. Expect (0, zeros).
#
#   garbage_header <target_n>
#     1-byte garbage header. Expect (4, zeros).
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_ebhl_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_ebhl_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_ebhl_${name}.expected"

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
EMPTY_CODE = bytes.fromhex('c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470')

# HISTORY_STORAGE_ADDRESS per EIP-2935.
HISTORY_ADDR = bytes.fromhex('0000F90827F1C53a10cb7A02335B175320002935'.lower())
HISTORY_SERVE_WINDOW = 8191

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

def build_storage_trie_one_slot(slot_idx_int, slot_value_hash_bytes):
    # slot_idx_be = u256 BE of slot_idx_int
    slot_idx_be = slot_idx_int.to_bytes(32, 'big')
    # In storage trie, slots are stored as rlp(slot_value:U256)
    slot_value_int = int.from_bytes(slot_value_hash_bytes, 'big')
    value_bytes = rlp.encode(slot_value_int)
    path = bytes_to_nibbles(k256(slot_idx_be))
    leaf = leaf_node(path, value_bytes)
    storage_root = k256(leaf)
    section = build_ssz_section([leaf])
    return storage_root, section

def build_state_trie_one_account(addr, account_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, account_rlp)
    return k256(leaf), build_ssz_section([leaf])

if mode == 'stored':
    target_n = int(parts[0])
    stored_n = int(parts[1])
    stored_hash = bytes.fromhex(parts[2])
    # The contract stores at slot index stored_n % HISTORY_SERVE_WINDOW.
    slot_idx_int = stored_n % HISTORY_SERVE_WINDOW
    storage_root, witness_storage = build_storage_trie_one_slot(slot_idx_int, stored_hash)
    account = encode_account(1, 0, storage_root, EMPTY_CODE)
    state_root, witness_state = build_state_trie_one_account(HISTORY_ADDR, account)
    header = encode_header(state_root)
    # If target_n % 8192 == stored_n % 8192 -> hit.
    if (target_n % HISTORY_SERVE_WINDOW) == slot_idx_int:
        expected_status = 0
        expected_hash = stored_hash
    else:
        expected_status = 0
        expected_hash = b'\\x00' * 32
elif mode == 'slot_miss':
    target_n = int(parts[0])
    stored_n = int(parts[1])
    stored_hash = bytes.fromhex(parts[2])
    storage_root, witness_storage = build_storage_trie_one_slot(stored_n % HISTORY_SERVE_WINDOW, stored_hash)
    account = encode_account(1, 0, storage_root, EMPTY_CODE)
    state_root, witness_state = build_state_trie_one_account(HISTORY_ADDR, account)
    header = encode_header(state_root)
    expected_status = 0
    expected_hash = b'\\x00' * 32
elif mode == 'no_history_contract':
    target_n = int(parts[0])
    # No history contract in trie; some unrelated account instead.
    other_addr = b'\\xaa' * 20
    account = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE)
    state_root, witness_state = build_state_trie_one_account(other_addr, account)
    witness_storage = b''
    header = encode_header(state_root)
    expected_status = 0
    expected_hash = b'\\x00' * 32
elif mode == 'garbage_header':
    target_n = int(parts[0])
    witness_state = b''
    witness_storage = b''
    header = b'\\x00'
    expected_status = 4
    expected_hash = b'\\x00' * 32
else:
    raise SystemExit('bad mode: ' + mode)

expected = struct.pack('<Q', expected_status) + expected_hash

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(header))
        + struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', len(witness_storage))
        + struct.pack('<Q', target_n)
        + header
        + witness_state
        + witness_storage
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_eip2935_blockhash_lookup.elf \
    -i "$in_file" -o "$out_file" -n 8000000 \
    >"$REPO_ROOT/gen-out/zisk_ebhl_${name}.emu.log" 2>&1 || true

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

HASH1="aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899"
HASH2="1111222233334444555566667777888899990000aaaabbbbccccddddeeeeffff"

FAILED=0
# Stored block at target = stored.
run_case "stored_target_eq"          stored 100 100 "$HASH1" || FAILED=1
# Wrap-around: target_n = stored_n + 8191 -> same slot.
run_case "stored_wraparound"         stored 8291 100 "$HASH1" || FAILED=1
# Regression: %8191 != %8192. target=8192 -> slot 1 under MOD 8191,
# but slot 0 under the old (buggy) AND 0x1fff mask. Must hit slot 1.
run_case "stored_mod_neq_mask"       stored 8192 8192 "$HASH1" || FAILED=1
# Different slot in same trie.
run_case "slot_miss_diff_slot"       slot_miss 100 200 "$HASH2" || FAILED=1
# History contract absent.
run_case "no_history_contract"       no_history_contract 100 || FAILED=1
# Garbage header.
run_case "garbage_header"            garbage_header 100 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: eip2935_blockhash_lookup end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
