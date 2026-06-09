#!/usr/bin/env bash
# codegen-zisk-call-balance-gate-check.sh
#
# Positive verification of the value-bearing CALL balance gate
# (callDescendFallThrough, bead fhsxz.2.4.2.61.6.4.1 / PR #8540) through the REAL
# dispatch loop with a genuine account-witness context.
#
# The probe `zisk_call_balance_gate` drives the live callFrameGuestRegistry h_CALL
# handler. The caller account (env.ADDRESS) exists in the supplied state trie with
# balance 100; the parent runs  CALL; PUSH1 0; SSTORE; PUSH1 0xAB; PUSH1 1; SSTORE;
# STOP  with a CALL value word = 200 (> 100) to a non-precompile callee.
#
# A correct gate: value 200 > balance 100 => push 0 and DO NOT descend; the parent
# then SSTOREs the CALL result (0) to slot 0 and a sentinel 0xAB to slot 1.
# Asserts halt 0, two emitted slots, slot 0 == 0 (call rejected) and slot 1 == 0xAB
# (parent resumed + ran to completion). No CLI input.
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  elif [[ -x /var/tmp/zisk-shared/ziskemu ]]; then
    ZISKEMU=/var/tmp/zisk-shared/ziskemu
  else
    echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2
    exit 1
  fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_call_balance_gate ELF"
lake exe codegen --program zisk_call_balance_gate --halt linux93 \
  -o gen-out/zisk_call_balance_gate

IN_FILE="$(pwd)/gen-out/zisk_call_balance_gate.input"
OUT_FILE="$(pwd)/gen-out/zisk_call_balance_gate.out"

# Build the account witness (ALICE, nonce 0, balance 100) reusing the
# balance-at-header-state-root fixture machinery.
ALICE="$(printf 'aa%.0s' $(seq 1 20))"
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
        out.append(byte >> 4); out.append(byte & 0xf)
    return out

def build_ssz_section(elements):
    n = len(elements)
    if n == 0: return b''
    section = b''; offset = 4 * n
    for e in elements:
        section += struct.pack('<I', offset); offset += len(e)
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

addr = bytes.fromhex('$ALICE')
account = encode_account(0, 100, EMPTY_TRIE, EMPTY_CODE)
path = bytes_to_nibbles(k256(addr))
leaf = leaf_node(path, account)
state_root = k256(leaf)
witness_state = build_ssz_section([leaf])
header = encode_header(state_root)

with open('$IN_FILE', 'wb') as f:
    record = (struct.pack('<Q', len(header)) + struct.pack('<Q', len(witness_state))
              + addr + header + witness_state)
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)
"

"$ZISKEMU" -e gen-out/zisk_call_balance_gate.elf \
  -i "$IN_FILE" -o "$OUT_FILE" -n 5000000 >/dev/null 2>&1 || true

python3 - <<PY
import struct, sys
d = open('$OUT_FILE', 'rb').read()
def w(off): return struct.unpack('<Q', d[off:off+8])[0]
halt, cnt = w(32), w(56)
ka, va = w(64), w(96)
kb, vb = w(128), w(160)
slots = {ka: va, kb: vb}
print(f"  halt_kind(+32)  = {halt} (exp 0)")
print(f"  slot count(+56) = {cnt} (exp 2)")
print(f"  record0 (+64/+96)   key={ka} val={hex(va)}")
print(f"  record1 (+128/+160) key={kb} val={hex(vb)}")
ok = (halt == 0 and cnt == 2 and 0 in slots and 1 in slots
      and slots[0] == 0 and slots[1] == 0xAB)
if ok:
    print(f"  slot0 (CALL result) = {slots[0]}  -> value-bearing CALL rejected (balance 100 < value 200)")
    print(f"  slot1 (sentinel)    = {hex(slots[1])} -> parent resumed past the CALL and ran to completion")
    print("==> PASS: value>balance CALL pushes 0 and does NOT descend (balance gate verified end-to-end)")
else:
    print("==> FAIL"); sys.exit(1)
PY
