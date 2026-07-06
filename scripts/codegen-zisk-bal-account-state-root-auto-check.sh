#!/usr/bin/env bash
# codegen-zisk-bal-account-state-root-auto-check.sh -- verify BAL replay with record derivation.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

VDIR="$REPO_ROOT/gen-out/mpt-set"
echo "==> generate BAL account state-root auto vector"
uv run --directory execution-specs --quiet python3 - "$VDIR" <<'PYGEN'
import os
import struct
import sys
from ethereum.crypto.hash import keccak256

outdir = sys.argv[1]
os.makedirs(outdir, exist_ok=True)


def minimal_be(n: int) -> bytes:
    if n == 0:
        return b""
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def rlp_len_prefix(length: int, base: int) -> bytes:
    if length < 56:
        return bytes([base + length])
    l = minimal_be(length)
    return bytes([base + 55 + len(l)]) + l


def rlp_bytes(x: bytes) -> bytes:
    if len(x) == 1 and x[0] < 0x80:
        return x
    return rlp_len_prefix(len(x), 0x80) + x


def rlp_list(xs):
    payload = b"".join(xs)
    return rlp_len_prefix(len(payload), 0xc0) + payload


def rlp_int(n: int) -> bytes:
    return rlp_bytes(minimal_be(n))


EMPTY_TRIE = bytes.fromhex("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")
EMPTY_CODE = bytes.fromhex("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")


def account_rlp(
    nonce: int,
    balance: int,
    storage_root: bytes = EMPTY_TRIE,
    code_hash: bytes = EMPTY_CODE,
) -> bytes:
    return rlp_list([rlp_int(nonce), rlp_int(balance), rlp_bytes(storage_root), rlp_bytes(code_hash)])


def change_pair(index: int, value: bytes) -> bytes:
    return rlp_list([rlp_int(index), value])


def storage_root_single(slot: int, value: bytes) -> bytes:
    slot_path = account_path(slot.to_bytes(32, "big"))
    return keccak256(leaf_node(slot_path, rlp_bytes(value)))


def account_change(
    address: bytes,
    storage_changes=None,
    balance_changes=None,
    nonce_changes=None,
    code_changes=None,
) -> bytes:
    storage_changes = storage_changes or []
    balance_changes = balance_changes or []
    nonce_changes = nonce_changes or []
    code_changes = code_changes or []
    sc = [
        rlp_list([rlp_int(slot), rlp_list([change_pair(i, rlp_bytes(v)) for i, v in changes])])
        for slot, changes in storage_changes
    ]
    bc = [change_pair(i, rlp_int(v)) for i, v in balance_changes]
    nc = [change_pair(i, rlp_int(v)) for i, v in nonce_changes]
    cc = [change_pair(i, rlp_bytes(v)) for i, v in code_changes]
    return rlp_list([rlp_bytes(address), rlp_list(sc), rlp_list([]),
                     rlp_list(bc), rlp_list(nc), rlp_list(cc)])


def account_path(address: bytes) -> list[int]:
    out = []
    for b in keccak256(address):
        out.append(b >> 4)
        out.append(b & 0x0f)
    return out


def hp_encode(path: list[int], is_leaf: bool) -> bytes:
    flag = (2 if is_leaf else 0) + (1 if len(path) % 2 else 0)
    out = bytearray()
    if len(path) % 2:
        out.append(flag * 16 + path[0])
        path = path[1:]
    else:
        out.append(flag * 16)
    for i in range(0, len(path), 2):
        out.append(path[i] * 16 + path[i + 1])
    return bytes(out)


def leaf_node(path: list[int], value: bytes) -> bytes:
    return rlp_list([rlp_bytes(hp_encode(path, True)), rlp_bytes(value)])


def branch_node(slots: list[bytes], value: bytes = b"") -> bytes:
    return rlp_len_prefix(sum(len(slot) for slot in slots) + len(rlp_bytes(value)), 0xc0) + b"".join(slots) + rlp_bytes(value)


def node_ref(node: bytes) -> bytes:
    if len(node) < 32:
        return node
    return b"\xa0" + keccak256(node)


def ssz_section(elements):
    out = bytearray()
    off = 4 * len(elements)
    for element in elements:
        out += struct.pack("<I", off)
        off += len(element)
    for element in elements:
        out += element
    return bytes(out)


def align8_body(body: bytearray):
    while len(body) % 8 != 0:
        body += b"\x00"


def build_input(root_hash, witness, bal_list, n):
    body = bytearray()
    body += struct.pack("<QQQ", len(witness), n, len(bal_list))
    body += root_hash
    body += bal_list
    align8_body(body)
    body += witness
    align8_body(body)
    return bytes(body)


def storage_trie_one_slot(slot_idx: bytes, value: int):
    path = []
    for b in keccak256(slot_idx):
        path.append(b >> 4)
        path.append(b & 0x0f)
    value_rlp = rlp_bytes(minimal_be(value))
    leaf = leaf_node(path, value_rlp)
    return keccak256(leaf), leaf


present_addr = bytes.fromhex("c0f6dc9e5836f54caadbf59cc69346c508e1992b")
present_path = account_path(present_addr)
for i in range(2, 256):
    missing_addr = i.to_bytes(20, "big")
    missing_path = account_path(missing_addr)
    if missing_path[0] != present_path[0]:
        break
else:
    raise AssertionError("could not find distinct first nibble")

old_account = account_rlp(1, 5)
present_new = account_rlp(1, 10 ** 10)
missing_new = account_rlp(7, 9)
old_leaf = leaf_node(present_path[1:], old_account)
present_leaf_new = leaf_node(present_path[1:], present_new)
missing_leaf_new = leaf_node(missing_path[1:], missing_new)

slots = [b"\x80"] * 16
slots[present_path[0]] = node_ref(old_leaf)
root = branch_node(slots)
root_hash = keccak256(root)

post_slots = list(slots)
post_slots[present_path[0]] = node_ref(present_leaf_new)
post_slots[missing_path[0]] = node_ref(missing_leaf_new)
expected = keccak256(branch_node(post_slots))

bal_list = rlp_list([
    account_change(present_addr, balance_changes=[(1, 10 ** 10)]),
    account_change(missing_addr, balance_changes=[(1, 9)], nonce_changes=[(1, 7)]),
])
with open(f"{outdir}/basra_modify_insert.input", "wb") as f:
    f.write(build_input(root_hash, ssz_section([root, old_leaf]), bal_list, 2))
with open(f"{outdir}/basra_modify_insert.expected", "w") as f:
    f.write(expected.hex())
print(f"basra_modify_insert slots={present_path[0]},{missing_path[0]} expected={expected.hex()[:16]}..")

full_addr = bytes.fromhex("102030405060708090a0b0c0d0e0f00112233445")
full_path = account_path(full_addr)
full_old_account = account_rlp(4, 11)
full_code = bytes.fromhex("602a60005260206000f3")
full_storage_value = bytes.fromhex("1234")
full_new_storage_root = storage_root_single(3, full_storage_value)
full_new_account = account_rlp(9, 123456, full_new_storage_root, keccak256(full_code))
full_old_leaf = leaf_node(full_path[1:], full_old_account)
full_new_leaf = leaf_node(full_path[1:], full_new_account)
full_slots = [b"\x80"] * 16
full_slots[full_path[0]] = node_ref(full_old_leaf)
full_root = branch_node(full_slots)
full_root_hash = keccak256(full_root)
full_post_slots = list(full_slots)
full_post_slots[full_path[0]] = node_ref(full_new_leaf)
full_expected = keccak256(branch_node(full_post_slots))

full_bal_list = rlp_list([
    account_change(
        full_addr,
        storage_changes=[(3, [(2, full_storage_value)])],
        balance_changes=[(3, 123456)],
        nonce_changes=[(4, 9)],
        code_changes=[(5, full_code)],
    ),
])
with open(f"{outdir}/basra_full_post_fields.input", "wb") as f:
    f.write(build_input(full_root_hash, ssz_section([full_root, full_old_leaf]), full_bal_list, 1))
with open(f"{outdir}/basra_full_post_fields.expected", "w") as f:
    f.write(full_expected.hex())
print(f"basra_full_post_fields slot={full_path[0]} expected={full_expected.hex()[:16]}..")

# A second vector covers the general post-state account value shape used by
# execution-specs: storage writes first produce a new storage_root, then the
# account leaf is rewritten with nonce, balance, storage_root, and code_hash.
raw_addr = bytes.fromhex("abababababababababababababababababababab")
raw_path = account_path(raw_addr)
slot_key = (123).to_bytes(32, "big")
old_storage_root, old_storage_leaf = storage_trie_one_slot(slot_key, 0x11)
new_storage_root, new_storage_leaf = storage_trie_one_slot(slot_key, 0x2222)
old_code = b"\x60\x00"
new_code = b"\x60\x2a\x60\x00\x52"
old_raw_account = rlp_list([
    rlp_int(3),
    rlp_int(4),
    rlp_bytes(old_storage_root),
    rlp_bytes(keccak256(old_code)),
])
new_raw_account = rlp_list([
    rlp_int(9),
    rlp_int(10 ** 12),
    rlp_bytes(new_storage_root),
    rlp_bytes(keccak256(new_code)),
])
old_raw_leaf = leaf_node(raw_path, old_raw_account)
new_raw_leaf = leaf_node(raw_path, new_raw_account)
raw_root_hash = keccak256(old_raw_leaf)
raw_expected = keccak256(new_raw_leaf)
raw_bal_list = rlp_list([
    rlp_list([
        rlp_bytes(raw_addr),
        rlp_list([
            rlp_list([
                rlp_bytes(slot_key),
                rlp_list([
                    change_pair(3, rlp_int(0x11)),
                    change_pair(4, rlp_int(0x2222)),
                ]),
            ]),
        ]),
        rlp_list([]),
        rlp_list([change_pair(5, rlp_int(10 ** 12))]),
        rlp_list([change_pair(6, rlp_int(9))]),
        rlp_list([rlp_list([rlp_int(7), rlp_bytes(new_code)])]),
    ]),
])
with open(f"{outdir}/basra_full_fields_raw.input", "wb") as f:
    f.write(build_input(
        raw_root_hash,
        ssz_section([old_raw_leaf, old_storage_leaf]),
        raw_bal_list,
        1,
    ))
with open(f"{outdir}/basra_full_fields_raw.expected", "w") as f:
    f.write(raw_expected.hex())
print(f"basra_full_fields_raw expected={raw_expected.hex()[:16]}..")
PYGEN

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_bal_account_state_root_auto probe ELF"
lake exe codegen --program zisk_bal_account_state_root_auto --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_bal_account_state_root_auto"

fail=0
for name in basra_modify_insert basra_full_post_fields basra_full_fields_raw; do
  out="$VDIR/$name.output"
  "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_bal_account_state_root_auto.elf" \
    -i "$VDIR/$name.input" -o "$out" -n 30000000 >/dev/null 2>&1 </dev/null \
    || { echo "  ERROR  $name"; fail=1; continue; }
  status="$(od -An -tu8 -j 32 -N 8 "$out" | tr -d ' \n')"
  actual="$(xxd -p -s 0 -l 32 "$out" | tr -d '\n')"
  expected="$(cat "$VDIR/$name.expected")"
  if [[ "$status" == "0" && "$actual" == "$expected" ]]; then
    echo "  PASS   $name root=${actual:0:16}.."
  else
    echo "  FAIL   $name status=$status"
    echo "    expected: $expected"
    echo "    actual:   $actual"
    fail=1
  fi
done
[[ "$fail" -eq 0 ]] && echo "==> PASS: bal_account_state_root_auto matches reference" \
  || { echo "==> FAIL"; exit 1; }
