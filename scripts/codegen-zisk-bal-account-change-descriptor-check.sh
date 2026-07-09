#!/usr/bin/env bash
# codegen-zisk-bal-account-change-descriptor-check.sh -- verify BAL account replay descriptor packaging.
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
STEPS="${BAACD_STEPS:-${ZISK_STEPS:-20000000}}"
echo "==> generate BAL account descriptor vectors"
uv run --directory execution-specs --quiet python3 - "$VDIR" <<'PYGEN'
import os
import struct
import sys
from ethereum.crypto.hash import keccak256
from ethereum.merkle_patricia_trie import Trie, root, trie_set
from ethereum_types.bytes import Bytes32
from ethereum_types.numeric import U256

outdir = sys.argv[1]
os.makedirs(outdir, exist_ok=True)

EMPTY_ROOT = bytes.fromhex("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")
EMPTY_CODE_HASH = bytes.fromhex("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")


def minimal_be(n: int) -> bytes:
    if n == 0:
        return b""
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def rlp_bytes(x: bytes) -> bytes:
    if len(x) == 1 and x[0] < 0x80:
        return x
    if len(x) <= 55:
        return bytes([0x80 + len(x)]) + x
    l = minimal_be(len(x))
    return bytes([0xb7 + len(l)]) + l + x


def rlp_list(xs):
    payload = b"".join(xs)
    if len(payload) <= 55:
        return bytes([0xc0 + len(payload)]) + payload
    l = minimal_be(len(payload))
    return bytes([0xf7 + len(l)]) + l + payload


def rlp_int(n: int) -> bytes:
    return rlp_bytes(minimal_be(n))


def account_rlp(
    nonce: int,
    balance: int,
    storage_root: bytes = EMPTY_ROOT,
    code_hash: bytes = EMPTY_CODE_HASH,
) -> bytes:
    return rlp_list([rlp_int(nonce), rlp_int(balance), rlp_bytes(storage_root), rlp_bytes(code_hash)])


def storage_root(slots: dict[int, int]) -> bytes:
    trie = Trie(secured=True, default=U256(0))
    for slot, value in slots.items():
        trie_set(trie, Bytes32(slot.to_bytes(32, "big")), U256(value))
    return bytes(root(trie))


def change_pair(index: int, value: bytes) -> bytes:
    return rlp_list([rlp_int(index), value])


def storage_change(slot: int, changes) -> bytes:
    return rlp_list([rlp_int(slot), rlp_list([change_pair(i, rlp_int(v)) for i, v in changes])])


def bal_account_change_rlp(address: bytes, storage_changes=None, balance_changes=None, nonce_changes=None):
    storage_changes = storage_changes or []
    balance_changes = balance_changes or []
    nonce_changes = nonce_changes or []
    sc = [storage_change(slot, changes) for slot, changes in storage_changes]
    bc = [change_pair(i, rlp_int(v)) for i, v in balance_changes]
    nc = [change_pair(i, rlp_int(v)) for i, v in nonce_changes]
    return rlp_list([rlp_bytes(address), rlp_list(sc), rlp_list([]),
                     rlp_list(bc), rlp_list(nc), rlp_list([])])


def account_path(address: bytes) -> bytes:
    h = keccak256(address)
    out = bytearray()
    for b in h:
        out.append(b >> 4)
        out.append(b & 0x0f)
    return bytes(out)


def build_input(account: bytes, account_change: bytes, is_insert: int) -> bytes:
    body = struct.pack("<QQQ", len(account), len(account_change), is_insert) + account
    while len(body) % 8 != 0:
        body += b"\x00"
    body += account_change
    while len(body) % 8 != 0:
        body += b"\x00"
    return body


base = account_rlp(1, 5)
nonempty_storage = account_rlp(1, 5, storage_root({1: 7}))
cases = [
    ("baacd_modify", bytes.fromhex("c0f6dc9e5836f54caadbf59cc69346c508e1992b"), base,
     dict(balance_changes=[(1, 10 ** 10)]), account_rlp(1, 10 ** 10), 0, 0),
    ("baacd_insert", bytes.fromhex("0000000000000000000000000000000000000002"), base,
     dict(balance_changes=[(1, 9)], nonce_changes=[(1, 7)]), account_rlp(7, 9), 1, 1),
    # Caller flag 4 now passes through instead of being normalized to MODIFY. It must
    # not hide the unsupported mode before downstream state-root handling.
    ("baacd_flag4_preserve_storage", bytes.fromhex("cccccccccccccccccccccccccccccccccccccccc"), nonempty_storage,
     dict(balance_changes=[(4, 6)]), account_rlp(1, 6, storage_root({1: 7})), 4, 4),
]

with open(f"{outdir}/baacd_cases.txt", "w") as case_file:
    for name, addr, account, kwargs, expected_value, input_flag, expected_flag in cases:
        account_change = bal_account_change_rlp(addr, **kwargs)
        with open(f"{outdir}/{name}.input", "wb") as f:
            f.write(build_input(account, account_change, input_flag))
        with open(f"{outdir}/{name}.path", "w") as f:
            f.write(account_path(addr).hex())
        with open(f"{outdir}/{name}.value", "w") as f:
            f.write(expected_value.hex())
        with open(f"{outdir}/{name}.flag", "w") as f:
            f.write(str(expected_flag))
        case_file.write(f"{name}\n")
        print(f"{name:20} path={account_path(addr).hex()[:16]}.. value_len={len(expected_value)} input_flag={input_flag} expected_flag={expected_flag}")
PYGEN

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_bal_account_change_descriptor probe ELF"
lake exe codegen --program zisk_bal_account_change_descriptor --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_bal_account_change_descriptor"

fail=0
while IFS= read -r name; do
  [[ -n "$name" ]] || continue
  out="$VDIR/$name.output"
  "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_bal_account_change_descriptor.elf" \
    -i "$VDIR/$name.input" -o "$out" -n "$STEPS" >/dev/null 2>&1 </dev/null \
    || { echo "  ERROR  $name"; fail=1; continue; }
  status="$(od -An -tu8 -j 0 -N 8 "$out" | tr -d ' \n')"
  path_ptr="$(od -An -tu8 -j 8 -N 8 "$out" | tr -d ' \n')"
  path_len="$(od -An -tu8 -j 16 -N 8 "$out" | tr -d ' \n')"
  value_ptr="$(od -An -tu8 -j 24 -N 8 "$out" | tr -d ' \n')"
  value_len="$(od -An -tu8 -j 32 -N 8 "$out" | tr -d ' \n')"
  is_insert="$(od -An -tu8 -j 40 -N 8 "$out" | tr -d ' \n')"
  actual_path="$(xxd -p -s 48 -l 64 "$out" | tr -d '\n')"
  actual_value="$(xxd -p -s 112 -l "$value_len" "$out" | tr -d '\n')"
  expected_path="$(cat "$VDIR/$name.path")"
  expected_value="$(cat "$VDIR/$name.value")"
  expected_flag="$(cat "$VDIR/$name.flag")"
  expected_len=$(( ${#expected_value} / 2 ))
  if [[ "$status" == "0" && "$path_ptr" == "2684420144" && "$path_len" == "64" && "$value_ptr" == "2684420208" && "$value_len" == "$expected_len" && "$is_insert" == "$expected_flag" && "$actual_path" == "$expected_path" && "$actual_value" == "$expected_value" ]]; then
    echo "  PASS   $name  value_len=$value_len is_insert=$is_insert"
  else
    echo "  FAIL   $name status=$status"
    echo "    desc path_ptr=$path_ptr path_len=$path_len value_ptr=$value_ptr value_len=$value_len is_insert=$is_insert"
    echo "    expected path=$expected_path len=$expected_len flag=$expected_flag value=$expected_value"
    echo "    actual   path=$actual_path value=$actual_value"
    fail=1
  fi
done < "$VDIR/baacd_cases.txt"
[[ "$fail" -eq 0 ]] && echo "==> PASS: bal_account_change_descriptor matches reference" \
  || { echo "==> FAIL"; exit 1; }
