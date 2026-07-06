#!/usr/bin/env bash
# codegen-zisk-bal-account-final-descriptor-array-check.sh -- verify BAL final descriptor compaction.
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
echo "==> generate BAL final descriptor-array vector"
uv run --directory execution-specs --quiet python3 - "$VDIR" <<'PYGEN'
import os
import struct
import sys
from ethereum.crypto.hash import keccak256

outdir = sys.argv[1]
os.makedirs(outdir, exist_ok=True)

OUTPUT = 0xA0010000
DESC_BASE = OUTPUT + 16
PATH_BASE = OUTPUT + 96
VALUE_BASE = OUTPUT + 224


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


def account_rlp(nonce: int, balance: int) -> bytes:
    return rlp_list([rlp_int(nonce), rlp_int(balance), rlp_bytes(b""), rlp_bytes(b"")])


def change_pair(index: int, value: bytes) -> bytes:
    return rlp_list([rlp_int(index), value])


def account_change(address: bytes, balance_changes=None, nonce_changes=None) -> bytes:
    balance_changes = balance_changes or []
    nonce_changes = nonce_changes or []
    bc = [change_pair(i, rlp_int(v)) for i, v in balance_changes]
    nc = [change_pair(i, rlp_int(v)) for i, v in nonce_changes]
    return rlp_list([rlp_bytes(address), rlp_list([]), rlp_list([]),
                     rlp_list(bc), rlp_list(nc), rlp_list([])])


def account_path(address: bytes) -> bytes:
    out = bytearray()
    for b in keccak256(address):
        out.append(b >> 4)
        out.append(b & 0x0f)
    return bytes(out)


def align8(n: int) -> int:
    return (n + 7) & ~7


def build_input(accounts, flags, bal_list: bytes) -> bytes:
    body = struct.pack("<QQ", len(bal_list), len(accounts))
    for account, flag in zip(accounts, flags):
        body += struct.pack("<QQ", len(account), flag)
    for account in accounts:
        body += account
        while len(body) % 8 != 0:
            body += b"\x00"
    body += bal_list
    while len(body) % 8 != 0:
        body += b"\x00"
    return body


base = account_rlp(1, 5)
addr0 = bytes.fromhex("c0f6dc9e5836f54caadbf59cc69346c508e1992b")
addr1 = bytes.fromhex("0000000000000000000000000000000000000001")
addr2 = bytes.fromhex("0000000000000000000000000000000000000002")
changes = [
    account_change(addr0, balance_changes=[(1, 10)]),
    account_change(addr1),
    account_change(addr0, balance_changes=[(1, 20)]),
    account_change(addr2, balance_changes=[(1, 9)], nonce_changes=[(1, 7)]),
]
bal_list = rlp_list(changes)
accounts = [base, base, base, base]
flags = [0, 0, 0, 1]
paths = [account_path(addr0), account_path(addr2)]
values = [account_rlp(1, 20), account_rlp(7, 9)]
modes = [0, 1]

with open(f"{outdir}/badf_compact.input", "wb") as f:
    f.write(build_input(accounts, flags, bal_list))

value_cursor = VALUE_BASE
expected_desc = []
for i, (path, value, mode) in enumerate(zip(paths, values, modes)):
    expected_desc.append((PATH_BASE + 64 * i, 64, value_cursor, len(value), mode))
    value_cursor += align8(len(value))

with open(f"{outdir}/badf_compact.expected", "w") as f:
    f.write("\n".join("\t".join(map(str, row)) for row in expected_desc))
with open(f"{outdir}/badf_compact.paths", "w") as f:
    f.write("\n".join(p.hex() for p in paths))
with open(f"{outdir}/badf_compact.values", "w") as f:
    f.write("\n".join(v.hex() for v in values))
print("badf_compact input_rows=4 final_rows=2 repeated_addr_keeps_last=true")
PYGEN

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_bal_account_final_descriptor_array probe ELF"
lake exe codegen --program zisk_bal_account_final_descriptor_array --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_bal_account_final_descriptor_array"

out="$VDIR/badf_compact.output"
"$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_bal_account_final_descriptor_array.elf" \
  -i "$VDIR/badf_compact.input" -o "$out" -n 3000000 >/dev/null 2>&1 </dev/null

status="$(od -An -tu8 -j 0 -N 8 "$out" | tr -d ' \n')"
count="$(od -An -tu8 -j 8 -N 8 "$out" | tr -d ' \n')"
fail=0
if [[ "$status" != "0" || "$count" != "2" ]]; then
  echo "  FAIL   badf_compact status=$status count=$count"
  fail=1
fi

mapfile -t exp_desc < "$VDIR/badf_compact.expected"
mapfile -t exp_paths < "$VDIR/badf_compact.paths"
mapfile -t exp_values < "$VDIR/badf_compact.values"
value_copy_off=224
for i in 0 1; do
  desc_off=$((16 + 40 * i))
  IFS=$'\t' read -r exp_path_ptr exp_path_len exp_value_ptr exp_value_len exp_mode <<< "${exp_desc[$i]}"
  path_ptr="$(od -An -tu8 -j "$desc_off" -N 8 "$out" | tr -d ' \n')"
  path_len="$(od -An -tu8 -j $((desc_off + 8)) -N 8 "$out" | tr -d ' \n')"
  value_ptr="$(od -An -tu8 -j $((desc_off + 16)) -N 8 "$out" | tr -d ' \n')"
  value_len="$(od -An -tu8 -j $((desc_off + 24)) -N 8 "$out" | tr -d ' \n')"
  mode="$(od -An -tu8 -j $((desc_off + 32)) -N 8 "$out" | tr -d ' \n')"
  path="$(xxd -p -s $((96 + 64 * i)) -l 64 "$out" | tr -d '\n')"
  value="$(xxd -p -s "$value_copy_off" -l "$value_len" "$out" | tr -d '\n')"
  if [[ "$path_ptr" != "$exp_path_ptr" || "$path_len" != "$exp_path_len" || "$value_ptr" != "$exp_value_ptr" || "$value_len" != "$exp_value_len" || "$mode" != "$exp_mode" || "$path" != "${exp_paths[$i]}" || "$value" != "${exp_values[$i]}" ]]; then
    echo "  FAIL   badf_compact row=$i"
    echo "    desc path_ptr=$path_ptr path_len=$path_len value_ptr=$value_ptr value_len=$value_len mode=$mode"
    echo "    expected path_ptr=$exp_path_ptr path_len=$exp_path_len value_ptr=$exp_value_ptr value_len=$exp_value_len mode=$exp_mode"
    echo "    path expected=${exp_paths[$i]} actual=$path"
    echo "    value expected=${exp_values[$i]} actual=$value"
    fail=1
  else
    echo "  PASS   badf_compact row=$i value_len=$value_len mode=$mode"
  fi
  value_copy_off=$(( (value_copy_off + value_len + 7) & ~7 ))
done

[[ "$fail" -eq 0 ]] && echo "==> PASS: bal_account_final_descriptor_array compacts to final rows" \
  || { echo "==> FAIL"; exit 1; }
