#!/usr/bin/env bash
# Verify mpt_delete_acc deletion slices: single-leaf deletion, branch-only
# deletion without canonical collapse, and covered branch-collapse cases.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

VDIR="$REPO_ROOT/gen-out/mpt-delete-acc"
mkdir -p "$VDIR"
echo "==> generate delete-acc vectors"
uv run --directory execution-specs --quiet python3 - "$VDIR" <<'PY'
from __future__ import annotations
import struct, sys
from Crypto.Hash import keccak

outdir = sys.argv[1]

def k256(b: bytes) -> bytes:
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

def rlp_len_prefix(length: int, base: int) -> bytes:
    if length < 56:
        return bytes([base + length])
    bl = length.to_bytes((length.bit_length() + 7) // 8, "big")
    return bytes([base + 55 + len(bl)]) + bl

def rlp_bytes(b: bytes) -> bytes:
    if len(b) == 1 and b[0] < 0x80:
        return b
    return rlp_len_prefix(len(b), 0x80) + b

def rlp_list(items: list[bytes]) -> bytes:
    payload = b"".join(items)
    return rlp_len_prefix(len(payload), 0xC0) + payload

def hp_encode(nibbles: list[int], is_leaf: bool) -> bytes:
    flag = (2 if is_leaf else 0) + (1 if len(nibbles) % 2 else 0)
    out = bytearray()
    if len(nibbles) % 2 == 1:
        out.append(flag * 16 + nibbles[0]); nibbles = nibbles[1:]
    else:
        out.append(flag * 16)
    for i in range(0, len(nibbles), 2):
        out.append(nibbles[i] * 16 + nibbles[i + 1])
    return bytes(out)

def leaf_node(path: list[int], value: bytes) -> bytes:
    return rlp_list([rlp_bytes(hp_encode(path, True)), rlp_bytes(value)])

def extension_node(path: list[int], child_ref: bytes) -> bytes:
    return rlp_list([rlp_bytes(hp_encode(path, False)), child_ref])

def branch_node(slots: list[bytes], value: bytes = b"") -> bytes:
    return rlp_list(slots + [rlp_bytes(value)])

def node_ref(node: bytes) -> bytes:
    return node if len(node) < 32 else b"\xa0" + k256(node)

def trie_root(node: bytes) -> bytes:
    return k256(node)

EMPTY_TRIE_ROOT = bytes.fromhex("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")

def ssz_section(elements: list[bytes]) -> bytes:
    out = bytearray(); off = 4 * len(elements)
    for e in elements:
        out += struct.pack("<I", off); off += len(e)
    for e in elements:
        out += e
    return bytes(out)

def build_input(root_hash: bytes, path: list[int], witness: list[bytes]) -> bytes:
    body = bytearray()
    sec = ssz_section(witness)
    body += struct.pack("<Q", len(sec))
    body += struct.pack("<Q", len(path))
    body += root_hash
    body += bytes(path)
    while len(body) % 8:
        body += b"\x00"
    body += sec
    while len(body) % 8:
        body += b"\x00"
    return bytes(body)

def write_case(name: str, root_hash: bytes, path: list[int], witness: list[bytes], expected: bytes, status: int = 0) -> None:
    with open(f"{outdir}/{name}.input", "wb") as f:
        f.write(build_input(root_hash, path, witness))
    with open(f"{outdir}/{name}.expected", "w") as f:
        f.write(expected.hex())
    with open(f"{outdir}/{name}.status", "w") as f:
        f.write(str(status))

leaf = leaf_node([1, 2, 3, 4], b"old-value")
write_case("leaf_to_empty", trie_root(leaf), [1, 2, 3, 4], [leaf], EMPTY_TRIE_ROOT)

la = leaf_node([0xa, 0xb], b"A" * 32)
lb = leaf_node([0xc, 0xd], b"B" * 32)
lc = leaf_node([0xe, 0xf], b"C" * 32)
slots = [b"\x80"] * 16
slots[1] = node_ref(la); slots[2] = node_ref(lb); slots[3] = node_ref(lc)
root = branch_node(slots)
slots2 = list(slots); slots2[1] = b"\x80"
root2 = branch_node(slots2)
write_case("branch_no_collapse", trie_root(root), [1, 0xa, 0xb], [root, la], trie_root(root2))

slots3 = [b"\x80"] * 16
slots3[1] = node_ref(la); slots3[2] = node_ref(lb)
root3 = branch_node(slots3)
collapsed = leaf_node([2, 0xc, 0xd], b"B" * 32)
write_case("branch_collapse_leaf", trie_root(root3), [1, 0xa, 0xb], [root3, la, lb], trie_root(collapsed))

slots4 = [b"\x80"] * 16
slots4[1] = node_ref(la)
root4 = branch_node(slots4, b"branch-value")
collapsed_value = leaf_node([], b"branch-value")
write_case("branch_value_collapse", trie_root(root4), [1, 0xa, 0xb], [root4, la], trie_root(collapsed_value))

ext = extension_node([3, 4], node_ref(lb))
slots5 = [b"\x80"] * 16
slots5[1] = node_ref(la); slots5[2] = node_ref(ext)
root5 = branch_node(slots5)
collapsed_ext = extension_node([2, 3, 4], node_ref(lb))
write_case("branch_collapse_extension", trie_root(root5), [1, 0xa, 0xb], [root5, la, ext], trie_root(collapsed_ext))

child_slots = [b"\x80"] * 16
child_slots[4] = node_ref(lc)
child_branch = branch_node(child_slots, b"child-branch-value")
slots6 = [b"\x80"] * 16
slots6[1] = node_ref(la); slots6[2] = node_ref(child_branch)
root6 = branch_node(slots6)
collapsed_branch = extension_node([2], node_ref(child_branch))
write_case("branch_collapse_branch", trie_root(root6), [1, 0xa, 0xb], [root6, la, child_branch], trie_root(collapsed_branch))

la_small = leaf_node([0xa], b"A")
lb_small = leaf_node([0xc], b"B")
assert len(la_small) < 32 and len(lb_small) < 32
slots_inline_leaf = [b"\x80"] * 16
slots_inline_leaf[1] = node_ref(la_small); slots_inline_leaf[2] = node_ref(lb_small)
root_inline_leaf = branch_node(slots_inline_leaf)
collapsed_inline_leaf = leaf_node([2, 0xc], b"B")
write_case("branch_collapse_inline_leaf", trie_root(root_inline_leaf), [1, 0xa],
           [root_inline_leaf, la_small], trie_root(collapsed_inline_leaf))

ext_small = extension_node([3], node_ref(lb_small))
assert len(ext_small) < 32
slots_inline_ext = [b"\x80"] * 16
slots_inline_ext[1] = node_ref(la_small); slots_inline_ext[2] = node_ref(ext_small)
root_inline_ext = branch_node(slots_inline_ext)
collapsed_inline_ext = extension_node([2, 3], node_ref(lb_small))
write_case("branch_collapse_inline_extension", trie_root(root_inline_ext), [1, 0xa],
           [root_inline_ext, la_small], trie_root(collapsed_inline_ext))

lc_small = leaf_node([0xe], b"C")
ld_small = leaf_node([0xf], b"D")
assert len(lc_small) < 32 and len(ld_small) < 32
child_slots_inline = [b"\x80"] * 16
child_slots_inline[4] = node_ref(lc_small); child_slots_inline[5] = node_ref(ld_small)
child_branch_inline = branch_node(child_slots_inline)
assert len(child_branch_inline) < 32
slots_inline_branch = [b"\x80"] * 16
slots_inline_branch[1] = node_ref(la_small); slots_inline_branch[2] = node_ref(child_branch_inline)
root_inline_branch = branch_node(slots_inline_branch)
collapsed_inline_branch = extension_node([2], node_ref(child_branch_inline))
write_case("branch_collapse_inline_branch", trie_root(root_inline_branch), [1, 0xa],
           [root_inline_branch, la_small], trie_root(collapsed_inline_branch))

# The survivor branch has a non-empty slot 0 whose hash begins with a high
# nibble that looks like a compact leaf prefix. Delete collapse must classify
# the survivor as a branch before trying leaf/extension extractors.
leaf_like_hash_child = leaf_node([0xa, 0xb], (1).to_bytes(2, "big") + b"X" * 30)
assert k256(leaf_like_hash_child)[0] >> 4 in (2, 3)
survivor_slots = [b"\x80"] * 16
survivor_slots[0] = node_ref(leaf_like_hash_child)
survivor_slots[4] = node_ref(lc)
survivor_branch = branch_node(survivor_slots)
slots6b = [b"\x80"] * 16
slots6b[1] = node_ref(la); slots6b[2] = node_ref(survivor_branch)
root6b = branch_node(slots6b)
collapsed_branch6b = extension_node([2], node_ref(survivor_branch))
write_case("branch_collapse_branch_leaflike_slot0", trie_root(root6b), [1, 0xa, 0xb],
           [root6b, la, survivor_branch, leaf_like_hash_child, lc],
           trie_root(collapsed_branch6b))

slots7 = [b"\x80"] * 16
slots7[1] = node_ref(la); slots7[2] = node_ref(lb); slots7[3] = node_ref(lc)
branch7 = branch_node(slots7)
root7 = extension_node([9, 9], node_ref(branch7))
slots7_after = list(slots7); slots7_after[1] = b"\x80"
branch7_after = branch_node(slots7_after)
collapsed_root7 = extension_node([9, 9], node_ref(branch7_after))
write_case("extension_bubble_branch_no_collapse", trie_root(root7), [9, 9, 1, 0xa, 0xb], [root7, branch7, la], trie_root(collapsed_root7))

slots8 = [b"\x80"] * 16
slots8[1] = node_ref(la); slots8[2] = node_ref(lb)
branch8 = branch_node(slots8)
root8 = extension_node([9, 9], node_ref(branch8))
collapsed_root8 = leaf_node([9, 9, 2, 0xc, 0xd], b"B" * 32)
write_case("extension_merge_leaf", trie_root(root8), [9, 9, 1, 0xa, 0xb], [root8, branch8, la, lb], trie_root(collapsed_root8))

ext9 = extension_node([3, 4], node_ref(lb))
slots9 = [b"\x80"] * 16
slots9[1] = node_ref(la); slots9[2] = node_ref(ext9)
branch9 = branch_node(slots9)
root9 = extension_node([9, 9], node_ref(branch9))
collapsed_root9 = extension_node([9, 9, 2, 3, 4], node_ref(lb))
write_case("extension_merge_extension", trie_root(root9), [9, 9, 1, 0xa, 0xb], [root9, branch9, la, ext9], trie_root(collapsed_root9))
PY

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_mpt_delete_acc probe ELF"
lake exe codegen --program zisk_mpt_delete_acc --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_mpt_delete_acc"

read_u64() { od -An -tu8 -j "$2" -N 8 "$1" | tr -d ' \n'; }

fail=0
for name in leaf_to_empty branch_no_collapse branch_collapse_leaf branch_value_collapse branch_collapse_extension branch_collapse_branch branch_collapse_inline_leaf branch_collapse_inline_extension branch_collapse_inline_branch branch_collapse_branch_leaflike_slot0 extension_bubble_branch_no_collapse extension_merge_leaf extension_merge_extension; do
  out="$VDIR/$name.output"
  if ! "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_mpt_delete_acc.elf" \
        -i "$VDIR/$name.input" -o "$out" -n 10000000 >/dev/null 2>&1 </dev/null; then
    echo "  ERROR  $name (ziskemu)"; fail=1; continue
  fi
  exp="$(cat "$VDIR/$name.expected")"
  exp_status="$(cat "$VDIR/$name.status")"
  act="$(od -An -tx1 -N 32 "$out" | tr -d ' \n')"
  st="$(read_u64 "$out" 32)"
  if [[ "$st" == "$exp_status" ]] && { [[ "$exp_status" != "0" ]] || [[ "$act" == "$exp" ]]; }; then
    echo "  PASS   $name"
  else
    echo "  FAIL   $name"
    echo "      root expected $exp"
    echo "      root actual   $act"
    echo "      status        $st (expected $exp_status)"
    fail=1
  fi
done

[[ "$fail" -eq 0 ]] && echo "==> PASS: mpt_delete_acc vectors match Python roots" \
  || { echo "==> FAIL"; exit 1; }
