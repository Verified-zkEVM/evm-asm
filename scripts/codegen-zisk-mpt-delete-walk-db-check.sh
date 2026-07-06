#!/usr/bin/env bash
# Verify mpt_delete_walk_db on existing-key trie shapes. The probe uses the
# DB-aware set-walk metadata layout; delete-specific collapse is covered by the
# follow-up mpt_delete_acc primitive.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

VDIR="$REPO_ROOT/gen-out/mpt-delete-walk-db"
mkdir -p "$VDIR"
echo "==> generate delete-walk vectors"
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

def leaf_node(path_nibbles: list[int], value: bytes) -> bytes:
    return rlp_list([rlp_bytes(hp_encode(path_nibbles, True)), rlp_bytes(value)])

def extension_node(path_nibbles: list[int], child_ref: bytes) -> bytes:
    hp = rlp_bytes(hp_encode(path_nibbles, False))
    return rlp_len_prefix(len(hp) + len(child_ref), 0xC0) + hp + child_ref

def branch_node(slots: list[bytes], value: bytes = b"") -> bytes:
    return rlp_list(slots + [rlp_bytes(value)])

def node_ref(node: bytes) -> bytes:
    return node if len(node) < 32 else b"\xa0" + k256(node)

def root(node: bytes) -> bytes:
    return k256(node)

def ssz_section(elements: list[bytes]) -> bytes:
    out = bytearray(); off = 4 * len(elements)
    for e in elements:
        out += struct.pack("<I", off); off += len(e)
    for e in elements:
        out += e
    return bytes(out)

def build_input(root_hash: bytes, path: list[int], witness: list[bytes]) -> bytes:
    body = bytearray()
    body += struct.pack("<Q", len(ssz_section(witness)))
    body += struct.pack("<Q", len(path))
    body += struct.pack("<Q", 0)
    body += root_hash
    body += bytes(path)
    while len(body) % 8:
        body += b"\x00"
    body += ssz_section(witness)
    while len(body) % 8:
        body += b"\x00"
    return bytes(body)

def write_case(name: str, witness: list[bytes], r: bytes, path: list[int], levels: list[tuple[str, int, int]]) -> None:
    with open(f"{outdir}/{name}.input", "wb") as f:
        f.write(build_input(r, path, witness))
    depth = len(levels)
    consumed = sum(c for _, _, c in levels)
    rows = [
        ("status", 0, 0),
        ("depth", 8, depth),
        ("consumed", 16, consumed),
        ("leaf_len", 32, len(witness[depth])),
    ]
    for i, (kind, nibble, _) in enumerate(levels):
        base = 128 + 32 * i
        rows += [
            (f"rec{i}_len", base + 8, len(witness[i])),
            (f"rec{i}_kind", base + 16, 0 if kind == "branch" else 1),
            (f"rec{i}_nibble", base + 24, nibble),
        ]
    with open(f"{outdir}/{name}.rwexpected", "w") as f:
        for field, off, val in rows:
            f.write(f"{field} {off} {val}\n")

old = b"A" * 32
leaf = leaf_node([1, 2, 3, 4], b"old-value")
write_case("leaf", [leaf], root(leaf), [1, 2, 3, 4], [])

la = leaf_node([0xa, 0xb], old)
lb = leaf_node([0xc, 0xd], b"b-val")
slots = [b"\x80"] * 16
slots[1] = node_ref(la); slots[2] = node_ref(lb)
br = branch_node(slots)
write_case("branch", [br, la], root(br), [1, 0xa, 0xb], [("branch", 1, 1)])

slots2 = [b"\x80"] * 16
slots2[1] = node_ref(la); slots2[2] = node_ref(lb)
br2 = branch_node(slots2)
ext = extension_node([5, 6], node_ref(br2))
write_case("ext_branch", [ext, br2, la], root(ext), [5, 6, 1, 0xa, 0xb], [("extension", 0, 2), ("branch", 1, 1)])
PY

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_mpt_delete_walk_db probe ELF"
lake exe codegen --program zisk_mpt_delete_walk_db --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_mpt_delete_walk_db"

read_u64() { od -An -tu8 -j "$2" -N 8 "$1" | tr -d ' \n'; }

fail=0
for name in leaf branch ext_branch; do
  out="$VDIR/$name.mdwdb.output"
  if ! "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_mpt_delete_walk_db.elf" \
        -i "$VDIR/$name.input" -o "$out" -n 5000000 >/dev/null 2>&1 </dev/null; then
    echo "  ERROR  $name (ziskemu)"; fail=1; continue
  fi
  shape_ok=1; details=""
  while read -r field off exp; do
    [[ -z "$field" ]] && continue
    case "$field" in
      status|depth|consumed|leaf_len|rec*_len|rec*_kind|rec*_nibble) ;;
      *) continue ;;
    esac
    act="$(read_u64 "$out" "$off")"
    if [[ "$act" != "$exp" ]]; then
      shape_ok=0; details+=$'\n'"      $field @${off}: expected $exp got $act"
    fi
  done < "$VDIR/$name.rwexpected"
  if [[ "$shape_ok" -eq 1 ]]; then
    d="$(read_u64 "$out" 8)"; c="$(read_u64 "$out" 16)"
    echo "  PASS   $name  (depth=$d consumed=$c)"
  else
    echo "  FAIL   $name$details"; fail=1
  fi
done

[[ "$fail" -eq 0 ]] && echo "==> PASS: mpt_delete_walk_db existing-key walk matches reference shapes" \
  || { echo "==> FAIL"; exit 1; }
