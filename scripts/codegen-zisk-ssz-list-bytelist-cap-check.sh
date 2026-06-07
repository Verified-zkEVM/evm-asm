#!/usr/bin/env bash
# codegen-zisk-ssz-list-bytelist-cap-check.sh -- verify PR-S11 bounds.
#
# The helper stages child roots in a 1024-byte scratch buffer, so it supports at
# most 32 ByteList elements. Each nested ByteList root currently uses the
# 1024-byte ssz_hash_tree_root_bytes scratch. This script checks one valid root
# against a Python SSZ recomputation and checks that oversized cases return a
# nonzero status with a zero output root.
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

VDIR="gen-out/ssz-list-bytelist-cap"
mkdir -p "$VDIR"

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_ssz_hash_tree_root_list_bytelist ELF"
lake exe codegen --program zisk_ssz_hash_tree_root_list_bytelist --halt linux93 \
  -o gen-out/zisk_ssz_hash_tree_root_list_bytelist >/dev/null

python3 - "$VDIR" <<'PY'
import hashlib
import os
import struct
import sys

VDIR = sys.argv[1]

def zero_hashes(depth):
    zs = [b"\x00" * 32]
    for _ in range(depth + 1):
        zs.append(hashlib.sha256(zs[-1] + zs[-1]).digest())
    return zs

def merkleize(chunks, limit_log2):
    zs = zero_hashes(max(limit_log2, 1))
    n = len(chunks)
    if n == 0:
        return zs[limit_log2]
    m = 1
    depth = 0
    while m < n:
        m <<= 1
        depth += 1
    layer = list(chunks) + [zs[0]] * (m - n)
    while len(layer) > 1:
        layer = [
            hashlib.sha256(layer[2 * i] + layer[2 * i + 1]).digest()
            for i in range(len(layer) // 2)
        ]
    root = layer[0]
    while depth < limit_log2:
        root = hashlib.sha256(root + zs[depth]).digest()
        depth += 1
    return root

def bytelist_root(value, byte_log2):
    padded = value + b"\x00" * ((-len(value)) % 32)
    chunks = [padded[i : i + 32] for i in range(0, len(padded), 32)]
    partial = merkleize(chunks, byte_log2)
    return hashlib.sha256(partial + len(value).to_bytes(32, "little")).digest()

def list_root(elements, byte_log2, count_log2):
    child_roots = [bytelist_root(e, byte_log2) for e in elements]
    partial = merkleize(child_roots, count_log2)
    return hashlib.sha256(partial + len(elements).to_bytes(32, "little")).digest()

def section(elements):
    if not elements:
        return b""
    off = 4 * len(elements)
    offsets = []
    body = b""
    for e in elements:
        offsets.append(off)
        body += e
        off += len(e)
    return b"".join(struct.pack("<I", o) for o in offsets) + body

def write_case(name, elements, byte_log2, count_log2, status):
    sec = section(elements)
    with open(os.path.join(VDIR, f"{name}.input"), "wb") as f:
        f.write(struct.pack("<Q", len(sec)))
        f.write(struct.pack("<Q", byte_log2))
        f.write(struct.pack("<Q", count_log2))
        f.write(sec)
        pad = (-(24 + len(sec))) % 8
        if pad:
            f.write(b"\x00" * pad)
    if status == 0:
        root = list_root(elements, byte_log2, count_log2)
    else:
        root = b"\x00" * 32
    with open(os.path.join(VDIR, f"{name}.expected"), "w") as f:
        f.write(root.hex() + f" {status}\n")

write_case("valid-three", [b"a", b"bc", bytes(range(40))], 2, 5, 0)
write_case("too-many", [bytes([i]) for i in range(33)], 0, 6, 1)
write_case("too-large-element", [b"x" * 1025], 6, 5, 1)
PY

run_case() {
  local name="$1"
  local out="$VDIR/$name.output"
  "$ZISKEMU" -e gen-out/zisk_ssz_hash_tree_root_list_bytelist.elf \
    -i "$VDIR/$name.input" -o "$out" -n 5000000 \
    >"$VDIR/$name.emu.log" 2>&1 || { echo "  ERROR $name"; exit 1; }
  local actual_root actual_status expected_root expected_status
  actual_root="$(xxd -p -l 32 "$out" | tr -d '\n')"
  actual_status="$(od -An -tu8 -j 32 -N 8 "$out" | tr -d ' \n')"
  read expected_root expected_status < "$VDIR/$name.expected"
  if [[ "$actual_root" == "$expected_root" && "$actual_status" == "$expected_status" ]]; then
    printf "  %-18s OK status=%s\n" "$name" "$actual_status"
  else
    printf "  %-18s FAIL\n    root exp=%s act=%s\n    status exp=%s act=%s\n" \
      "$name" "$expected_root" "$actual_root" "$expected_status" "$actual_status"
    exit 1
  fi
}

run_case valid-three
run_case too-many
run_case too-large-element

echo "==> PASS: ssz_hash_tree_root_list_bytelist enforces helper bounds"
