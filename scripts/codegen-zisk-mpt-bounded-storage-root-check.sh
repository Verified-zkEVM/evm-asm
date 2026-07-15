#!/usr/bin/env bash
# Storage specialization KATs for sd13v's bounded root builder.
#
# The builder receives already-RLP-encoded storage values.  These cases prove
# the uint256 write bound (1 byte and the full 33-byte RLP form), deletion to
# the canonical empty root, and that a larger unchanged witness leaf is not
# rejected merely because constructed storage writes are bounded to 33 bytes.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
workdir="$(mktemp -d)"; trap 'rm -rf "$workdir"' EXIT
bash scripts/codegen-force-relink.sh >/dev/null
lake exe codegen --program zisk_mpt_bounded_storage_root --halt linux93 -o "$workdir/root" >/dev/null
uv run --directory execution-specs --quiet python3 - "$workdir" <<'PY'
from ethereum.crypto.hash import keccak256
import pathlib, struct, sys

root = pathlib.Path(sys.argv[1])
EMPTY_TRIE_ROOT = bytes.fromhex("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")
path = [0] * 64

def rlp_len_prefix(length, base):
    if length < 56:
        return bytes([base + length])
    raw = length.to_bytes((length.bit_length() + 7) // 8, "big")
    return bytes([base + 55 + len(raw)]) + raw

def rlp_bytes(value):
    if len(value) == 1 and value[0] < 0x80:
        return value
    return rlp_len_prefix(len(value), 0x80) + value

def hp_leaf(nibbles):
    assert len(nibbles) % 2 == 0
    return bytes([0x20]) + bytes((nibbles[i] << 4) | nibbles[i + 1]
                                for i in range(0, len(nibbles), 2))

def leaf_node(nibbles, value):
    payload = rlp_bytes(hp_leaf(nibbles)) + rlp_bytes(value)
    return rlp_len_prefix(len(payload), 0xc0) + payload
cases = [
    # An empty storage trie has no witness node.  Inserting its first slot
    # must construct the canonical one-leaf trie directly.
    ("empty_insert", None, b"\x01", 1),
    # The canonical uint256 encoding of 1 is its one-byte RLP form.
    ("one", b"", b"\x01", 0),
    # A full uint256 has 32 payload bytes and RLP byte-string prefix 0xa0.
    ("max", b"\x01", b"\xa0" + b"\xff" * 32, 0),
    # This cannot arise as a constructed uint256 value, but a valid committed
    # witness leaf must not be rejected solely by the write-side 33-byte cap.
    ("wide_witness", b"\xb8\x22" + b"\x7f" * 34, b"\x01", 0),
    # Zero is represented by deleting the leaf, never by a stored empty value.
    ("delete", b"\x01", None, 2),
]
for name, old_value, new_value, mode in cases:
    old = leaf_node(path, old_value) if old_value is not None else None
    section = struct.pack('<I', 4) + old if old is not None else b""
    value = new_value or b""
    assert len(value) <= 40
    # The storage probe uses a fixed 40-byte descriptor-value field so the
    # mode and witness offsets remain stable for the 33-byte max-u256 case.
    old_root = keccak256(old) if old is not None else EMPTY_TRIE_ROOT
    blob = (struct.pack('<Q', len(section)) + old_root + b'\0' * 64 +
            struct.pack('<Q', len(value)) + value.ljust(40, b'\0') +
            struct.pack('<Q', mode) + section)
    (root / f'{name}.input').write_bytes(blob + b'\0' * (-len(blob) % 8))
    expected = EMPTY_TRIE_ROOT if mode == 2 else keccak256(leaf_node(path, new_value))
    (root / f'{name}.expected').write_bytes(expected)
PY
for case in empty_insert one max wide_witness delete; do
  "$ZISKEMU" -e "$workdir/root.elf" -i "$workdir/$case.input" -o "$workdir/$case.output" -n 2000000 >/dev/null </dev/null
  python3 - "$workdir" "$case" <<'PY'
import pathlib, struct, sys
root = pathlib.Path(sys.argv[1]); case = sys.argv[2]
out = (root / f'{case}.output').read_bytes()
status = struct.unpack_from('<Q', out)[0]
assert status == 0, (case, status)
assert out[8:40] == (root / f'{case}.expected').read_bytes(), case
PY
done
echo 'PASS: bounded storage root handles 1, max uint256, wide witness, and delete'
