#!/usr/bin/env bash
# codegen-zisk-block-validate-receipts-root-indexed-check.sh
#
# Validate the descriptor-array receipts_root path against execution-specs'
# indexed MPT root implementation for 0, 1, 2, and N>2 receipts.
set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_block_validate_receipts_root_indexed ELF"
lake exe codegen --program zisk_block_validate_receipts_root_indexed --halt linux93 \
  -o gen-out/zisk_block_validate_receipts_root_indexed

read_u64() { od -An -tu8 -j "$2" -N 8 "$1" | tr -d ' \n'; }

run_case() {
  local name="$1"
  local receipts_py="$2"
  local override="$3"
  local exp_status="$4"
  local exp_valid="$5"
  local in_file="$REPO_ROOT/gen-out/zisk_block_validate_receipts_root_indexed_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_validate_receipts_root_indexed_${name}.output"

  uv run --directory execution-specs --quiet python3 - "$in_file" <<PYGEN
import struct, sys
from ethereum.merkle_patricia_trie import Trie, trie_set, root
from ethereum_rlp import rlp
from ethereum_types.bytes import Bytes
from ethereum_types.numeric import Uint

receipts = $receipts_py
override = "$override"
vals = [bytes.fromhex(v) for v in receipts]

trie = Trie(secured=False, default=None)
for i, value in enumerate(vals):
    trie_set(trie, Bytes(rlp.encode(Uint(i))), Bytes(value))
correct_root = bytes(root(trie))

if override == "garbage":
    header_rlp = b"\x00"
else:
    if override == "":
        field5 = correct_root
    elif override == "wrong":
        field5 = bytes.fromhex("ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100")
    elif override == "short":
        field5 = b"\xaa" * 16
    else:
        raise ValueError(f"unknown override {override!r}")
    fields = [
        b"\x11"*32, b"\x22"*32, b"\x33"*20, b"\x44"*32, b"\x55"*32,
        field5, b"\x00"*256, b"", b"\x01", b"\x83\xff\xff\xff",
        b"", b"\x83\x01\x02\x03", b"", b"\x77"*32, b"\x00"*8,
    ]
    header_rlp = rlp.encode(fields)

with open(sys.argv[1], "wb") as f:
    f.write(struct.pack("<Q", len(header_rlp)))
    f.write(struct.pack("<Q", len(vals)))
    for value in vals:
        f.write(struct.pack("<Q", len(value)))
    f.write(header_rlp)
    f.write(b"\x00" * ((-len(header_rlp)) % 8))
    for value in vals:
        f.write(value)
        f.write(b"\x00" * ((-len(value)) % 8))
PYGEN

  if ! "$ZISKEMU" -e gen-out/zisk_block_validate_receipts_root_indexed.elf \
        -i "$in_file" -o "$out_file" -n 30000000 >/dev/null 2>&1 </dev/null; then
    printf "  %-28s ERROR ziskemu\n" "$name"
    return 1
  fi

  local status valid
  status="$(read_u64 "$out_file" 0)"
  valid="$(read_u64 "$out_file" 8)"
  if [[ "$status" == "$exp_status" && "$valid" == "$exp_valid" ]]; then
    printf "  %-28s OK   status=%s valid=%s\n" "$name" "$status" "$valid"
    return 0
  fi

  printf "  %-28s FAIL status=%s/%s valid=%s/%s\n" \
    "$name" "$status" "$exp_status" "$valid" "$exp_valid"
  return 1
}

receipt_hex() {
  uv run --directory execution-specs --quiet python3 - "$1" <<'PYREC'
import sys
from ethereum_rlp import rlp
from ethereum_types.numeric import Uint
status = int(sys.argv[1])
cum_gas = 21000 * (status + 1)
receipt = rlp.encode([Uint(status), Uint(cum_gas), b"\x00" * 256, []])
print(receipt.hex())
PYREC
}

R0="$(receipt_hex 0)"
R1="$(receipt_hex 1)"
R2="$(receipt_hex 2)"
R3="$(receipt_hex 3)"
R4="$(receipt_hex 4)"

CASES=(
  "empty|[]||0|1"
  "one|['$R0']||0|1"
  "two|['$R0','$R1']||0|1"
  "five|['$R0','$R1','$R2','$R3','$R4']||0|1"
  "mismatch_wrong_root|['$R0','$R1','$R2']|wrong|0|0"
  "header_short_root|['$R0']|short|2|0"
  "header_parse_fail|['$R0']|garbage|1|0"
)

FAILED=0
for row in "${CASES[@]}"; do
  IFS='|' read -r name receipts override exp_status exp_valid <<<"$row"
  run_case "$name" "$receipts" "$override" "$exp_status" "$exp_valid" || FAILED=1
done

[[ "$FAILED" -eq 0 ]] && echo "==> PASS: indexed receipts_root validator matches execution-specs" \
  || { echo "==> FAIL"; exit 1; }
