#!/usr/bin/env bash
# codegen-zisk-mpt-indexed-large-leaf-hash-check.sh
#
# Verify the streaming large MPT leaf hash helper used by indexed transaction
# tries. The helper computes keccak(rlp([hp_path, value])) without copying the
# large value into the fixed MPT leaf scratch buffer.
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

echo "==> emit zisk_mpt_indexed_large_leaf_hash ELF"
lake exe codegen --program zisk_mpt_indexed_large_leaf_hash --halt linux93 \
  -o gen-out/zisk_mpt_indexed_large_leaf_hash

read_u64() { od -An -tu8 -j "$2" -N 8 "$1" | tr -d ' \n'; }

FAILED=0
# Reuse the same Python reference body by substituting a literal expression.
for spec in \
  "empty_large 0 0 'ab' * 200000 0" \
  "nibble7_large 1 7 'cd' * 200000 0" \
  "small_rejected 0 0 'ef' * 8 1" \
  "bad_kind 2 0 '12' * 200000 1"; do
  read -r name kind nibble expr_a op expr_b exp_status <<< "$spec"
  value_py="$expr_a $op $expr_b"
  in_file="$REPO_ROOT/gen-out/zisk_mpt_indexed_large_leaf_hash_${name}.input"
  out_file="$REPO_ROOT/gen-out/zisk_mpt_indexed_large_leaf_hash_${name}.output"
  exp_file="$REPO_ROOT/gen-out/zisk_mpt_indexed_large_leaf_hash_${name}.expected"
  uv run --directory execution-specs --quiet python3 - "$in_file" "$exp_file" "$kind" "$nibble" "$value_py" <<'PYCASE2'
import sys, struct
from ethereum.crypto.hash import keccak256
from ethereum_rlp import rlp

value = bytes.fromhex(eval(sys.argv[5]))
kind = int(sys.argv[3])
nibble = int(sys.argv[4])
if kind == 0:
    hp = bytes([0x20])
elif kind == 1:
    hp = bytes([0x30 | nibble])
else:
    hp = b""
expected = keccak256(rlp.encode([hp, value])) if kind in (0, 1) and len(value) >= 56 and 0 <= nibble <= 15 else b"\x00" * 32
with open(sys.argv[1], "wb") as f:
    f.write(struct.pack("<QQQ", kind, nibble, len(value)))
    f.write(value)
    f.write(b"\x00" * ((-len(value)) % 8))
with open(sys.argv[2], "w") as f:
    f.write(expected.hex())
PYCASE2
  if ! "$ZISKEMU" -e gen-out/zisk_mpt_indexed_large_leaf_hash.elf \
        -i "$in_file" -o "$out_file" -n 20000000 >/dev/null 2>&1 </dev/null; then
    printf "  %-24s ERROR ziskemu\n" "$name"
    FAILED=1
    continue
  fi
  st="$(read_u64 "$out_file" 32)"
  actual="$(od -An -tx1 -j 0 -N 32 "$out_file" | tr -d ' \n')"
  expected="$(cat "$exp_file")"
  if [[ "$st" == "$exp_status" && ( "$exp_status" != "0" || "$actual" == "$expected" ) ]]; then
    printf "  %-24s OK   status=%s hash=%s..\n" "$name" "$st" "${actual:0:16}"
  else
    printf "  %-24s FAIL status=%s/%s\n" "$name" "$st" "$exp_status"
    printf "      expected %s\n" "$expected"
    printf "      got      %s\n" "$actual"
    FAILED=1
  fi
done

[[ "$FAILED" -eq 0 ]] && echo "==> PASS: large indexed leaf hash helper matches execution-specs" \
  || { echo "==> FAIL"; exit 1; }
