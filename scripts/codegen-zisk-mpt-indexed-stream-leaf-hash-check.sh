#!/usr/bin/env bash
# Verify the general shallow indexed-leaf streaming hash against execution-specs.
set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
mkdir -p gen-out

lake build codegen >/dev/null
lake exe codegen --program zisk_mpt_indexed_stream_leaf_hash --halt linux93 \
  -o gen-out/zisk_mpt_indexed_stream_leaf_hash >/dev/null

read_u64() { od -An -tu8 -j "$2" -N 8 "$1" | tr -d ' \n'; }
run_case() {
  local name="$1" path_py="$2" value_py="$3" expected_status="$4"
  local in="$REPO_ROOT/gen-out/zisk_mpt_indexed_stream_leaf_hash_${name}.input"
  local out="$REPO_ROOT/gen-out/zisk_mpt_indexed_stream_leaf_hash_${name}.output"
  local expected="$REPO_ROOT/gen-out/zisk_mpt_indexed_stream_leaf_hash_${name}.expected"
  uv run --directory execution-specs --quiet python3 - "$in" "$expected" "$path_py" "$value_py" "$expected_status" <<'PY'
import struct, sys
from ethereum.crypto.hash import keccak256
from ethereum_rlp import rlp

path = bytes(eval(sys.argv[3]))
value = bytes.fromhex(eval(sys.argv[4]))
status = int(sys.argv[5])
assert len(path) <= 7
if len(path) % 2:
    hp = bytes([0x30 | path[0]]) + bytes((path[i] << 4) | path[i + 1] for i in range(1, len(path), 2))
else:
    hp = bytes([0x20]) + bytes((path[i] << 4) | path[i + 1] for i in range(0, len(path), 2))
with open(sys.argv[1], "wb") as f:
    f.write(struct.pack("<QQ", len(path), len(value)))
    f.write(path + b"\0" * (8 - len(path)))
    f.write(value)
    f.write(b"\0" * (-len(value) % 8))
with open(sys.argv[2], "w") as f:
    f.write((keccak256(rlp.encode([hp, value])) if status == 0 else b"\0" * 32).hex())
PY
  "$ZISKEMU" -e gen-out/zisk_mpt_indexed_stream_leaf_hash.elf -i "$in" -o "$out" -n 20000000 >/dev/null </dev/null
  local status actual
  status="$(read_u64 "$out" 32)"
  actual="$(od -An -tx1 -j 0 -N 32 "$out" | tr -d ' \n')"
  [[ "$status" == "$expected_status" ]] && { [[ "$status" != 0 ]] || [[ "$actual" == "$(cat "$expected")" ]]; } || {
    echo "FAIL $name: status=$status expected=$expected_status hash=$actual expected=$(cat "$expected")" >&2; return 1;
  }
  echo "OK $name"
}

run_case key0_large '[8, 0]' "'ab' * 32768" 0
run_case two_byte_key_large '[8, 1, 8, 0]' "'cd' * 32768" 0
run_case max_depth_large '[8, 2, 0, 2, 5, 2]' "'ef' * 32768" 0
run_case short_value_rejected '[8, 0]' "'01' * 26" 1
run_case over_depth_rejected '[8, 0, 0, 0, 0, 0, 0]' "'01' * 27" 1
echo 'PASS: shallow indexed streaming leaf hashes match execution-specs'
