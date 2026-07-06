#!/usr/bin/env bash
# codegen-zisk-block-validate-withdrawals-root-indexed-check.sh
#
# Verify block_validate_withdrawals_root_indexed against execution-specs'
# Merkle Patricia Trie root implementation for indexed withdrawals.
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

echo "==> emit zisk_block_validate_withdrawals_root_indexed ELF"
lake exe codegen --program zisk_block_validate_withdrawals_root_indexed --halt linux93 \
  -o gen-out/zisk_block_validate_withdrawals_root_indexed

read_u64() { od -An -tu8 -j "$2" -N 8 "$1" | tr -d ' \n'; }

run_case() {
  local name="$1"
  local n_withdrawals="$2"
  local header_mode="$3"
  local exp_status="$4"
  local exp_valid="$5"
  local in_file="$REPO_ROOT/gen-out/zisk_block_validate_withdrawals_root_indexed_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_validate_withdrawals_root_indexed_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_block_validate_withdrawals_root_indexed_${name}.expected"

  uv run --directory execution-specs --quiet python3 - "$in_file" "$exp_file" "$n_withdrawals" "$header_mode" <<'PY'
import sys, struct
from ethereum.merkle_patricia_trie import Trie, trie_set, root
from ethereum_rlp import rlp
from ethereum_types.bytes import Bytes, Bytes20
from ethereum_types.numeric import Uint

out_path, exp_path, n_s, header_mode = sys.argv[1:5]
n = int(n_s)

def withdrawal(i: int) -> bytes:
    addr = Bytes20(bytes([(0x20 + i) % 256]) * 20)
    return bytes(rlp.encode((Uint(i), Uint(1000 + i), addr, Uint(1_000_000 + i))))

values = [withdrawal(i) for i in range(n)]
trie = Trie(secured=False, default=None)
for i, value in enumerate(values):
    trie_set(trie, Bytes(rlp.encode(Uint(i))), Bytes(value))
expected_root = bytes(root(trie))

if header_mode == "match":
    claimed_root = expected_root
    fields = [Bytes(b"") for _ in range(17)]
    fields[16] = Bytes(claimed_root)
    header = bytes(rlp.encode(fields))
elif header_mode == "mismatch":
    claimed_root = bytes([expected_root[0] ^ 0x01]) + expected_root[1:]
    fields = [Bytes(b"") for _ in range(17)]
    fields[16] = Bytes(claimed_root)
    header = bytes(rlp.encode(fields))
elif header_mode == "short":
    fields = [Bytes(b"") for _ in range(17)]
    fields[16] = Bytes(b"\x12" * 31)
    header = bytes(rlp.encode(fields))
elif header_mode == "missing":
    fields = [Bytes(b"") for _ in range(16)]
    header = bytes(rlp.encode(fields))
elif header_mode == "garbage":
    header = b"\xff\xff\xff"
else:
    raise ValueError(f"unknown header_mode: {header_mode}")

with open(out_path, "wb") as f:
    f.write(struct.pack("<Q", len(header)))
    f.write(struct.pack("<Q", len(values)))
    for value in values:
        f.write(struct.pack("<Q", len(value)))
    f.write(header)
    f.write(b"\x00" * ((-len(header)) % 8))
    for value in values:
        f.write(value)
        f.write(b"\x00" * ((-len(value)) % 8))
with open(exp_path, "w") as f:
    f.write(expected_root.hex())
PY

  if ! "$ZISKEMU" -e gen-out/zisk_block_validate_withdrawals_root_indexed.elf \
        -i "$in_file" -o "$out_file" -n 40000000 >/dev/null 2>&1 </dev/null; then
    printf "  %-20s ERROR ziskemu\n" "$name"
    return 1
  fi

  local st valid expected
  st="$(read_u64 "$out_file" 0)"
  valid="$(read_u64 "$out_file" 8)"
  expected="$(cat "$exp_file")"
  if [[ "$st" == "$exp_status" && "$valid" == "$exp_valid" ]]; then
    printf "  %-20s OK   status=%s valid=%s root=%s..\n" "$name" "$st" "$valid" "${expected:0:16}"
    return 0
  fi

  printf "  %-20s FAIL status=%s/%s valid=%s/%s\n" "$name" "$st" "$exp_status" "$valid" "$exp_valid"
  return 1
}

FAILED=0
run_case "empty_match" 0 match 0 1 || FAILED=1
run_case "one_match" 1 match 0 1 || FAILED=1
run_case "three_match" 3 match 0 1 || FAILED=1
run_case "mismatch" 3 mismatch 0 0 || FAILED=1
run_case "short_root" 2 short 2 0 || FAILED=1
run_case "missing_field" 2 missing 1 0 || FAILED=1
run_case "garbage_header" 2 garbage 1 0 || FAILED=1
run_case "too_many" 129 match 3 0 || FAILED=1

[[ "$FAILED" -eq 0 ]] && echo "==> PASS: indexed withdrawals_root validator matches execution-specs" \
  || { echo "==> FAIL"; exit 1; }
