#!/usr/bin/env bash
# codegen-zisk-eip7778-remaining-block-gas-check.sh -- EIP-7778 remaining gas checker.
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

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_eip7778_remaining_block_gas_check ELF"
lake exe codegen --program zisk_eip7778_remaining_block_gas_check --halt linux93 \
  -o gen-out/zisk_eip7778_remaining_block_gas_check

REPO_ROOT="$(pwd)"

# run_case <name> <block_gas_limit> <tx_gases_csv> <used_increments_csv> <status> <index> <used>
run_case() {
  local name="$1" limit="$2" tx_gases="$3" used_increments="$4" exp_status="$5" exp_index="$6" exp_used="$7"
  local in_file="$REPO_ROOT/gen-out/zisk_eip7778_remaining_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_eip7778_remaining_${name}.output"
  local expected_file="$REPO_ROOT/gen-out/zisk_eip7778_remaining_${name}.expected.hex"

  python3 - "$in_file" "$expected_file" "$limit" "$tx_gases" "$used_increments" \
    "$exp_status" "$exp_index" "$exp_used" <<'EOF_PY'
import struct
import sys

(
    in_file,
    expected_file,
    limit_s,
    tx_gases_s,
    used_increments_s,
    exp_status_s,
    exp_index_s,
    exp_used_s,
) = sys.argv[1:]

def parse_csv(s: str) -> list[int]:
    if not s:
        return []
    return [int(x, 0) for x in s.split(",")]

limit = int(limit_s, 0)
tx_gases = parse_csv(tx_gases_s)
used_increments = parse_csv(used_increments_s)
assert len(tx_gases) == len(used_increments)

payload = bytearray()
payload += struct.pack("<Q", limit)
payload += struct.pack("<Q", len(tx_gases))
for gas in tx_gases:
    payload += struct.pack("<Q", gas)
for used in used_increments:
    payload += struct.pack("<Q", used)

with open(in_file, "wb") as f:
    f.write(payload)

out = struct.pack(
    "<QQQ",
    int(exp_status_s, 0),
    int(exp_index_s, 0),
    int(exp_used_s, 0),
)
with open(expected_file, "w") as f:
    f.write(out.hex())
EOF_PY

  "$ZISKEMU" -e gen-out/zisk_eip7778_remaining_block_gas_check.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_eip7778_remaining_${name}.emu.log" 2>&1 || true

  local actual expected
  actual="$(dd if="$out_file" bs=1 count=24 2>/dev/null | xxd -p | tr -d '\n')"
  expected="$(cat "$expected_file")"
  if [[ "$actual" == "$expected" ]]; then
    printf "  %-26s OK   status=%s index=%s used=%s\n" "$name" "$exp_status" "$exp_index" "$exp_used"
    return 0
  fi
  printf "  %-26s FAIL status=%s index=%s used=%s\n" "$name" "$exp_status" "$exp_index" "$exp_used"
  printf "      actual:   %s\n" "$actual"
  printf "      expected: %s\n" "$expected"
  return 1
}

FAILED=0
run_case "empty_block" 100000 "" "" 0 0 0 || FAILED=1
run_case "boundary_second_tx" 100000 "60000,40000" "60000,40000" 0 0 100000 || FAILED=1
run_case "second_exceeds_remaining" 100000 "60000,40001" "60000,0" 1 2 60000 || FAILED=1
run_case "first_exceeds_limit" 100000 "100001" "0" 1 1 0 || FAILED=1
run_case "increment_overflow" 18446744073709551615 "1,0" "18446744073709551615,1" 2 2 18446744073709551615 || FAILED=1

if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: EIP-7778 remaining block-gas checker"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
