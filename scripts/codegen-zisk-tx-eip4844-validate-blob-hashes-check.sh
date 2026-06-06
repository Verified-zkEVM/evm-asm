#!/usr/bin/env bash
# codegen-zisk-tx-eip4844-validate-blob-hashes-check.sh -- PR-K139.
#
# Decode an EIP-4844 inner RLP and enforce blob-versioned-hash
# structural validity: 1..max_blob_count items, each 32 bytes, each
# with KZG version byte 0x01.
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

echo "==> emit zisk_tx_eip4844_validate_blob_hashes ELF"
lake exe codegen --program zisk_tx_eip4844_validate_blob_hashes --halt linux93 \
  -o gen-out/zisk_tx_eip4844_validate_blob_hashes

REPO_ROOT="$(pwd)"

# run_case <name> <num_blobs> <version_byte> <hash_len> <max_blob_count> <expected_status> <expected_count>
run_case() {
  local name="$1" n="$2" version="$3" hash_len="$4" max_count="$5" expected_status="$6" expected_count="$7"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_eip4844_validate_blob_hashes_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_eip4844_validate_blob_hashes_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
n = int(sys.argv[2])
version = int(sys.argv[3])
hash_len = int(sys.argv[4])
max_count = int(sys.argv[5])
ALICE = bytes([0xaa] * 20)
R = bytes([0x11] * 32)
S = bytes([0x22] * 32)
if hash_len == 0:
    h = b''
else:
    h = bytes([version]) + bytes([0xab] * (hash_len - 1))
inner = [
    1, 7, 10**9, 2*10**9, 21000,
    ALICE, 10**18, b'', [],
    1, [h for _ in range(n)], 0,
    int.from_bytes(R, 'big'), int.from_bytes(S, 'big'),
]
inner_rlp = rlp.encode(inner)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(inner_rlp)))
    f.write(struct.pack('<Q', max_count))
    f.write(inner_rlp)
    pad = (-(16 + len(inner_rlp))) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file" "$n" "$version" "$hash_len" "$max_count"

  "$ZISKEMU" -e gen-out/zisk_tx_eip4844_validate_blob_hashes.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_tx_eip4844_validate_blob_hashes_${name}.emu.log" 2>&1 || true

  local actual_status actual_count exp_status_le exp_count_le
  actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  actual_count="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  exp_status_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"
  exp_count_le="$(python3 -c "print(int('$expected_count').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" && "$actual_count" == "$exp_count_le" ]]; then
    printf "  %-24s OK   status=%s count=%s\n" "$name" "$expected_status" "$expected_count"
    return 0
  else
    printf "  %-24s FAIL status=0x%s count=0x%s (expected status=%s count=%s)\n" \
      "$name" "$actual_status" "$actual_count" "$expected_status" "$expected_count"
    return 1
  fi
}

FAILED=0
run_case "one_blob"       1 1 32 6 0 1 || FAILED=1
run_case "six_blobs"      6 1 32 6 0 6 || FAILED=1
run_case "zero_blobs"     0 1 32 6 3 0 || FAILED=1
run_case "seven_blobs"    7 1 32 6 4 7 || FAILED=1
run_case "bad_version"    1 2 32 6 6 1 || FAILED=1
run_case "short_hash"     1 1 31 6 5 1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_eip4844_validate_blob_hashes enforces EIP-4844 structural blob hash rules"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
