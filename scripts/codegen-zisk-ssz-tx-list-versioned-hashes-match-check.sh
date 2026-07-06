#!/usr/bin/env bash
# codegen-zisk-ssz-tx-list-versioned-hashes-match-check.sh -- PR-K140.
#
# Check execution-specs is_valid_versioned_hashes parity at the tx-list helper
# level: SSZ new_payload_request.versioned_hashes must equal the concatenated
# EIP-4844 tx blob_versioned_hashes, and non-blob payloads require an empty SSZ
# versioned_hashes list.
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

echo "==> emit zisk_ssz_tx_list_versioned_hashes_match ELF"
lake exe codegen --program zisk_ssz_tx_list_versioned_hashes_match --halt linux93 \
  -o gen-out/zisk_ssz_tx_list_versioned_hashes_match

REPO_ROOT="$(pwd)"

# run_case <name> <mode> <expected_status>
run_case() {
  local name="$1" mode="$2" expected_status="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_ssz_tx_list_versioned_hashes_match_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_ssz_tx_list_versioned_hashes_match_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
mode = sys.argv[2]

def tx_list(*txs):
    table_len = 4 * len(txs)
    offsets = []
    cursor = table_len
    for tx in txs:
        offsets.append(cursor)
        cursor += len(tx)
    return b''.join(struct.pack('<I', off) for off in offsets) + b''.join(txs)

blob_hash = bytes([1]) + bytes(range(1, 32))
other_hash = bytes([1]) + bytes([0xee] * 31)
to = bytes([0xaa] * 20)
r = bytes([0x11] * 32)
s = bytes([0x22] * 32)
inner = [
    1, 7, 10**9, 2 * 10**9, 21000,
    to, 0, b'', [],
    1, [blob_hash], 0,
    int.from_bytes(r, 'big'), int.from_bytes(s, 'big'),
]
blob_tx = bytes([3]) + rlp.encode(inner)

if mode == 'match':
    txs = tx_list(blob_tx)
    hashes = blob_hash
elif mode == 'mismatch':
    txs = tx_list(blob_tx)
    hashes = other_hash
elif mode == 'extra_without_txs':
    txs = b''
    hashes = blob_hash
else:
    raise SystemExit(f'unknown mode {mode}')

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(txs)))
    f.write(struct.pack('<Q', len(hashes)))
    f.write(txs)
    f.write(hashes)
    pad = (-(16 + len(txs) + len(hashes))) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file" "$mode"

  "$ZISKEMU" -e gen-out/zisk_ssz_tx_list_versioned_hashes_match.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_ssz_tx_list_versioned_hashes_match_${name}.emu.log" 2>&1 || true

  local actual_status exp_status_le
  actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  exp_status_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" ]]; then
    printf "  %-20s OK   status=%s\n" "$name" "$expected_status"
    return 0
  else
    printf "  %-20s FAIL status=0x%s (expected status=%s)\n" \
      "$name" "$actual_status" "$expected_status"
    return 1
  fi
}

FAILED=0
run_case "matching_blob" "match" 0 || FAILED=1
run_case "mismatched_blob" "mismatch" 4 || FAILED=1
run_case "extra_no_txs" "extra_without_txs" 4 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: ssz_tx_list_versioned_hashes_match mirrors is_valid_versioned_hashes cases"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
