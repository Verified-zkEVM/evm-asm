#!/usr/bin/env bash
# Focused matrix for the concatenate-only .12 sequential shape predicate.
set -euo pipefail

cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
if [[ -z "$ZISKEMU" ]]; then
  echo "ziskemu not found -- set ZISKEMU=..." >&2
  exit 1
fi

mkdir -p gen-out
echo "==> lake build codegen"
lake build codegen
echo "==> emit zisk_multi_tx_sequential_supported_shape ELF"
lake exe codegen --program zisk_multi_tx_sequential_supported_shape --halt linux93 \
  -o gen-out/zisk_multi_tx_sequential_supported_shape

python3 - gen-out/zisk_multi_tx_sequential_supported_shape.input <<'PY'
import struct, sys

cases = [
    ("legacy_eoa", 0, 0, 0, 0),
    ("access_list_contract", 0, 0, 1, 1),
    ("dynamic_eoa", 0, 0, 2, 0),
    ("dynamic_contract", 0, 0, 2, 1),
    ("malformed_status", 3, 0, 0, 0),
    ("creation", 0, 1, 0, 0),
    ("blob_deferred", 0, 0, 3, 1),
    ("set_code_deferred", 0, 0, 4, 0),
    ("unsupported_recipient", 0, 0, 0, 2),
    ("extract_failure", 20, 0, 2, 1),
    ("unknown_type", 0, 0, 99, 0),
]
with open(sys.argv[1], "wb") as f:
    f.write(struct.pack("<Q", len(cases)))
    for _, status, creation, tx_type, recipient_shape in cases:
        row = bytearray(200)
        for off, value in ((0, status), (48, creation), (160, tx_type), (192, recipient_shape)):
            row[off:off + 8] = struct.pack("<Q", value)
        f.write(row)
with open("gen-out/zisk_multi_tx_sequential_supported_shape.expected", "w") as f:
    f.write("\n".join("0" if i < 4 else "1" for i in range(len(cases))) + "\n")
PY

"$ZISKEMU" -e gen-out/zisk_multi_tx_sequential_supported_shape.elf \
  -i gen-out/zisk_multi_tx_sequential_supported_shape.input \
  -o gen-out/zisk_multi_tx_sequential_supported_shape.output -n 500000 \
  >gen-out/zisk_multi_tx_sequential_supported_shape.emu.log 2>&1 || true

python3 - gen-out/zisk_multi_tx_sequential_supported_shape.output \
  gen-out/zisk_multi_tx_sequential_supported_shape.expected <<'PY'
import sys
actual = list(open(sys.argv[1], "rb").read()[:11])
expected = [int(line) for line in open(sys.argv[2]) if line.strip()]
print(f"  cases={len(expected)} actual={actual} expected={expected}")
if actual != expected:
    raise SystemExit(1)
print("==> PASS: sequential supported-shape predicate matrix")
PY
