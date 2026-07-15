#!/usr/bin/env bash
# Check RLP-index lexicographic ordering before the bounded indexed builder.
set -euo pipefail
cd "$(dirname "$0")/.."
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
mkdir -p gen-out
lake build codegen >/dev/null
lake exe codegen --program zisk_mpt_indexed_sort_changes --halt linux93 -o gen-out/zisk_mpt_indexed_sort_changes >/dev/null

python3 - <<'PY'
import struct
# Numeric input order 0,127,128,256.  RLP lexical order is 127,0,128,256:
# 0x7f < 0x80 < 0x81,0x80 < 0x82,0x01,0x00.
paths = [bytes([8, 0]), bytes([7, 15]), bytes([8, 1, 8, 0]), bytes([8, 2, 0, 1, 0, 0])]
with open('gen-out/zisk_mpt_indexed_sort_changes.input', 'wb') as f:
    f.write(struct.pack('<Q', len(paths)))
    for p in paths:
        f.write(struct.pack('<Q', len(p)))
        f.write(p + b'\0' * (8 - len(p)))
PY
"$ZISKEMU" -e gen-out/zisk_mpt_indexed_sort_changes.elf \
  -i gen-out/zisk_mpt_indexed_sort_changes.input \
  -o gen-out/zisk_mpt_indexed_sort_changes.output -n 3000000 >/dev/null </dev/null
python3 - <<'PY'
import struct
out = open('gen-out/zisk_mpt_indexed_sort_changes.output', 'rb').read()
status = struct.unpack_from('<Q', out, 0)[0]
order = list(struct.unpack_from('<4Q', out, 8))
assert status == 0, status
assert order == [1, 0, 2, 3], order
print('PASS: RLP index order 127,0,128,256 is lexicographic, not numeric')
PY
