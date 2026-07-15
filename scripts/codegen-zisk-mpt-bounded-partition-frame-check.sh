#!/usr/bin/env bash
# Verify frame-local radix ranges derived from sorted final descriptor keys.
set -euo pipefail
cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

workdir="$(mktemp -d)"
trap 'rm -rf "$workdir"' EXIT
bash scripts/codegen-force-relink.sh >/dev/null
lake exe codegen --program zisk_mpt_bounded_partition_frame --halt linux93 -o "$workdir/partition" >/dev/null

python3 - "$workdir/input" <<'PY'
import pathlib
import struct
import sys

keys = [[9] + [0] * 63, [1, 0, 5] + [7] * 61, [0] + [15] * 63]
pathlib.Path(sys.argv[1]).write_bytes(struct.pack('<Q', len(keys)) + bytes(sum(keys, [])))
PY

"$ZISKEMU" -e "$workdir/partition.elf" -i "$workdir/input" -o "$workdir/output" -n 1000000 >/dev/null </dev/null

python3 - "$workdir/output" <<'PY'
import pathlib
import struct
import sys

out = pathlib.Path(sys.argv[1]).read_bytes()
assert struct.unpack_from('<Q', out)[0] == 0
ranges = [struct.unpack_from('<QQ', out, 8 + 16*i) for i in range(10)]
assert ranges == [(0, 1), (1, 2)] + [(2, 2)] * 7 + [(2, 3)], ranges
print('PASS: bounded frame partitions sorted descriptors into exact child ranges')
PY
