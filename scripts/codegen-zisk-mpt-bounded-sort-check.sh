#!/usr/bin/env bash
# Verify sd13v's bounded MSD descriptor sorter with the emitted ZisK probe.
# The vector checks a nontrivial lexicographic ordering and rejects an invalid
# nibble even when the input has a single descriptor (the no-partition case),
# and rejects duplicate final keys after normalization.
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

echo "==> lake build codegen"
bash scripts/codegen-force-relink.sh >/dev/null
echo "==> emit zisk_mpt_bounded_sort"
lake exe codegen --program zisk_mpt_bounded_sort --halt linux93 -o "$workdir/sort" >/dev/null

python3 - "$workdir" <<'PY'
import pathlib
import struct
import sys

out = pathlib.Path(sys.argv[1])
keys = [[9] + [0] * 63, [1, 0, 5] + [7] * 61, [0] + [15] * 63]
(out / "good.input").write_bytes(struct.pack("<Q", len(keys)) + bytes(sum(keys, [])))
(out / "bad.input").write_bytes(struct.pack("<Q", 1) + bytes([16]) + b"\0" * 63)
(out / "duplicate.input").write_bytes(struct.pack("<Q", 2) + bytes(keys[0] + keys[0]))
PY

"$ZISKEMU" -e "$workdir/sort.elf" -i "$workdir/good.input" -o "$workdir/good.output" -n 1000000 >/dev/null </dev/null
"$ZISKEMU" -e "$workdir/sort.elf" -i "$workdir/bad.input" -o "$workdir/bad.output" -n 1000000 >/dev/null </dev/null
"$ZISKEMU" -e "$workdir/sort.elf" -i "$workdir/duplicate.input" -o "$workdir/duplicate.output" -n 1000000 >/dev/null </dev/null

python3 - "$workdir" <<'PY'
import pathlib
import struct
import sys

root = pathlib.Path(sys.argv[1])
good = (root / "good.output").read_bytes()
status, count = struct.unpack_from("<QQ", good)
paths = [list(good[16 + 64 * i : 16 + 64 * (i + 1)]) for i in range(count)]
assert (status, count) == (0, 3), (status, count)
assert paths == sorted(paths), paths
bad = (root / "bad.output").read_bytes()
assert struct.unpack_from("<QQ", bad) == (1, 1)
duplicate = (root / "duplicate.output").read_bytes()
assert struct.unpack_from("<QQ", duplicate) == (2, 2)
print("PASS: bounded MSD sort orders paths and rejects malformed or duplicate final keys")
PY
