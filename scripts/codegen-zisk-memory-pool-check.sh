#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
if [[ -z "$ZISKEMU" && -x "$HOME/.zisk/bin/ziskemu" ]]; then
  ZISKEMU="$HOME/.zisk/bin/ziskemu"
fi
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }

mkdir -p gen-out
lake exe codegen --program zisk_call_descend --halt linux93 -o gen-out/zisk_call_descend >/dev/null
: > gen-out/zisk_call_descend.input
"$ZISKEMU" -e gen-out/zisk_call_descend.elf -i gen-out/zisk_call_descend.input \
  -o gen-out/zisk_call_descend.output -n 100000000 >gen-out/zisk_call_descend.emu.log 2>&1

python3 - <<'PY'
import struct
data = open("gen-out/zisk_call_descend.output", "rb").read(64)
got = struct.unpack("<8Q", data)
expected = (
    0x30020,              # child base = parent base + ceil32(parent MSIZE)
    0x1122334455667788,   # parent >128 KiB write survives child
    0x8877665544332211,   # child >128 KiB write reads back
    0,                    # reused sibling slice is zero-on-expansion
    0xaabbccddeeff0011,   # sibling write reads back
    0x1122334455667788,   # sibling did not alias parent
    0,                    # sibling and returned child reuse the same LIFO base
    0,                    # no OOG marker
)
for i, (actual, want) in enumerate(zip(got, expected)):
    print(f"  {'OK  ' if actual == want else 'FAIL'} word[{i}] got={actual:#x} expected={want:#x}")
if got != expected:
    raise SystemExit(1)
PY

echo "PASS: shared pool supports >128 KiB nested memory and isolates parent/child/sibling frames"
