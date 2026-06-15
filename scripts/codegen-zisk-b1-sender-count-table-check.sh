#!/usr/bin/env bash
# codegen-zisk-b1-sender-count-table-check.sh
#
# Unit-check b1_sender_count_table: sort six A1 skip-list sender lanes
# deterministically and emit one count per distinct sender. This is the
# non-quadratic substrate for the multi-tx B1 final-nonce check.
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

mkdir -p gen-out
echo "==> lake build codegen"
lake build codegen >/dev/null
echo "==> emit zisk_b1_sender_count_table ELF"
lake exe codegen --program zisk_b1_sender_count_table --halt linux93 \
  -o gen-out/zisk_b1_sender_count_table

python3 - <<'PY'
import struct
with open('gen-out/zisk_b1_sender_count_table_mode0.input', 'wb') as f:
    f.write(struct.pack('<Q', 0))
with open('gen-out/zisk_b1_sender_count_table_mode1.input', 'wb') as f:
    f.write(struct.pack('<Q', 1))
PY

run_mode() {
  local mode="$1"
  "$ZISKEMU" -e gen-out/zisk_b1_sender_count_table.elf \
    -i "gen-out/zisk_b1_sender_count_table_mode${mode}.input" \
    -o "gen-out/zisk_b1_sender_count_table_mode${mode}.output" -n 2000000 \
    >"gen-out/zisk_b1_sender_count_table_mode${mode}.emu.log" 2>&1 || true
}

run_mode 0
run_mode 1

python3 - <<'PY'
import struct, sys

d = open('gen-out/zisk_b1_sender_count_table_mode0.output', 'rb').read()

def u64(o):
    return struct.unpack('<Q', d[o:o + 8])[0] if o + 8 <= len(d) else None

expected = [
    (bytes([0x11]) * 20 + bytes(12), 3),
    (bytes([0x22]) * 20 + bytes(12), 2),
    (bytes([0x33]) * 20 + bytes(12), 1),
]

failed = False
checks = [
    ('status', u64(0), 0),
    ('distinct count', u64(8), 3),
]
for label, got, exp in checks:
    ok = got == exp
    failed = failed or not ok
    print(f"  {'OK  ' if ok else 'FAIL'} {label:18s} got={got!r} exp={exp!r}")

for i, (addr, count) in enumerate(expected):
    off = 16 + i * 40
    got_addr = d[off:off + 32]
    got_count = u64(off + 32)
    ok_addr = got_addr == addr
    ok_count = got_count == count
    failed = failed or not ok_addr or not ok_count
    print(f"  {'OK  ' if ok_addr else 'FAIL'} entry[{i}].addr      got={got_addr.hex()} exp={addr.hex()}")
    print(f"  {'OK  ' if ok_count else 'FAIL'} entry[{i}].count     got={got_count!r} exp={count!r}")

d17 = open('gen-out/zisk_b1_sender_count_table_mode1.output', 'rb').read()
status17 = struct.unpack('<Q', d17[0:8])[0]
count17 = struct.unpack('<Q', d17[8:16])[0]
ok17 = status17 == 0 and count17 == 17
failed = failed or not ok17
print(f"  {'OK  ' if status17 == 0 else 'FAIL'} distinct17.status got={status17!r} exp=0")
print(f"  {'OK  ' if count17 == 17 else 'FAIL'} distinct17.count  got={count17!r} exp=17")

sys.exit(1 if failed else 0)
PY

echo
echo "==> PASS: b1_sender_count_table emits sorted distinct sender counts"
