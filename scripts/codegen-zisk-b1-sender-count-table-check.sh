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
for mode in range(13):
    with open(f'gen-out/zisk_b1_sender_count_table_mode{mode}.input', 'wb') as f:
        f.write(struct.pack('<Q', mode))
PY

run_mode() {
  local mode="$1"
  local steps=5000000
  case "$mode" in
    2|3|10|11) steps=50000000 ;;
    4|12) steps=300000000 ;;
    5) steps=2000000 ;;
  esac
  "$ZISKEMU" -e gen-out/zisk_b1_sender_count_table.elf \
    -i "gen-out/zisk_b1_sender_count_table_mode${mode}.input" \
    -o "gen-out/zisk_b1_sender_count_table_mode${mode}.output" -n "$steps" \
    >"gen-out/zisk_b1_sender_count_table_mode${mode}.emu.log" 2>&1 || true
}

for mode in 0 1 2 3 4 5 6 7 8 9 10 11 12; do
  run_mode "$mode"
done

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
    ('find last status', u64(136), 0),
    ('find last count', u64(144), 1),
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

boundary_cases = [
    (1, 'distinct17', 0, 17, 0, 1),
    (2, 'distinct1024', 0, 1024, 0, 1),
    (3, 'distinct1025', 0, 1025, 0, 1),
    (4, 'distinct9523', 0, 9523, 0, 1),
    (5, 'overcap9524', 1, None, 9, 0),
]

for mode, label, exp_status, exp_count, exp_find_status, exp_find_count in boundary_cases:
    dm = open(f'gen-out/zisk_b1_sender_count_table_mode{mode}.output', 'rb').read()
    status = struct.unpack('<Q', dm[0:8])[0] if len(dm) >= 8 else None
    count = struct.unpack('<Q', dm[8:16])[0] if len(dm) >= 16 else None
    find_status = struct.unpack('<Q', dm[136:144])[0] if len(dm) >= 144 else None
    find_count = struct.unpack('<Q', dm[144:152])[0] if len(dm) >= 152 else None
    ok_status = status == exp_status
    ok_count = exp_count is None or count == exp_count
    ok_find_status = find_status == exp_find_status
    ok_find_count = find_count == exp_find_count
    failed = failed or not ok_status or not ok_count or not ok_find_status or not ok_find_count
    print(f"  {'OK  ' if ok_status else 'FAIL'} {label}.status got={status!r} exp={exp_status!r}")
    if exp_count is not None:
        print(f"  {'OK  ' if ok_count else 'FAIL'} {label}.count  got={count!r} exp={exp_count!r}")
    print(f"  {'OK  ' if ok_find_status else 'FAIL'} {label}.find_status got={find_status!r} exp={exp_find_status!r}")
    print(f"  {'OK  ' if ok_find_count else 'FAIL'} {label}.find_count  got={find_count!r} exp={exp_find_count!r}")

sequence_cases = [
    (6, 'seq_repeated_valid', 0, 6),
    (7, 'seq_reuse_reject', 40, 2),
    (8, 'seq_too_high_reject', 40, 2),
    (9, 'seq_distinct17', 0, 17),
    (10, 'seq_distinct1024', 0, 1024),
    (11, 'seq_distinct1025', 0, 1025),
    (12, 'seq_distinct9523', 0, 9523),
]

for mode, label, exp_status, exp_processed in sequence_cases:
    dm = open(f'gen-out/zisk_b1_sender_count_table_mode{mode}.output', 'rb').read()
    seq_status = struct.unpack('<Q', dm[152:160])[0] if len(dm) >= 160 else None
    processed = struct.unpack('<Q', dm[160:168])[0] if len(dm) >= 168 else None
    ok_status = seq_status == exp_status
    ok_processed = processed == exp_processed
    failed = failed or not ok_status or not ok_processed
    print(f"  {'OK  ' if ok_status else 'FAIL'} {label}.seq_status got={seq_status!r} exp={exp_status!r}")
    print(f"  {'OK  ' if ok_processed else 'FAIL'} {label}.processed  got={processed!r} exp={exp_processed!r}")

sys.exit(1 if failed else 0)
PY

echo
echo "==> PASS: b1_sender_count_table emits sorted distinct sender counts"
