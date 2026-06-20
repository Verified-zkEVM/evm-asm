#!/usr/bin/env bash
# codegen-zisk-block-log-window-snapshot-overflow-check.sh -- block log-window snapshot capacity probe.
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

echo "==> emit zisk_block_log_window_snapshot_overflow ELF"
lake exe codegen --program zisk_block_log_window_snapshot_overflow --halt linux93 \
  -o gen-out/zisk_block_log_window_snapshot_overflow

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" mode="$2"
  local in_file="$REPO_ROOT/gen-out/zisk_block_log_window_snapshot_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_log_window_snapshot_${name}.output"
  local expected_file="$REPO_ROOT/gen-out/zisk_block_log_window_snapshot_${name}.expected.hex"

  python3 - "$in_file" "$expected_file" "$mode" <<'EOF_PY'
import struct
import sys

in_file, expected_file, mode = sys.argv[1:]
mode_num = int(mode)
payload = bytearray(8)
payload[0:8] = struct.pack('<Q', mode_num)
with open(in_file, 'wb') as f:
    f.write(payload)

if mode_num == 1:
    # return, count, data_used, overflow, last_start, last_count
    # count/last_start == bvBlockLogDescCapacity (gas/375 = 533333 since #9043;
    # the probe pre-seeds bv_block_log_count to the capacity to force the count guard).
    words = (1, 533333, 0, 1, 533333, 0)
elif mode_num == 2:
    words = (1, 1, 0, 1, 0, 0)
else:
    raise ValueError(mode)
with open(expected_file, 'w') as f:
    f.write(struct.pack('<' + 'Q' * len(words), *words).hex())
EOF_PY

  "$ZISKEMU" -e gen-out/zisk_block_log_window_snapshot_overflow.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_block_log_window_snapshot_${name}.emu.log" 2>&1 || true

  local actual expected
  actual="$(dd if="$out_file" bs=1 count=48 2>/dev/null | xxd -p | tr -d '\n')"
  expected="$(cat "$expected_file")"
  if [[ "$actual" == "$expected" ]]; then
    printf "  %-18s OK\n" "$name"
    return 0
  fi
  printf "  %-18s FAIL\n" "$name"
  printf "      actual:   %s\n" "$actual"
  printf "      expected: %s\n" "$expected"
  printf "      emulator log: %s\n" "$REPO_ROOT/gen-out/zisk_block_log_window_snapshot_${name}.emu.log"
  return 1
}

FAILED=0
run_case "desc_overflow" 1 || FAILED=1
run_case "data_overflow" 2 || FAILED=1

if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block log-window snapshot capacity probe"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
