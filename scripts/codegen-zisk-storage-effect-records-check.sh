#!/usr/bin/env bash
# codegen-zisk-storage-effect-records-check.sh -- committed storage-effect
# record arena probe.
set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

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
lake build codegen >/dev/null

echo "==> emit zisk_storage_effect_records_probe ELF"
lake exe codegen --program zisk_storage_effect_records_probe --halt linux93 \
  -o gen-out/zisk_storage_effect_records_probe >/dev/null

run_case() {
  local name="$1" cap="$2" attempts="$3" mode="${4:-0}"
  local in_file="$REPO_ROOT/gen-out/zisk_storage_effect_records_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_storage_effect_records_${name}.output"
  local expected_file="$REPO_ROOT/gen-out/zisk_storage_effect_records_${name}.expected.hex"

  python3 - "$in_file" "$expected_file" "$cap" "$attempts" "$mode" <<'EOF_PY'
import struct
import sys

in_file, expected_file, cap_s, attempts_s, mode_s = sys.argv[1:]
cap = int(cap_s, 0)
attempts = int(attempts_s, 0)
mode = int(mode_s, 0)
with open(in_file, "wb") as f:
    f.write(struct.pack("<Q", cap))
    f.write(struct.pack("<Q", attempts))
    f.write(struct.pack("<Q", mode))

records = []
last_status = 0
for i in range(attempts):
    if len(records) >= cap:
        last_status = 1
        continue
    records.append((1, 2 * i, i + 1, 0))
    last_status = 0

runtime_cases = {
    1: (1, 0, 1, 0),
    2: (1, 2, 3, 0),
    3: (0, 4, 0, 0),
}
if mode:
    if len(records) >= cap:
        last_status = 1
    else:
        records.append(runtime_cases[mode])
        last_status = 0

out = bytearray(104)
out[0:8] = struct.pack("<Q", last_status)
out[8:16] = struct.pack("<Q", len(records))
out[16:24] = struct.pack("<Q", cap)
out[24:32] = struct.pack("<Q", 0 if records else 1)
if records:
    out[32:64] = struct.pack("<QQQQ", *records[0])
out[64:72] = struct.pack("<Q", 0 if records else 1)
if records:
    out[72:104] = struct.pack("<QQQQ", *records[-1])
with open(expected_file, "w") as f:
    f.write(out.hex())
EOF_PY

  "$ZISKEMU" -e gen-out/zisk_storage_effect_records_probe.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_storage_effect_records_${name}.emu.log" 2>&1 || true

  local actual expected
  actual="$(dd if="$out_file" bs=1 count=104 2>/dev/null | xxd -p | tr -d '\n')"
  expected="$(cat "$expected_file")"
  if [[ "$actual" == "$expected" ]]; then
    printf "  %-24s OK   cap=%s attempts=%s mode=%s\n" "$name" "$cap" "$attempts" "$mode"
    return 0
  fi
  printf "  %-24s FAIL cap=%s attempts=%s mode=%s\n" "$name" "$cap" "$attempts" "$mode"
  printf "      actual:   %s\n" "$actual"
  printf "      expected: %s\n" "$expected"
  return 1
}

FAILED=0
run_case "zero_records" 4 0 || FAILED=1
run_case "one_success" 4 1 || FAILED=1
run_case "cap_overflow" 2 3 || FAILED=1
run_case "runtime_success0" 4 0 1 || FAILED=1
run_case "runtime_success2" 4 0 2 || FAILED=1
run_case "runtime_revert" 4 0 3 || FAILED=1

if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: storage-effect record arena ABI probe"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
