#!/usr/bin/env bash
# codegen-zisk-capture-system-storage-exec-rows-check.sh -- bead bmvmx.5.5.1.2.1.3.1.1.
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
lake build codegen

echo "==> emit zisk_capture_system_storage_exec_rows ELF"
lake exe codegen --program zisk_capture_system_storage_exec_rows --halt linux93   -o gen-out/zisk_capture_system_storage_exec_rows

out_file="gen-out/zisk_capture_system_storage_exec_rows.output"
"$ZISKEMU" -e gen-out/zisk_capture_system_storage_exec_rows.elf   -o "$out_file" -n 10000000 >gen-out/zisk_capture_system_storage_exec_rows.emu.log 2>&1 || true

python3 - <<'PY2'
from pathlib import Path
out = Path('gen-out/zisk_capture_system_storage_exec_rows.output').read_bytes()
vals = [int.from_bytes(out[i:i+8], 'little') for i in range(0, 144, 8)]
cap = vals[17]
want = [
    0, 2, 0, 0, 0x2222, 0x333f,
    1,
    0, cap, 0x2222,
    2, 1, 2, cap, 1, cap + 1, 2, cap,
]
if vals != want:
    raise SystemExit(f"FAIL: got={vals} want={want}")
print(
    f"  status={vals[0]} count={vals[1]} tx0={vals[2]} tx1={vals[3]} "
    f"row0=0x{vals[4]:x} row1_last=0x{vals[5]:x} "
    f"malformed={vals[6]} exact_cap={vals[7]} exact_count={vals[8]} "
    f"exact_row=0x{vals[9]:x} overflow={vals[10]} "
    f"last_range=[{vals[11]},{vals[12]}) old={vals[13]} rows={vals[14]} "
    f"new={vals[15]} last_status={vals[16]} cap={vals[17]}"
)
PY2

echo "==> PASS: capture_system_storage_exec_rows side arena copy"
