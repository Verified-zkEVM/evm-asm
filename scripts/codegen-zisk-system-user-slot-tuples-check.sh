#!/usr/bin/env bash
# codegen-zisk-system-user-slot-tuples-check.sh -- bead bmvmx.5.5.1.2.1.3.1.2.
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

program="zisk_system_user_exec_log_slot_tuples"
echo "==> emit $program ELF"
lake exe codegen --program "$program" --halt linux93 -o "gen-out/$program"

out_file="gen-out/${program}.output"
"$ZISKEMU" -e "gen-out/${program}.elf" -o "$out_file" -n 10000000 >"gen-out/${program}.emu.log" 2>&1 || true

python3 - <<'PY2'
from pathlib import Path
out = Path("gen-out/zisk_system_user_exec_log_slot_tuples.output").read_bytes()
vals = [int.from_bytes(out[i:i+8], "little") for i in range(0, 56, 8)]
want = [1, 0, 1, 2, 0, 1, 1]
if vals != want:
    raise SystemExit(f"FAIL: got={vals} want={want}")
print(
    "  sys_count=%d sys_ok=%d sys_bad=%d mix_count=%d mix_ok=%d mix_bad_sys=%d mix_bad_user=%d"
    % tuple(vals)
)
PY2

echo "==> PASS: system+user slot tuple merge probe"
