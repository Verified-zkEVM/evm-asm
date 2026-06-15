#!/usr/bin/env bash
# Probe the keyed cross-tx committed-storage snapshot upsert helper.
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2; exit 1; fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_mtx_committed_snapshot_upsert ELF"
lake exe codegen --program zisk_mtx_committed_snapshot_upsert --halt linux93 \
  -o gen-out/zisk_mtx_committed_snapshot_upsert

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" mode="$2" expect="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_cssu_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_cssu_${name}.output"

  MODE="$mode" python3 -c "
import os, struct, sys
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', int(os.environ['MODE'])))
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_mtx_committed_snapshot_upsert.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_cssu_${name}.emu.log" 2>&1 || true

  local got
  got=$(python3 -c "
words=[]
d=open('$out_file','rb').read()
for off in range(0,88,8):
    words.append(int.from_bytes(d[off:off+8], 'little'))
print(':'.join(str(x) for x in words))
")
  if [[ "$got" == "$expect" ]]; then
    printf "  %-14s OK   [%s]\n" "$name" "$got"; return 0
  fi
  printf "  %-14s FAIL got=[%s] expected=[%s]\n" "$name" "$got" "$expect"; return 1
}

FAILED=0
# count:status:stored_status:e0_addr:e0_slot:e0_orig:e0_cur:e1_addr:e1_slot:e1_cur:sentinel
run_case "zero"      0 "0:0:0:0:0:0:0:0:0:0:238" || FAILED=1
run_case "insert"    1 "1:0:0:170:7:66:17:0:0:0:238" || FAILED=1
run_case "duplicate" 2 "1:0:0:170:7:66:51:0:0:0:238" || FAILED=1
run_case "mixed"     3 "2:0:0:170:7:66:51:170:9:85:238" || FAILED=1
run_case "overflow"  4 "3:1:1:0:0:0:0:0:0:0:238" || FAILED=1
run_case "highdup"   5 "1:0:0:170:7:66:130:0:0:0:238" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: committed-storage snapshot upsert preserves latest values and reports conservative unique-key overflow"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
