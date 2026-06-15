#!/usr/bin/env bash
# Probe bounded lookup of the chunked cross-tx committed-storage table.
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

echo "==> emit zisk_mtx_committed_chunked_latest_value ELF"
lake exe codegen --program zisk_mtx_committed_chunked_latest_value --halt linux93 \
  -o gen-out/zisk_mtx_committed_chunked_latest_value

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" mode="$2" expect="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_cscl_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_cscl_${name}.output"

  MODE="$mode" python3 -c "
import os, struct, sys
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', int(os.environ['MODE'])))
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_mtx_committed_chunked_latest_value.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_cscl_${name}.emu.log" 2>&1 || true

  local got
  got=$(python3 -c "
words=[]
d=open('$out_file','rb').read()
for off in range(0,32,8):
    words.append(int.from_bytes(d[off:off+8], 'little'))
print(':'.join(str(x) for x in words))
")
  if [[ "$got" == "$expect" ]]; then
    printf "  %-14s OK   [%s]\n" "$name" "$got"; return 0
  fi
  printf "  %-14s FAIL got=[%s] expected=[%s]\n" "$name" "$got" "$expect"; return 1
}

FAILED=0
# status:value:recipientScratchLow:slotScratchLow
run_case "empty"       0 "0:238:170:7" || FAILED=1
run_case "no_match"    1 "0:238:170:7" || FAILED=1
run_case "chunk0"      2 "1:17:170:7"  || FAILED=1
run_case "chunk1"      3 "1:119:170:8" || FAILED=1
run_case "latest_page" 4 "1:119:170:7" || FAILED=1
run_case "over_cap"    5 "2:238:0:0"   || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chunked committed-storage lookup scans pages and preserves latest-value semantics"
  exit 0
else
  echo "==> FAIL"; exit 1
fi
