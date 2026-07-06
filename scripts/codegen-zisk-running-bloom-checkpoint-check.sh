#!/usr/bin/env bash
# codegen-zisk-running-bloom-checkpoint-check.sh
#
# Exercise the 256-byte running bloom zero/copy helpers used by the
# future call-frame rollback path. The probe snapshots a hot bloom into
# checkpoint depth 0, clears the hot buffer, restores it, and emits the
# restored bytes.
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

echo "==> emit zisk_running_bloom_checkpoint ELF"
lake exe codegen --program zisk_running_bloom_checkpoint --halt linux93 \
  -o gen-out/zisk_running_bloom_checkpoint

REPO_ROOT="$(pwd)"

# run_case <name> <bloom_hex_256B>
run_case() {
  local name="$1" bloom="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_running_bloom_checkpoint_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_running_bloom_checkpoint_${name}.output"

  python3 -c "
import struct, sys
bloom = bytes.fromhex('$bloom')
assert len(bloom) == 256, len(bloom)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', 0))
    f.write(bloom)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_running_bloom_checkpoint.elf \
    -i "$in_file" -o "$out_file" -n 200000 \
    >"$REPO_ROOT/gen-out/zisk_running_bloom_checkpoint_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -c 256 "$out_file" | tr -d '\n')"

  if [[ "$actual" == "$bloom" ]]; then
    local nbits; nbits="$(python3 -c "print(bin(int('$actual' or '0', 16)).count('1'))")"
    printf "  %-26s OK   bits_set=%d\n" "$name" "$nbits"
    return 0
  else
    printf "  %-26s FAIL\n" "$name"
    printf "      actual:   %s...\n" "${actual:0:80}"
    printf "      expected: %s...\n" "${bloom:0:80}"
    return 1
  fi
}

ZERO256="$(python3 -c "print('00' * 256)")"
ALL_FF256="$(python3 -c "print('ff' * 256)")"
SPARSE="$(python3 -c "b=bytearray(256); b[0]=1; b[31]=0x80; b[127]=0x42; b[255]=0xff; print(bytes(b).hex())")"
PATTERN="$(python3 -c "print(bytes((i * 17 + 3) % 256 for i in range(256)).hex())")"

FAILED=0
run_case "zero"     "$ZERO256" || FAILED=1
run_case "all_ff"   "$ALL_FF256" || FAILED=1
run_case "sparse"   "$SPARSE" || FAILED=1
run_case "pattern"  "$PATTERN" || FAILED=1

if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: running bloom checkpoint zero/copy/restore preserves 256-byte blooms"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
