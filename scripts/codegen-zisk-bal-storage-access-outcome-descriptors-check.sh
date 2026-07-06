#!/usr/bin/env bash
# codegen-zisk-bal-storage-access-outcome-descriptors-check.sh -- storage access outcomes -> BAL storage no-op descriptors.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

VDIR="$REPO_ROOT/gen-out/bal-storage-access-outcomes"
mkdir -p "$VDIR"

echo "==> generate expected storage descriptor paths"
uv run --directory execution-specs --quiet python3 - "$VDIR" <<'PYGEN'
import os
import sys
from ethereum.crypto.hash import keccak256

outdir = sys.argv[1]
os.makedirs(outdir, exist_ok=True)

def path(slot: bytes) -> str:
    nibbles = bytearray()
    for b in keccak256(slot):
        nibbles.append(b >> 4)
        nibbles.append(b & 0x0F)
    return nibbles.hex()

with open(f"{outdir}/expected.paths", "w") as f:
    f.write(path(bytes.fromhex("11" * 32)) + "\n")
    f.write(path(bytes.fromhex("22" * 32)) + "\n")

print("expected rows=2: committed slot A and slot B for selected account")
PYGEN

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_bal_storage_access_outcome_descriptors probe ELF"
lake exe codegen --program zisk_bal_storage_access_outcome_descriptors --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_bal_storage_access_outcome_descriptors"

out="$VDIR/output.bin"
"$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_bal_storage_access_outcome_descriptors.elf" \
  -o "$out" -n 2000000 >/dev/null 2>&1 </dev/null

status="$(od -An -tu8 -j 0 -N 8 "$out" | tr -d ' \n')"
count="$(od -An -tu8 -j 8 -N 8 "$out" | tr -d ' \n')"
fail=0
if [[ "$status" != "0" ]]; then
  echo "  FAIL   status=$status"
  fail=1
fi
if [[ "$count" != "2" ]]; then
  echo "  FAIL   count=$count expected=2"
  fail=1
fi

mapfile -t expected_paths < "$VDIR/expected.paths"
for i in 0 1; do
  desc_off=$((16 + 40 * i))
  exp_path_ptr=$((0xA0010060 + 64 * i))
  path_ptr="$(od -An -tu8 -j "$desc_off" -N 8 "$out" | tr -d ' \n')"
  path_len="$(od -An -tu8 -j $((desc_off + 8)) -N 8 "$out" | tr -d ' \n')"
  value_len="$(od -An -tu8 -j $((desc_off + 24)) -N 8 "$out" | tr -d ' \n')"
  mode="$(od -An -tu8 -j $((desc_off + 32)) -N 8 "$out" | tr -d ' \n')"
  path="$(xxd -p -s $((96 + 64 * i)) -l 64 "$out" | tr -d '\n')"
  if [[ "$path_ptr" != "$exp_path_ptr" || "$path_len" != "64" || "$value_len" != "0" || "$mode" != "3" || "$path" != "${expected_paths[$i]}" ]]; then
    echo "  FAIL   row=$i path_ptr=$path_ptr path_len=$path_len value_len=$value_len mode=$mode"
    echo "         expected path_ptr=$exp_path_ptr path_len=64 value_len=0 mode=3"
    echo "         expected path=${expected_paths[$i]}"
    echo "         actual   path=$path"
    fail=1
  else
    echo "  PASS   row=$i mode=3 value_len=0 path=${path:0:16}..."
  fi
done

if [[ "$fail" -eq 0 ]]; then
  echo "==> PASS: storage access outcomes materialize read-only BAL storage descriptors"
else
  echo "==> FAIL"
  exit 1
fi
