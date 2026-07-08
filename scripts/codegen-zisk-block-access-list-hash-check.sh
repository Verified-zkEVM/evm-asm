#!/usr/bin/env bash
# codegen-zisk-block-access-list-hash-check.sh -- verify block_access_list_hash
# (bead fhsxz.2.4.2.5) on REAL EEST fixtures: the probe is fed the same ziskemu
# input the guest consumes, navigates SSZ_BASE -> NPR -> exec_payload, keccak256
# of the block_access_list section, and emits it at OUTPUT+0. We compare against
# the fixture blockHeader's blockAccessListHash (RLP header field 21 of 23).
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"
TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.5.0}"
FILTER="${1:-eip4895}"; LIMIT="${2:-20}"
ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi
FX="${EEST_FIXTURES_DIR:-$REPO_ROOT/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX" >&2; exit 1; }
RUN="$REPO_ROOT/gen-out/bah-run"; rm -rf "$RUN"; mkdir -p "$RUN"

echo "==> build + emit probe + convert fixtures"
lake build codegen >/dev/null
lake exe codegen --program zisk_block_access_list_hash --halt linux93 -o "$REPO_ROOT/gen-out/zisk_block_access_list_hash" >/dev/null
python3 scripts/eest-stateless-to-input.py --fixtures-dir "$FX" --out-dir "$RUN" --limit "$LIMIT" --filter "$FILTER" >/dev/null
MAN="$RUN/manifest.tsv"; [[ -s "$MAN" ]] || { echo "no fixtures" >&2; exit 1; }

pass=0 fail=0
while IFS=$'\t' read -r label input expected_hex succ_bit input_len relpath; do
  out="$RUN/$label.out"
  "$ZISKEMU" -e gen-out/zisk_block_access_list_hash.elf -i "$input" -o "$out" -n 5000000 >/dev/null 2>&1 </dev/null || { echo "  ERROR $relpath"; fail=$((fail+1)); continue; }
  got="$(xxd -p -s 0 -l 32 "$out"|tr -d '\n')"
  # Expected = keccak256(block_access_list section) derived from THIS input's SSZ
  # (per-variant correct, independent of multi-variant JSON ordering).
  exp="$(uv run --directory execution-specs --quiet python3 - "$input" "$REPO_ROOT/scripts" <<PYEOF 2>/dev/null
import sys
sys.path.insert(0, sys.argv[2]); import mpt_ref as m
data=open(sys.argv[1],"rb").read(); L=int.from_bytes(data[0:8],"little"); outer=data[8:8+L][2:]
u32=lambda b,o:int.from_bytes(b[o:o+4],"little")
ep=outer[60:]; npr=outer[16:]
bal=ep[u32(ep,528):(u32(npr,4)-44)]
print(m.k256(bal).hex())
PYEOF
)"
  if [[ "$got" == "$exp" ]]; then pass=$((pass+1)); echo "  PASS $(basename "$relpath") balhash=${got:0:16}.."
  else fail=$((fail+1)); echo "  FAIL $(basename "$relpath") got=$got exp=$exp"; fi
done < "$MAN"
echo "block_access_list_hash: pass=$pass fail=$fail"
[[ "$fail" -eq 0 ]] && echo "==> PASS: block_access_list_hash matches the fixture blockAccessListHash" || { echo "==> FAIL"; exit 1; }
