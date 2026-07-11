#!/usr/bin/env bash
# codegen-zisk-bal-section-info-check.sh -- verify BAL SSZ locator on real EEST inputs.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"
TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.6.0}"
FILTER="${1:-block_access_lists_eip4895}"
LIMIT="${2:-16}"
ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi
FX="${EEST_FIXTURES_DIR:-$REPO_ROOT/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX" >&2; exit 1; }
RUN="$REPO_ROOT/gen-out/bsi-check"; rm -rf "$RUN"; mkdir -p "$RUN"

echo "==> build + emit probe + convert fixtures"
lake build codegen >/dev/null
lake exe codegen --program zisk_bal_section_info --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_bal_section_info" >/dev/null
python3 scripts/eest-stateless-to-input.py --fixtures-dir "$FX" --out-dir "$RUN" \
  --limit "$LIMIT" --filter "$FILTER" >/dev/null
MAN="$RUN/manifest.tsv"; [[ -s "$MAN" ]] || { echo "no fixtures" >&2; exit 1; }

uv run --directory execution-specs --quiet python3 - "$MAN" "$REPO_ROOT/scripts" "$REPO_ROOT" > "$RUN/expected.tsv" <<'PY'
import os, sys
sys.path.insert(0, sys.argv[2])
import rlp
repo = sys.argv[3]
base = 0x40000000 + 18
for line in open(sys.argv[1]):
    fields = line.rstrip("\n").split("\t")
    if len(fields) < 2:
        continue
    label, inp = fields[0], fields[1]
    if not os.path.isabs(inp):
        inp = os.path.join(repo, inp)
    try:
        data = open(inp, "rb").read()
        length = int.from_bytes(data[0:8], "little")
        outer = data[8:8 + length][2:]
        u32 = lambda b, o: int.from_bytes(b[o:o + 4], "little")
        ep = outer[60:]
        npr = outer[16:]
        bal_off = u32(ep, 528)
        bal_end_rel = u32(npr, 4) - 44
        bal = ep[bal_off:bal_end_rel]
        ptr = base + 60 + bal_off
        print(f"{label}\t{ptr}\t{len(bal)}\t{len(rlp.decode(bal))}")
    except Exception:
        print(f"{label}\tERR\tERR\tERR")
PY

declare -A INP REL
while IFS=$'\t' read -r label inp expected status invalid rel; do
  INP[$label]="$inp"; REL[$label]="$rel"
done < "$MAN"

pass=0; fail=0
while IFS=$'\t' read -r label exp_ptr exp_len exp_count; do
  [[ "$exp_ptr" == "ERR" ]] && continue
  inp="${INP[$label]:-}"; [[ -z "$inp" ]] && continue
  out="$RUN/$label.out"
  "$ZISKEMU" -e gen-out/zisk_bal_section_info.elf -i "$inp" -o "$out" -n 5000000 >/dev/null 2>&1 </dev/null || {
    echo "  ERROR  $label"; fail=$((fail+1)); continue
  }
  st="$(od -An -tu8 -j 0 -N 8 "$out" | tr -d ' \n')"
  ptr="$(od -An -tu8 -j 8 -N 8 "$out" | tr -d ' \n')"
  len="$(od -An -tu8 -j 16 -N 8 "$out" | tr -d ' \n')"
  count="$(od -An -tu8 -j 24 -N 8 "$out" | tr -d ' \n')"
  if [[ "$st" == "0" && "$ptr" == "$exp_ptr" && "$len" == "$exp_len" && "$count" == "$exp_count" ]]; then
    echo "  PASS   $(basename "${REL[$label]}") len=$len count=$count"
    pass=$((pass+1))
  else
    echo "  FAIL   $label status=$st ptr=$ptr len=$len count=$count"
    echo "    expected ptr=$exp_ptr len=$exp_len count=$exp_count ($(basename "${REL[$label]}"))"
    fail=$((fail+1))
  fi
done < "$RUN/expected.tsv"

echo "bal_section_info: pass=$pass fail=$fail"
[[ "$fail" -eq 0 && "$pass" -gt 0 ]] && echo "==> PASS: bal_section_info locates BAL RLP" \
  || { echo "==> FAIL"; exit 1; }
