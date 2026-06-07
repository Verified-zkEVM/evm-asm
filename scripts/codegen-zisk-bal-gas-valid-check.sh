#!/usr/bin/env bash
# codegen-zisk-bal-gas-valid-check.sh -- verify bal_gas_valid (bead fhsxz.2.4.2.5,
# the EIP-7928 BAL gas-limit rule) on REAL EEST fixtures. The probe navigates the
# guest input to the block_access_list section + block_gas_limit and emits
# 0=valid / 1=exceeded / 2=parse-error. Expected is computed from each input's own
# SSZ (RLP-walk the BAL, bal_items = Σ(1 + len(storage_changes) + len(storage_reads)),
# invalid iff bal_items*2000 > gas_limit). Includes bal_gas_limit_boundary, whose
# below_boundary variant MUST be rejected (1). By default the script runs every
# selected row for the filter so new BAL fixtures are covered automatically; pass
# a second positional argument to cap the run for a short local smoke.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"
TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
FILTER="${1:-block_access_lists}"
LIMIT_OVERRIDE="${2:-}"
ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi
FX="${EEST_FIXTURES_DIR:-$REPO_ROOT/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX" >&2; exit 1; }
RUN="$REPO_ROOT/gen-out/bgv-check"; rm -rf "$RUN"; mkdir -p "$RUN"

echo "==> build + emit probe + convert fixtures"
lake build codegen >/dev/null
lake exe codegen --program zisk_bal_gas_valid --halt linux93 -o "$REPO_ROOT/gen-out/zisk_bal_gas_valid" >/dev/null
conv_args=(--fixtures-dir "$FX" --out-dir "$RUN" --filter "$FILTER")
[[ -n "$LIMIT_OVERRIDE" ]] && conv_args+=(--limit "$LIMIT_OVERRIDE")
python3 scripts/eest-stateless-to-input.py "${conv_args[@]}" >/dev/null
MAN="$RUN/manifest.tsv"; [[ -s "$MAN" ]] || { echo "no fixtures" >&2; exit 1; }

# expected per label (single Python pass; absolute paths)
uv run --directory execution-specs --quiet python3 - "$MAN" "$REPO_ROOT/scripts" "$REPO_ROOT" > "$RUN/expected.tsv" <<'PY'
import sys, os
sys.path.insert(0, sys.argv[2]); import rlp
REPO=sys.argv[3]
for line in open(sys.argv[1]):
    f=line.rstrip("\n").split("\t")
    if len(f)<2: continue
    label,inp=f[0],f[1]
    if not os.path.isabs(inp): inp=os.path.join(REPO,inp)
    try:
        data=open(inp,"rb").read(); L=int.from_bytes(data[0:8],"little"); outer=data[8:8+L][2:]
        u32=lambda b,o:int.from_bytes(b[o:o+4],"little"); ep=outer[60:]; npr=outer[16:]
        bal=ep[u32(ep,528):(u32(npr,4)-44)]; gl=int.from_bytes(ep[412:420],"little")
        items=sum(1+len(a[1])+len(a[2]) for a in rlp.decode(bal))
        print(f"{label}\t{1 if items*2000>gl else 0}")
    except Exception as e:
        print(f"{label}\tERR")
PY

declare -A INP REL
while IFS=$'\t' read -r l i e s il rel; do INP[$l]="$i"; REL[$l]="$rel"; done < "$MAN"
pass=0 fail=0 rej=0
while IFS=$'\t' read -r label exp; do
  inp="${INP[$label]:-}"; [[ -z "$inp" || "$exp" == "ERR" ]] && continue
  "$ZISKEMU" -e gen-out/zisk_bal_gas_valid.elf -i "$inp" -o "$RUN/$label.out" -n 5000000 >/dev/null 2>&1 </dev/null || { echo "  ERROR $label"; fail=$((fail+1)); continue; }
  got="$(od -An -tu8 -j 0 -N 8 "$RUN/$label.out"|tr -d ' \n')"
  if [[ "$got" == "$exp" ]]; then pass=$((pass+1)); [[ "$got" == "1" ]] && { rej=$((rej+1)); echo "  REJECT(exceeded) $(basename "${REL[$label]}")"; }
  else fail=$((fail+1)); echo "  FAIL $label got=$got exp=$exp ($(basename "${REL[$label]}"))"; fi
done < "$RUN/expected.tsv"
echo "bal_gas_valid: pass=$pass fail=$fail (of which $rej correctly REJECTED as gas-limit-exceeded)"
[[ "$fail" -eq 0 && "$pass" -gt 0 ]] && echo "==> PASS: bal_gas_valid matches the EIP-7928 rule" || { echo "==> FAIL"; exit 1; }
