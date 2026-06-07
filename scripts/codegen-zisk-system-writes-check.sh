#!/usr/bin/env bash
# codegen-zisk-system-writes-check.sh -- verify system_write_descriptors
# (bead fhsxz.2.4.2.5 steps a/b) on REAL EEST fixtures: derive the EIP-2935 +
# EIP-4788 (slot, value) pairs the block writes straight from the SSZ payload and
# check them against the fixture's own header fields (number/timestamp/parentHash).
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"
TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
FILTER="${1:-eip4895}"; LIMIT="${2:-12}"
ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi
FX="${EEST_FIXTURES_DIR:-$REPO_ROOT/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX" >&2; exit 1; }
RUN="$REPO_ROOT/gen-out/swd-run"; rm -rf "$RUN"; mkdir -p "$RUN"

echo "==> build + emit probe + convert fixtures"
lake build codegen >/dev/null
lake exe codegen --program zisk_system_write_descriptors --halt linux93 -o "$REPO_ROOT/gen-out/zisk_system_write_descriptors" >/dev/null
python3 scripts/eest-stateless-to-input.py --fixtures-dir "$FX" --out-dir "$RUN" --limit "$LIMIT" --filter "$FILTER" >/dev/null
MAN="$RUN/manifest.tsv"; [[ -s "$MAN" ]] || { echo "no fixtures" >&2; exit 1; }

# Derive expected system writes from each input's SSZ.
uv run --directory execution-specs --quiet python3 - "$MAN" <<'PY'
import sys
man=open(sys.argv[1]).read().strip().splitlines()
out=[]
for line in man:
    f=line.split("\t"); inp=f[1]
    data=open(inp,"rb").read()
    L=int.from_bytes(data[0:8],"little"); outer=data[8:8+L][2:]
    ep=outer[60:]
    number=int.from_bytes(ep[404:412],"little"); ts=int.from_bytes(ep[428:436],"little")
    ph=ep[0:32]
    s2935=(((number-1) & ((1<<64)-1)) % 8192).to_bytes(32,"big")
    v2935=ph.lstrip(b"\x00") or b""
    ts_slot=ts % 8191
    s4788=ts_slot.to_bytes(32,"big")
    v4788=ts.to_bytes(8,"big").lstrip(b"\x00") or b""
    s4788r=(ts_slot + 8191).to_bytes(32,"big")
    v4788r=outer[24:56].lstrip(b"\x00") or b""
    out.append("\t".join([f[0], inp, s2935.hex(), v2935.hex(), s4788.hex(), v4788.hex(), s4788r.hex(), v4788r.hex()]))
open(sys.argv[1]+".exp","w").write("\n".join(out)+"\n")
print(f"derived expected for {len(out)} fixtures")
PY

fail=0 n=0
while IFS=$'\t' read -r label inp s2935 v2935 s4788 v4788 s4788r v4788r; do
  n=$((n+1)); out="$RUN/$label.out"
  "$ZISKEMU" -e gen-out/zisk_system_write_descriptors.elf -i "$inp" -o "$out" -n 5000000 >/dev/null 2>&1 </dev/null
  g_s2935="$(xxd -p -s 0 -l 32 "$out"|tr -d '\n')"
  g_l2935="$(od -An -tu8 -j 32 -N 8 "$out"|tr -d ' \n')"
  g_v2935="$(xxd -p -s 40 -l "${g_l2935:-0}" "$out" 2>/dev/null|tr -d '\n')"
  g_s4788="$(xxd -p -s 72 -l 32 "$out"|tr -d '\n')"
  g_l4788="$(od -An -tu8 -j 104 -N 8 "$out"|tr -d ' \n')"
  g_v4788="$(xxd -p -s 112 -l "${g_l4788:-0}" "$out" 2>/dev/null|tr -d '\n')"
  g_s4788r="$(xxd -p -s 144 -l 32 "$out"|tr -d '\n')"
  g_l4788r="$(od -An -tu8 -j 176 -N 8 "$out"|tr -d ' \n')"
  g_v4788r="$(xxd -p -s 184 -l "${g_l4788r:-0}" "$out" 2>/dev/null|tr -d '\n')"
  if [[ "$g_s2935" == "$s2935" && "$g_v2935" == "$v2935" && "$g_s4788" == "$s4788" && "$g_v4788" == "$v4788" && "$g_s4788r" == "$s4788r" && "$g_v4788r" == "$v4788r" ]]; then
    echo "  PASS $(basename "$inp")"
  else
    echo "  FAIL $(basename "$inp")"
    echo "    2935 slot g=$g_s2935 e=$s2935"; echo "    2935 val  g=$g_v2935 e=$v2935"
    echo "    4788 slot g=$g_s4788 e=$s4788"; echo "    4788 val  g=$g_v4788 e=$v4788"
    echo "    4788 root slot g=$g_s4788r e=$s4788r"; echo "    4788 root val  g=$g_v4788r e=$v4788r"
    fail=1
  fi
done < "$MAN.exp"
echo "checked $n fixtures"
[[ "$fail" -eq 0 ]] && echo "==> PASS: system_write_descriptors matches fixture-derived EIP-2935/4788 writes" || { echo "==> FAIL"; exit 1; }
