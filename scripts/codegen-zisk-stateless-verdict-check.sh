#!/usr/bin/env bash
# codegen-zisk-stateless-verdict-check.sh -- verify stateless_verdict_from_ssz
# (bead evm-asm-fhsxz.2.4.2) on REAL EEST fixtures.
#
# The `zisk_stateless_verdict` probe is fed the SAME ziskemu `-i` input the
# stateless guest consumes (SSZ_BASE = 0x40000012), navigates it with the real
# extractors, runs step2_verdict, and emits the verdict bit at OUTPUT+0. We
# compare that bit against the fixture's expected `successful_validation`
# (the manifest's succ_bit). This proves the verdict on REAL input (closing
# the "synthetic-only" gap) and is the de-risk before wiring into the guest
# epilogue.
#
# Reports, per fixture: verdict==expected (MATCH) / verdict!=expected (DIFF).
# A valid block whose verdict the guest cannot yet confirm (tx-bearing,
# non-existent-account, repeat) shows verdict=0 vs exp=1 = a conservative MISS
# (expected; not a soundness failure). A DIFF where verdict=1 vs exp=0 would be
# a FALSE POSITIVE (a real bug) -- flagged loudly.
#
# Usage:
#   codegen-zisk-stateless-verdict-check.sh [--filter SUB] [--skip N] [--limit N]
#     --max-failures N         stop after N ERROR/FALSE-POSITIVE/DIFF results
#     --stop-after-failures N  alias for --max-failures
#     --bsr-witness-cap N      override BSR witness cap (experiment)
#     --bsr-bal-cap N          override BSR BAL row cap (experiment)
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.6.1}"
FILTER="eip4895"
SKIP=0
LIMIT=30
STEPS="${EEST_STEPS:-50000000}"
BSR_WITNESS_CAP="${EEST_BSR_WITNESS_CAP:-}"
BSR_BAL_CAP="${EEST_BSR_BAL_CAP:-}"
MAX_FAILURES=""

usage() {
  cat <<'USAGE'
Usage:
  scripts/codegen-zisk-stateless-verdict-check.sh [options]

Options:
  --filter SUBSTR          only fixtures whose relpath contains SUBSTR
  --skip N                 skip first N fixtures
  --limit N                cap to N probe invocations (default 30)
  --steps N                ziskemu max steps (default $EEST_STEPS or 50000000)
  --max-failures N         stop after N ERROR/FALSE-POSITIVE/DIFF results
  --stop-after-failures N  alias for --max-failures
  --bsr-witness-cap N      override BSR witness cap (experiment)
  --bsr-bal-cap N          override BSR BAL row cap (experiment)
  -h, --help               show this help
USAGE
}

require_arg() {
  local opt="$1"
  if [[ $# -lt 2 || -z "${2:-}" ]]; then
    echo "$opt requires an argument" >&2
    usage >&2
    exit 1
  fi
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) usage; exit 0 ;;
    --filter) require_arg "$1" "${2:-}"; FILTER="$2"; shift 2 ;;
    --skip)   require_arg "$1" "${2:-}"; SKIP="$2";   shift 2 ;;
    --limit)  require_arg "$1" "${2:-}"; LIMIT="$2";  shift 2 ;;
    --steps)  require_arg "$1" "${2:-}"; STEPS="$2";  shift 2 ;;
    --max-failures|--stop-after-failures) require_arg "$1" "${2:-}"; MAX_FAILURES="$2"; shift 2 ;;
    --bsr-witness-cap) require_arg "$1" "${2:-}"; BSR_WITNESS_CAP="$2"; shift 2 ;;
    --bsr-bal-cap)     require_arg "$1" "${2:-}"; BSR_BAL_CAP="$2";     shift 2 ;;
    *) echo "unknown arg: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if ! [[ "$SKIP" =~ ^[0-9]+$ ]]; then
  echo "--skip must be a nonnegative integer (got: $SKIP)" >&2
  exit 1
fi

if ! [[ "$LIMIT" =~ ^[0-9]+$ ]] || [[ "$LIMIT" -lt 1 ]]; then
  echo "--limit must be a positive integer (got: $LIMIT)" >&2
  exit 1
fi
if ! [[ "$STEPS" =~ ^[0-9]+$ ]] || [[ "$STEPS" -lt 1 ]]; then
  echo "--steps must be a positive integer (got: $STEPS)" >&2
  exit 1
fi
if [[ -n "$MAX_FAILURES" ]] && { ! [[ "$MAX_FAILURES" =~ ^[0-9]+$ ]] || [[ "$MAX_FAILURES" -lt 1 ]]; }; then
  echo "--max-failures must be a positive integer when set (got: $MAX_FAILURES)" >&2
  exit 1
fi
if [[ -n "$BSR_WITNESS_CAP" ]] && ! [[ "$BSR_WITNESS_CAP" =~ ^[0-9]+$ ]]; then
  echo "--bsr-witness-cap must be a nonnegative integer when set (got: $BSR_WITNESS_CAP)" >&2
  exit 1
fi
if [[ -n "$BSR_BAL_CAP" ]] && ! [[ "$BSR_BAL_CAP" =~ ^[0-9]+$ ]]; then
  echo "--bsr-bal-cap must be a nonnegative integer when set (got: $BSR_BAL_CAP)" >&2
  exit 1
fi

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

FX="${EEST_FIXTURES_DIR:-$REPO_ROOT/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

echo "==> lake build codegen"
lake build codegen >/dev/null

resolve_riscv_tool() {
  local env_var="$1"; shift
  local from_env="${!env_var:-}"
  local candidate
  if [[ -n "$from_env" ]]; then
    echo "$from_env"
    return 0
  fi
  for candidate in "$@"; do
    if command -v "$candidate" >/dev/null 2>&1; then
      command -v "$candidate"
      return 0
    fi
  done
  echo "$1"
}

patch_bsr_caps_and_relink() {
  local asm="gen-out/zisk_stateless_verdict_v2.s"
  local obj="gen-out/zisk_stateless_verdict_v2.o"
  local elf="gen-out/zisk_stateless_verdict_v2.elf"
  local old_witness="  la t0, bsr_fail_code; sd zero, 0(t0); li t1, 262144; bgtu a2, t1, .Lbsr_cons_change_cap"
  local new_witness="  la t0, bsr_fail_code; sd zero, 0(t0); li t1, $BSR_WITNESS_CAP; bgtu a2, t1, .Lbsr_cons_change_cap"
  local old_bal=$'  li t0, 2000; divu t1, a0, t0\n  la t2, bsr_bal_count; ld t6, 0(t2); bgtu t6, t1, .Lbsr_cons_change_cap; add t0, s1, t6; li t1, 100018; bgtu t0, t1, .Lbsr_cons_change_cap'
  local new_bal=$'  li t0, 2000; divu t1, a0, t0\n  la t2, bsr_bal_count; ld t6, 0(t2); bgtu t6, t1, .Lbsr_cons_change_cap; li t1, '"$BSR_BAL_CAP"$'; bgtu t6, t1, .Lbsr_cons_change_cap; add t0, s1, t6; li t1, 100018; bgtu t0, t1, .Lbsr_cons_change_cap'
  local as_tool ld_tool

  python3 - "$asm" "$BSR_WITNESS_CAP" "$old_witness" "$new_witness" "$BSR_BAL_CAP" "$old_bal" "$new_bal" <<'PYPATCH'
import sys
path, witness_cap, old_witness, new_witness, bal_cap, old_bal, new_bal = sys.argv[1:]
text = open(path, "r", encoding="utf-8").read()
replacements = []
if witness_cap:
    replacements.append(("block_state_root witness-cap", old_witness, new_witness))
if bal_cap:
    replacements.append(("block_state_root BAL row-cap", old_bal, new_bal))
for label, old, new in replacements:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"expected exactly one {label} instruction, found {count}")
    text = text.replace(old, new, 1)
open(path, "w", encoding="utf-8").write(text)
PYPATCH

  as_tool="$(resolve_riscv_tool RISCV_AS riscv64-unknown-elf-as riscv64-elf-as)"
  ld_tool="$(resolve_riscv_tool RISCV_LD riscv64-unknown-elf-ld riscv64-elf-ld)"
  "$as_tool" -march=rv64imac -mno-relax -o "$obj" "$asm"
  "$ld_tool" -Ttext=0x80000000 -Tdata=0xa3000000 \
    --section-start=.sszscratch=0xbf500000 \
    -nostdlib --no-relax -o "$elf" "$obj"
}

if [[ -n "$BSR_WITNESS_CAP" || -n "$BSR_BAL_CAP" ]]; then
  cap_note=""
  [[ -n "$BSR_WITNESS_CAP" ]] && cap_note="bsr_witness_cap=$BSR_WITNESS_CAP"
  [[ -n "$BSR_BAL_CAP" ]] && cap_note="${cap_note:+$cap_note, }bsr_bal_cap=$BSR_BAL_CAP"
  echo "==> emit zisk_stateless_verdict_v2 probe assembly (experimental $cap_note)"
  lake exe codegen --program zisk_stateless_verdict_v2 --halt linux93 -o gen-out/zisk_stateless_verdict_v2 --asm-only >/dev/null
  patch_bsr_caps_and_relink
else
  echo "==> emit zisk_stateless_verdict_v2 probe ELF"
  lake exe codegen --program zisk_stateless_verdict_v2 --halt linux93 -o gen-out/zisk_stateless_verdict_v2 >/dev/null
fi

RUN_DIR="$REPO_ROOT/gen-out/verdict-run"
rm -rf "$RUN_DIR"; mkdir -p "$RUN_DIR"
selection="filter=$FILTER, limit=$LIMIT"
conv_args=(--fixtures-dir "$FX" --out-dir "$RUN_DIR" --limit "$LIMIT" --filter "$FILTER")
if [[ "$SKIP" != "0" ]]; then
  selection="$selection, skip=$SKIP"
  conv_args+=(--skip "$SKIP")
fi
echo "==> convert fixtures (tag=$TAG, $selection)"
python3 scripts/eest-stateless-to-input.py "${conv_args[@]}"
MANIFEST="$RUN_DIR/manifest.tsv"
[[ -s "$MANIFEST" ]] || { echo "no blocks selected" >&2; exit 1; }

format_dbg() {
  local out="$1"
  local raw
  local -a labels=(
    bv_fail
    header
    state
    bal_count
    bsr_fail
    change_count
    witness_len
    baacd_fail
    bacv_fail
    baap_fail
    sri_index
    sri_mode
    sri_status
  )
  local -a words=()
  local i value dbg=""

  raw="$(od -An -v -tu8 -j 8 -N 104 "$out" 2>/dev/null | xargs || true)"
  read -r -a words <<< "$raw"
  for i in "${!labels[@]}"; do
    value="${words[$i]:-?}"
    dbg="${dbg:+$dbg }${labels[$i]}=$value"
  done
  echo "$dbg"
}

case_suffix() {
  local block_gas_limit="$1"
  local relpath="$2"
  if [[ "$block_gas_limit" =~ ^[0-9]+$ ]]; then
    echo "gas=$block_gas_limit  $relpath"
  else
    echo "$relpath"
  fi
}

total=0 match=0 miss=0 fp=0 err=0 diff=0 stopEarly=0

failure_limit_reached() {
  [[ -n "$MAX_FAILURES" && $((err + fp + diff)) -ge "$MAX_FAILURES" ]]
}

while IFS=$'\t' read -r label input expected_hex succ_bit input_len block_gas_limit relpath _extra; do
  if [[ -z "${relpath:-}" ]]; then
    relpath="$block_gas_limit"
    block_gas_limit=""
  fi
  total=$((total + 1))
  out="$RUN_DIR/$label.vout"
  if ! "$ZISKEMU" -e gen-out/zisk_stateless_verdict_v2.elf -i "$input" -o "$out" \
        -n "$STEPS" >/dev/null 2>&1 </dev/null; then
    err=$((err + 1)); echo "  ERROR(exit)   $relpath"
    if failure_limit_reached; then stopEarly=1; break; fi
    continue
  fi
  v="$(od -An -tu1 -j 0 -N 1 "$out" 2>/dev/null | tr -d ' \n')"
  if [[ -z "$v" ]]; then
    err=$((err + 1)); echo "  ERROR(short)  $relpath"
    if failure_limit_reached; then stopEarly=1; break; fi
    continue
  fi
  dbg="$(format_dbg "$out")"
  suffix="$(case_suffix "$block_gas_limit" "$relpath")"
  if [[ "$v" == "$succ_bit" ]]; then
    match=$((match + 1)); echo "  MATCH  verdict=$v exp=$succ_bit dbg=[$dbg]  $suffix"
  elif [[ "$v" == "0" && "$succ_bit" == "1" ]]; then
    miss=$((miss + 1)); echo "  miss   verdict=0 exp=1 (conservative) dbg=[$dbg]  $suffix"
  elif [[ "$v" == "1" && "$succ_bit" == "0" ]]; then
    fp=$((fp + 1)); echo "  ** FALSE POSITIVE ** verdict=1 exp=0 dbg=[$dbg]  $suffix"
    if failure_limit_reached; then stopEarly=1; break; fi
  else
    diff=$((diff + 1))
    echo "  DIFF   verdict=$v exp=$succ_bit dbg=[$dbg]  $suffix"
    if failure_limit_reached; then stopEarly=1; break; fi
  fi
done < "$MANIFEST"

if [[ "$stopEarly" -eq 1 ]]; then
  echo "==> stopped after $((err + fp + diff)) failure(s) (--max-failures $MAX_FAILURES)"
fi
echo "============================================================"
echo "stateless_verdict on real $FILTER fixtures: total=$total"
echo "  MATCH (verdict==expected):        $match"
echo "  conservative miss (v=0 exp=1):    $miss"
echo "  FALSE POSITIVE (v=1 exp=0):       $fp"
echo "  unexpected DIFF:                  $diff"
echo "  errors:                           $err"
if [[ "$fp" -gt 0 ]]; then
  echo "==> FAIL: false positives present (unsound)"; exit 1
fi
if [[ "$match" -eq 0 ]]; then
  echo "==> no exact matches yet (all conservative misses / errors)"; exit 0
fi
echo "==> PASS: $match verdict(s) match real fixtures, 0 false positives"
