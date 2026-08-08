#!/usr/bin/env bash
# eest-specref-check.sh -- Run the SpecRef reference model
# (`EvmAsm.Stateless.SpecRef.run_stateless_guest`, the pure-Lean functional
# port of execution-specs' Amsterdam stateless-guest spec) against the *same*
# EEST "zkevm" conformance fixtures exercised by
# scripts/codegen-eest-stateless-check.sh, and report how the reference
# output compares to each fixture's recorded `statelessOutputBytes`.
#
# Why this exists alongside the guest harness (ziskemu/spike):
#   SpecRef runs in-process (a `lake exe`, no ELF / emulator / step budget), so
#   it is a fast, environment-free way to tie the Lean port's full path —
#   deserialization / SSZ-codec / NPR-root hashing / header / chain-config /
#   witness-assembly / execution — to the canonical conformance fixtures.
#   Fixture selection (tag, --all/--skip/--limit/--filter,
#   --random/--seed/--reverse) is identical to the guest harness so the two
#   report on the same rows.
#
# The execution seam (post-s1d19.5):
#   SpecRef's `run_stateless_guest` takes an `ExecutionSeam` defaulting to the
#   full ported `elExecute` (`PrecompilesTable.lean`). The placeholder
#   `executeAlwaysOk` still exists for unit tests but is NOT the harness
#   default. The Python `run_stateless_guest` at the pinned fixture tag
#   (`scripts/eest-fixture-tag.txt`) runs the same EVM surface. ALL THREE
#   output regions are therefore expected to match:
#
#     * root  (bytes 0:32,  new_payload_request_root)  -- pre-execution hashing;
#              SpecRef MUST match on every fixture.            [gateable]
#     * succ  (byte 32,     successful_validation)     -- real execution verdict;
#              un-allowlisted divergence is FAIL (rc=1).       [gateable]
#     * tail  (bytes 33:N,  chain_config echo)         -- pure echo of the
#              fixture chain config; N is the SSZ-encoded length.
#              On the current pin (v0.6.x) ChainConfig dropped fork /
#              blob-schedule fields, so a normal success result is **69
#              bytes** (tail 33:69; 138 hex chars). Pre-v0.6 layouts were
#              105 bytes; do not revive that figure from older docs.
#                                                                  [gateable]
#     * full  (all N bytes match)                      -- root + succ + tail.
#
#   Variable-length deserialize-failure sentinels are compared byte-for-byte
#   (PASS(malformed) / FAIL[malformed]), not by the three-region split.
#
#   A per-case line shows which regions matched. Any root/tail miss means the
#   pre-execution path disagreed with the fixture (a real SpecRef bug). A
#   succ-only miss is FAIL[succ] unless the fixture is listed in
#   `scripts/eest-succ-allow.txt` (fixture-vs-pinned-spec burndown; goal is
#   an empty file). Allowlisted succ misses print PASS(allow).
#
# Per-case artefacts under the run directory:
#   <label>.specref-result.tsv  -- TWO fields: `OK\t<hex>` or `ERROR\t<reason>`
#     (GH #11746 / PR #11747: NOT `<label>.result.tsv`, which is the guest
#     harness filename. Default schemas are identical in shape, so a name
#     collision would be a silent wrong verdict — distinct names close it.)
#   <label>.output / <label>.log -- raw SpecRef bytes and lake-exe log
#
# Run-dir ownership (GH #11748 / PR #11749):
#   `scripts/lib/eest-run-dir.sh` claims the directory with an `.eest-run-dir`
#   marker naming this harness. Recreates a dir this harness owns (documented
#   behaviour); refuses to delete a dir owned by another harness, a live peer
#   pid, or an unmarked non-empty tree. Shared with the guest harness.
#
# Usage:
#   scripts/eest-specref-check.sh [options]
#     --all              run every stateless block (slow); default: smoke subset
#     --skip N           skip first N selected stateless blocks after filtering
#     --limit N          cap to N guest invocations (default 50)
#     --filter SUBSTR    only fixtures whose relpath contains SUBSTR
#     --min-root N       exit 1 if fewer than N root-region matches
#     --min-tail N       exit 1 if fewer than N tail-region matches
#     --min-succ N       exit 1 if fewer than N succ (verdict) matches
#     --quiet-passes     suppress per-case PASS(full) lines
#     --show-passes      print per-case PASS(full) lines
#     --random           shuffle fixtures before --limit
#     --seed N           integer seed for --random
#     --reverse          process selected fixtures last-to-first
#     --tag TAG          EEST fixture tag (default $EEST_FIXTURE_TAG or $(cat scripts/eest-fixture-tag.txt))
#     --run-dir DIR      use DIR instead of an auto run dir under gen-out/eest-specref-run
#     --no-build         skip `lake build specref-eest-check` (reuse the built exe)
#     -h, --help         show this help
#
# Environment:
#   EEST_FIXTURES_DIR   fixtures root (default gen-out/eest-fixtures/<tag>/fixtures/fixtures)
#   EEST_FIXTURE_TAG    default fixture tag
#   EEST_RUN_DIR        explicit run directory (ownership-guarded; see above)
#
# Exit:
#   0 -- ran to completion; --min-{root,tail,succ} met; no un-allowlisted
#        succ FAIL; and (when no --min-* set) no pre-execution FAIL/ERROR
#   1 -- build/convert failure, no fixtures, a --min-* regression, an
#        un-allowlisted succ FAIL, or a pre-execution disagreement
set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ALL=0
SKIP=0
LIMIT=50
FILTER=""
MIN_ROOT=""
MIN_TAIL=""
QUIET_PASSES="${EEST_QUIET_PASSES:-0}"
TAG="${EEST_FIXTURE_TAG:-$(cat scripts/eest-fixture-tag.txt)}"
NO_BUILD="${EEST_NO_BUILD:-0}"
RUN_DIR_OVERRIDE=""
RANDOM_ORDER="${EEST_RANDOM_ORDER:-0}"
RANDOM_SEED="${EEST_RANDOM_SEED:-}"
REVERSE_ORDER="${EEST_REVERSE_ORDER:-0}"
JOBS="${EEST_JOBS:-auto}"

usage() {
  cat <<'USAGE'
Usage:
  scripts/eest-specref-check.sh [options]

Options:
  --all                    run every stateless block (slow); default: smoke subset
  --skip N                 skip first N selected stateless blocks after filtering
  --limit N                cap to N invocations (default 50)
  --filter SUBSTR          only fixtures whose relpath contains SUBSTR
  --min-root N             exit 1 if fewer than N root-region matches
  --min-tail N             exit 1 if fewer than N tail-region matches
  --min-succ N             exit 1 if fewer than N succ (verdict) matches
  --quiet-passes           suppress per-case PASS(full) lines
  --show-passes            print per-case PASS(full) lines
  --random                 shuffle fixtures before --limit
  --seed N                 integer seed for --random
  --reverse                process selected fixtures last-to-first
  --tag TAG                EEST fixture tag (default $(cat scripts/eest-fixture-tag.txt))
  --run-dir DIR            use DIR instead of an auto run dir
  --no-build               skip lake build (reuse the built exe)
  --jobs N|auto            parallel `lake exe` jobs (default auto, capped at nproc)
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
    --all) ALL=1; shift ;;
    --skip) require_arg "$1" "${2:-}"; SKIP="$2"; shift 2 ;;
    --limit) require_arg "$1" "${2:-}"; LIMIT="$2"; shift 2 ;;
    --filter) require_arg "$1" "${2:-}"; FILTER="$2"; shift 2 ;;
    --min-root) require_arg "$1" "${2:-}"; MIN_ROOT="$2"; shift 2 ;;
    --min-tail) require_arg "$1" "${2:-}"; MIN_TAIL="$2"; shift 2 ;;
    --min-succ) require_arg "$1" "${2:-}"; MIN_SUCC="$2"; shift 2 ;;
    --quiet-passes) QUIET_PASSES=1; shift ;;
    --show-passes) QUIET_PASSES=0; shift ;;
    --random) RANDOM_ORDER=1; shift ;;
    --seed) require_arg "$1" "${2:-}"; RANDOM_SEED="$2"; shift 2 ;;
    --reverse) REVERSE_ORDER=1; shift ;;
    --tag) require_arg "$1" "${2:-}"; TAG="$2"; shift 2 ;;
    --run-dir) require_arg "$1" "${2:-}"; RUN_DIR_OVERRIDE="$2"; shift 2 ;;
    --no-build) NO_BUILD=1; shift ;;
    --jobs) require_arg "$1" "${2:-}"; JOBS="$2"; shift 2 ;;
    *) echo "unknown arg: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if ! [[ "$SKIP" =~ ^[0-9]+$ ]]; then
  echo "--skip must be a nonnegative integer (got: $SKIP)" >&2; exit 1
fi
if ! [[ "$LIMIT" =~ ^[0-9]+$ ]] || [[ "$LIMIT" -lt 1 ]]; then
  echo "--limit must be a positive integer (got: $LIMIT)" >&2; exit 1
fi
if [[ -n "$MIN_ROOT" ]] && { ! [[ "$MIN_ROOT" =~ ^[0-9]+$ ]] || [[ "$MIN_ROOT" -lt 1 ]]; }; then
  echo "--min-root must be a positive integer when set (got: $MIN_ROOT)" >&2; exit 1
fi
if [[ -n "$MIN_TAIL" ]] && { ! [[ "$MIN_TAIL" =~ ^[0-9]+$ ]] || [[ "$MIN_TAIL" -lt 1 ]]; }; then
  echo "--min-tail must be a positive integer when set (got: $MIN_TAIL)" >&2; exit 1
fi
if [[ -n "${MIN_SUCC:-}" && ! "$MIN_SUCC" =~ ^[0-9]+$ ]]; then
  echo "--min-succ must be a positive integer when set (got: $MIN_SUCC)" >&2; exit 1
fi
case "$QUIET_PASSES" in
  1|true|yes) QUIET_PASSES=1 ;;
  *) QUIET_PASSES=0 ;;
esac
if [[ "$RANDOM_ORDER" != "0" && "$RANDOM_ORDER" != "1" ]]; then
  echo "EEST_RANDOM_ORDER must be 0 or 1 (got: $RANDOM_ORDER)" >&2; exit 1
fi
if [[ -n "$RANDOM_SEED" ]] && ! [[ "$RANDOM_SEED" =~ ^[0-9]+$ ]]; then
  echo "--seed must be a nonnegative integer (got: $RANDOM_SEED)" >&2; exit 1
fi
if [[ -n "$RANDOM_SEED" && "$RANDOM_ORDER" -eq 0 ]]; then
  echo "--seed requires --random" >&2; exit 1
fi
if [[ "$REVERSE_ORDER" != "0" && "$REVERSE_ORDER" != "1" ]]; then
  echo "EEST_REVERSE_ORDER must be 0 or 1 (got: $REVERSE_ORDER)" >&2; exit 1
fi
CPUS="$(nproc 2>/dev/null || echo 1)"
if [[ "$JOBS" == "auto" ]]; then
  JOBS="$CPUS"
elif ! [[ "$JOBS" =~ ^[0-9]+$ ]] || [[ "$JOBS" -lt 1 ]]; then
  echo "--jobs must be a positive integer or auto (got: $JOBS)" >&2; exit 1
fi
echo "==> SpecRef EEST conformance check (reference model, no ziskemu, jobs=$JOBS)"

# --- build the Lean exe -----------------------------------------------------
if [[ "$NO_BUILD" -eq 0 ]]; then
  echo "==> lake build specref-eest-check"
  lake build specref-eest-check
else
  echo "==> skipping build (--no-build)"
fi

# --- locate fixtures --------------------------------------------------------
FX="${EEST_FIXTURES_DIR:-$REPO_ROOT/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
if [[ ! -d "$FX" ]]; then
  echo "EEST fixtures not found at: $FX" >&2
  echo "  run: scripts/eest-fetch-fixtures.sh '$TAG'" >&2
  exit 1
fi

mkdir -p gen-out

if [[ -n "${RUN_DIR_OVERRIDE:-}" ]]; then
  RUN_DIR="$RUN_DIR_OVERRIDE"
elif [[ -n "${EEST_RUN_DIR:-}" ]]; then
  RUN_DIR="$EEST_RUN_DIR"
else
  RUN_DIR="$REPO_ROOT/gen-out/eest-specref-run/run-$(date -u +%Y%m%dT%H%M%SZ)-$$"
fi
# GH #11748: this used to be an unconditional `rm -rf "$RUN_DIR"`, which would
# destroy a user-supplied directory and could delete a concurrent run's inputs
# mid-flight. The guard recreates a directory this harness owns (the documented
# behaviour) and refuses to delete anything else.
source "$REPO_ROOT/scripts/lib/eest-run-dir.sh"
if ! eest_prepare_run_dir "$RUN_DIR" "eest-specref-check.sh"; then
  exit 1
fi

# --- convert fixtures -> inputs + manifest (same selection as the guest) -----
conv_args=(--fixtures-dir "$FX" --out-dir "$RUN_DIR")
[[ "$SKIP" != "0" ]] && conv_args+=(--skip "$SKIP")
[[ "$ALL" -eq 0 ]] && conv_args+=(--limit "$LIMIT")
[[ -n "$FILTER" ]] && conv_args+=(--filter "$FILTER")
selection="$([[ $ALL -eq 1 ]] && echo all || echo "limit=$LIMIT")"
[[ "$SKIP" != "0" ]] && selection="$selection, skip=$SKIP"
[[ -n "$FILTER" ]] && selection="$selection, filter=$FILTER"
echo "==> convert fixtures (tag=$TAG, $selection)"
echo "    run dir: $RUN_DIR"
python3 scripts/eest-stateless-to-input.py "${conv_args[@]}"

MANIFEST="$RUN_DIR/manifest.tsv"
[[ -s "$MANIFEST" ]] || { echo "no stateless blocks selected" >&2; exit 1; }
mapfile -t manifestLines < "$MANIFEST"

selectedCount="${#manifestLines[@]}"
declare -A manifestRowByLabel=()
for i in "${!manifestLines[@]}"; do
  IFS=$'\t' read -r label _ <<< "${manifestLines[$i]}"
  manifestRowByLabel["$label"]=$((i + 1))
done

if [[ "$RANDOM_ORDER" -eq 1 ]]; then
  if [[ -z "$RANDOM_SEED" ]]; then
    RANDOM_SEED="$(python3 -c 'import random; print(random.randint(0, 2**31-1))')"
  fi
  echo "==> random order: seed=$RANDOM_SEED"
  mapfile -t manifestLines < <(
    printf '%s\n' "${manifestLines[@]}" | python3 -c "
import sys, random
lines = sys.stdin.read().splitlines()
random.Random(int(sys.argv[1])).shuffle(lines)
print('\n'.join(lines))
" "$RANDOM_SEED"
  )
  selection="$selection, random(seed=$RANDOM_SEED)"
fi

if [[ "$REVERSE_ORDER" -eq 1 ]]; then
  echo "==> reverse order: processing selected fixtures last-to-first"
  reversedLines=()
  for ((i = ${#manifestLines[@]} - 1; i >= 0; i--)); do
    reversedLines+=("${manifestLines[$i]}")
  done
  manifestLines=("${reversedLines[@]}")
  selection="$selection, reverse"
fi

# GH #11308: optional third argument is manifest column 8 = `case_id`, a SHA-256
# over (fixture relpath, full test name, block index, ORIGINAL stateless input
# bytes).  It is a CASE IDENTITY, not a hash of the on-disk input file -- an
# overwritten file still matches its case_id (#11301) -- so it cannot establish
# file integrity.  Printed with an explicit `case_id=` prefix so it cannot be
# misread as a content hash (that misreading cost a false lead on #11362).
case_identity() {
  local label="$1"
  local relpath="$2"
  local case_id="${3:-}"
  local manifest_row="${manifestRowByLabel[$label]:-?}"
  local id="$relpath (label=$label manifest_row=$manifest_row/$selectedCount"
  [[ -n "$case_id" ]] && id="$id case_id=$case_id"
  if [[ "$manifest_row" != "?" ]]; then
    id="$id rerun_skip=$((SKIP + manifest_row - 1)) rerun_limit=1"
  fi
  if [[ "$RANDOM_ORDER" -eq 1 ]]; then
    id="$id random_seed=$RANDOM_SEED"
  fi
  printf '%s)' "$id"
}

# --- run + classify ---------------------------------------------------------
# A normal 69-byte SszStatelessValidationResult on the current pin (v0.6.x:
# ChainConfig lost its fork and blob-schedule fields) decomposes into three
# regions. Pre-v0.6 was 105 bytes — do not hardcode that figure from old docs.
#   root  [0:32]   (hex chars 0..64)   = new_payload_request_root
#   succ  [32]     (hex chars 64..66)  = successful_validation (real elExecute)
#   tail  [33:69]  (hex chars 66..138) = u32 offset + chain_config echo
# Results whose ForkActivation optionals differ from the common
# timestamp-only shape encode to other lengths. Compare those byte-for-byte.
# Un-allowlisted succ divergence is a FAIL (seam is real; see file header).
total=0 err=0 full=0 succ=0 root=0 tail=0 succdiv=0 succfail=0 malformed=0

SUCC_ALLOW_FILE="$REPO_ROOT/scripts/eest-succ-allow.txt"
succ_allowlisted() {
  local label="$1"
  [[ -f "$SUCC_ALLOW_FILE" ]] || return 1
  while IFS= read -r pat; do
    [[ -z "$pat" || "$pat" == \#* ]] && continue
    [[ "$label" == *"$pat"* ]] && return 0
  done < "$SUCC_ALLOW_FILE"
  return 1
}

# Worker: invoke the exe and write a per-case result TSV so the dispatcher
# can run many cases in parallel and the classifier can read them back in
# manifest order. Result schema: "<STATUS>\t<actual_hex|reason>" -- TWO fields.
#
# GH #11746: this file is named "<label>.specref-result.tsv", NOT
# "<label>.result.tsv", which is what codegen-eest-stateless-check.sh writes.
# Both harnesses honour EEST_RUN_DIR and --run-dir, so the two could otherwise
# target one directory under one filename.
#
# ⛔ Why a distinct NAME rather than a field-count check: in the DEFAULT
# configuration the two schemas are IDENTICAL.  Every codegen-eest-stateless-check
# write is TWO fields ("OK\t<hex>", "BUDGET\tsteps:N", "ERROR\t<reason>") except
# the single --specref-oracle path, which writes three.  A collided file is
# therefore indistinguishable in shape from a legitimate one, in BOTH directions,
# so no arity or content check can detect it -- and the guest harness reading a
# SpecRef row would consume SpecRef's output AS THE GUEST'S with no anomaly at
# all: a silent wrong verdict.  Distinct filenames make that impossible instead.
#
# Run-dir ownership (GH #11748 / PR #11749): both harnesses now go through
# `eest_prepare_run_dir` rather than an unconditional `rm -rf`. That closes the
# sequential clobber of a foreign directory; concurrent same-dir runs by two
# harnesses are still refused by the marker (other-harness / live-pid cases).
run_worker() {
  local line="$1"
  local label input expected_hex succ_bit input_len gas_limit relpath case_id
  # Manifest is 8 columns (GH #11308): label input_file expected_hex succ_bit
  # input_len block_gas_limit fixture_relpath case_id.  ALL EIGHT must be named --
  # with seven names the last variable absorbed the remainder, so relpath silently
  # carried "<path>\t<case_id>" and every report printed a bare 64-hex string next
  # to the path that reads as a content hash.  case_id is a CASE IDENTITY over the
  # ORIGINAL input bytes, not a hash of the file on disk.
  # The trailing _rest sink is load-bearing: bash `read` gives the LAST name every
  # remaining field, so without it a future column 9 would corrupt case_id exactly
  # as column 8 corrupted relpath.  _rest is never read.  (Python readers here use
  # positional fields[:7] slices and are already column-count tolerant.)
  IFS=$'\t' read -r label input expected_hex succ_bit input_len gas_limit relpath case_id _rest <<< "$line"
  local out="$RUN_DIR/$label.output"
  local log="$RUN_DIR/$label.log"
  local result="$RUN_DIR/$label.specref-result.tsv"

  if ! lake exe specref-eest-check "$input" "$out" >"$log" 2>&1; then
    printf 'ERROR\tspec\n' > "$result"
    return 0
  fi
  local actual_hex
  actual_hex="$(xxd -p "$out" 2>/dev/null | tr -d '\n' || true)"
  printf 'OK\t%s\n' "$actual_hex" > "$result"
}

wait_for_one_worker() {
  # Workers always write a per-case specref-result.tsv; their exit code is irrelevant
  # (a lake-exe failure is recorded as an ERROR row, not a crash). Swallow it
  # so `set -e` in the dispatcher never aborts on a finished-but-nonzero job.
  wait -n 2>/dev/null || true
}

classify_case() {
  local line="$1"
  local label input expected_hex succ_bit input_len gas_limit relpath case_id
  # Manifest is 8 columns (GH #11308): label input_file expected_hex succ_bit
  # input_len block_gas_limit fixture_relpath case_id.  ALL EIGHT must be named --
  # with seven names the last variable absorbed the remainder, so relpath silently
  # carried "<path>\t<case_id>" and every report printed a bare 64-hex string next
  # to the path that reads as a content hash.  case_id is a CASE IDENTITY over the
  # ORIGINAL input bytes, not a hash of the file on disk.
  # The trailing _rest sink is load-bearing: bash `read` gives the LAST name every
  # remaining field, so without it a future column 9 would corrupt case_id exactly
  # as column 8 corrupted relpath.  _rest is never read.  (Python readers here use
  # positional fields[:7] slices and are already column-count tolerant.)
  IFS=$'\t' read -r label input expected_hex succ_bit input_len gas_limit relpath case_id _rest <<< "$line"
  local result="$RUN_DIR/$label.specref-result.tsv"
  total=$((total + 1))
  if [[ ! -f "$result" ]]; then
    err=$((err + 1))
    echo "  ERROR(missing) $(case_identity "$label" "$relpath" "$case_id")"
    return 0
  fi
  local status actual_hex _extra
  # The _extra sink plus the emptiness check below is the arity half of GH
  # #11746: it catches a file with MORE fields than this schema (which the
  # length gate would report as a confusing FAIL[malformed]).  The FEWER-fields
  # direction is closed by the distinct filename, not here.
  IFS=$'\t' read -r status actual_hex _extra < "$result"
  if [[ -n "$_extra" ]]; then
    err=$((err + 1))
    echo "  ERROR(schema)  $(case_identity "$label" "$relpath" "$case_id") (expected 2 fields in $result, found more: is another harness writing this directory?)"
    return 0
  fi
  if [[ "$status" != "OK" ]]; then
    err=$((err + 1))
    case "$actual_hex" in
      spec) echo "  ERROR(spec)   $(case_identity "$label" "$relpath" "$case_id") (see $RUN_DIR/$label.log)" ;;
      *) echo "  ERROR($actual_hex) $(case_identity "$label" "$relpath" "$case_id")" ;;
    esac
    return 0
  fi

  if [[ "${#expected_hex}" -ne 138 || "${#actual_hex}" -ne 138 ]]; then
    if [[ "$expected_hex" == "$actual_hex" ]]; then
      full=$((full + 1))
      malformed=$((malformed + 1))
      if [[ "$QUIET_PASSES" -eq 0 ]]; then
        echo "  PASS(malformed) $(case_identity "$label" "$relpath" "$case_id")"
      fi
    else
      echo "  FAIL[malformed] $(case_identity "$label" "$relpath" "$case_id")"
      echo "    expected: $expected_hex"
      echo "    actual:   $actual_hex"
      err=$((err + 1))
    fi
    return 0
  fi

  local exp_root="${expected_hex:0:64}"
  local act_root="${actual_hex:0:64}"
  local exp_succ="${expected_hex:64:2}"
  local act_succ="${actual_hex:64:2}"
  local exp_tail="${expected_hex:66:72}"
  local act_tail="${actual_hex:66:72}"

  local r="root" s="succ" t="tail"
  [[ "$exp_root" == "$act_root" ]] || r="----"
  [[ "$exp_succ" == "$act_succ" ]] || s="----"
  [[ "$exp_tail" == "$act_tail" ]] || t="----"

  [[ "$r" == "root" ]] && root=$((root + 1))
  [[ "$t" == "tail" ]] && tail=$((tail + 1))
  # `succ` accounting: only count a succ MATCH when root+tail also match
  # (a spurious succ match on a broken case is meaningless).
  if [[ "$r" == "root" && "$t" == "tail" ]]; then
    if [[ "$s" == "succ" ]]; then
      succ=$((succ + 1))
      full=$((full + 1))
    else
      # succ divergence: a FAIL unless the fixture is in the
      # fixture-vs-pinned-spec allowlist (scripts/eest-succ-allow.txt).
      if succ_allowlisted "$label"; then
        succdiv=$((succdiv + 1))
      else
        succfail=$((succfail + 1))
      fi
    fi
  fi

  # Reporting: root/tail mismatch => pre-execution FAIL. succ-only miss =>
  # FAIL[succ] unless allowlisted (seam is real elExecute; not a placeholder gap).
  if [[ "$r" == "root" && "$t" == "tail" ]]; then
    if [[ "$s" == "succ" ]]; then
      if [[ "$QUIET_PASSES" -eq 0 ]]; then
        echo "  PASS(full)  $(case_identity "$label" "$relpath" "$case_id")"
      fi
    elif succ_allowlisted "$label"; then
      echo "  PASS(allow) $(case_identity "$label" "$relpath" "$case_id") [root/succ(div:fixture-allowlisted)/tail]"
    else
      echo "  FAIL[succ]  $(case_identity "$label" "$relpath" "$case_id")"
      echo "    expected: $expected_hex"
      echo "    actual:   $actual_hex"
    fi
  else
    echo "  FAIL[$r/$s/$t] $(case_identity "$label" "$relpath" "$case_id")"
    echo "    expected: $expected_hex"
    echo "    actual:   $actual_hex"
    err=$((err + 1))
  fi
}

echo "==> run SpecRef on $selectedCount case(s) ($selection, jobs=$JOBS)"
running=0
for line in "${manifestLines[@]}"; do
  run_worker "$line" &
  running=$((running + 1))
  if [[ "$running" -ge "$JOBS" ]]; then
    wait_for_one_worker
    running=$((running - 1))
  fi
done
# Drain remaining workers.
while [[ "$running" -gt 0 ]]; do
  wait_for_one_worker || true
  running=$((running - 1))
done

# Classify in manifest order so the report is stable regardless of completion
# order.
for line in "${manifestLines[@]}"; do
  classify_case "$line"
done

# --- summary ----------------------------------------------------------------
echo
echo "============================================================"
echo " SpecRef EEST conformance summary"
echo "============================================================"
echo "  total cases : $total"
echo "  ERROR/FAIL  : $err    (pre-execution disagreement -- a real SpecRef bug)"
echo "  succ FAIL   : $succfail  (verdict disagreement -- a real SpecRef bug)"
echo "  full match  : $full   (root + succ + tail -- the guest's exact output)"
echo "  root match  : $root   (pre-execution NPR-root hashing)   [gateable]"
echo "  tail match  : $tail   (chain-config echo)                [gateable]"
echo "  succ match  : $succ   (successful_validation; counted only when root+tail also match)"
echo "  succ diverg : $succdiv  (fixture-vs-pinned-spec, allowlisted in eest-succ-allow.txt)"
echo "  malformed   : $malformed  (variable-length failed sentinel; exact-byte match)"
echo "============================================================"

rc=0
if [[ -n "$MIN_ROOT" && "$root" -lt "$MIN_ROOT" ]]; then
  echo "REGRESSION: --min-root $MIN_ROOT not met (root matches = $root)" >&2
  rc=1
fi
if [[ -n "$MIN_TAIL" && "$tail" -lt "$MIN_TAIL" ]]; then
  echo "REGRESSION: --min-tail $MIN_TAIL not met (tail matches = $tail)" >&2
  rc=1
fi
if [[ -n "${MIN_SUCC:-}" && "$succ" -lt "$MIN_SUCC" ]]; then
  echo "REGRESSION: --min-succ $MIN_SUCC not met (succ matches = $succ)" >&2
  rc=1
fi
if [[ "$succfail" -gt 0 ]]; then
  # The seam is real (s1d19): any un-allowlisted succ divergence is a bug.
  rc=1
fi
if [[ "$err" -gt 0 && -z "$MIN_ROOT$MIN_TAIL${MIN_SUCC:-}" ]]; then
  # With no explicit gate, surface pre-execution failures via exit code too.
  rc=1
fi

exit "$rc"
