#!/usr/bin/env bash
# codegen-eest-stateless-check.sh -- Run the RISC-V stateless guest against
# the EEST "zkevm" conformance fixtures and report a pass/fail baseline.
#
# Pipeline (end to end):
#   1. build the `stateless_guest` ELF via codegen -> as -> ld;
#   2. convert EEST zkevm fixtures (Amsterdam / Glamsterdam) into ziskemu
#      `-i` inputs + a manifest via scripts/eest-stateless-to-input.py;
#   3. run each guest input on ziskemu and compare its output against the
#      fixture's recorded `statelessOutputBytes`.
#
# Fixtures come from the release tarball fetched by
# scripts/eest-fetch-fixtures.sh (NOT re-filled locally); the EEST repo is
# vendored as the `execution-spec-tests` submodule for provenance.
#
# Conformance metrics reported per run -- the 105-byte
# SszStatelessValidationResult decomposes into three independently
# checkable regions, each reported separately so we can see *where* the
# guest is right, not just full-vs-not:
#   * root   -- bytes 0:32  == expected: new_payload_request_root
#               (computed by the epilogue's SSZ merkle tree from the
#               guest-visible stateless input. Root mismatches now point to
#               a concrete unsupported field/path rather than a blanket
#               "static list roots" limitation.)
#   * succ   -- byte 32     == expected: successful_validation bit.
#   * tail   -- bytes 33:105 == expected: u32 offset (=37) + the 68-byte
#               chain_config (echoed from the input by the encoder).
#   * full   -- all 105 bytes match (root AND succ AND tail).
#   * BUDGET -- the run exhausted the ziskemu --steps budget before halting
#               (e.g. a sha256-heavy NPR-root merkleization). This is NOT a
#               correctness failure (the guest never produced an answer to
#               be wrong about), so it is counted and reported SEPARATELY
#               from ERROR and never folded into fail / the --min-* gates.
#               Detection greps the emulator log against EEST_STEP_LIMIT_RE
#               (override if your ziskemu build phrases it differently); a
#               non-match falls through to ERROR, so this never regresses
#               the existing classification.
#   * ERROR  -- ziskemu nonzero exit / truncated output unrelated to the
#               step budget (e.g. the guest hit an Unimplemented exit).
# A per-FAIL line shows which regions matched, e.g. "[root/----/tail]".
#
# Usage:
#   scripts/codegen-eest-stateless-check.sh [options]
#     --all              run every stateless block (slow); default: smoke subset
#     --skip N           skip first N selected stateless blocks after filtering
#     --limit N          cap to N guest invocations (default 50)
#     --filter SUBSTR    only fixtures whose relpath contains SUBSTR
#     --steps N          ziskemu max steps (default $EEST_STEPS or 1000000000)
#     --jobs N|auto      parallel ziskemu jobs (default $EEST_JOBS or auto)
#     --max-failures N   stop after N FAIL/ERROR results (default: disabled)
#     --stop-after-failures N
#                        alias for --max-failures
#     --quiet-passes     suppress per-case PASS(full) lines
#     --bsr-witness-cap N
#                        experimental: patch the emitted block_state_root
#                        witness cap before relinking (default: guest default)
#     --bsr-bal-cap N
#                        experimental: patch the emitted block_state_root
#                        BAL row cap before relinking (default: guest default)
#     --job-mem-mib N|auto
#                        memory budget per ziskemu job (default $EEST_JOB_MEM_MIB
#                        or auto). Auto is derived from the ziskemu build:
#                        stock builds budget ~7000 MiB/process; patched lowmem
#                        builds advertising PATCHED-lowmem budget 1024 MiB/process
#                        for this stateless guest workload.
#                        CPU cap uses one core/job on patched builds and four
#                        cores/job on stock builds unless EEST_JOB_CPU_THREADS is set.
#     --min-succ N       exit 1 if fewer than N succ-bit matches (regression gate)
#     --min-full N       exit 1 if fewer than N full (105-byte) matches (regression gate)
#     --min-root N       exit 1 if fewer than N root matches (regression gate)
#     --no-verify-input-parity
#                        skip the default byte-for-byte check that ziskemu -i
#                        inputs unpack to fixture statelessInputBytes
#     --verify-execution-spec-input
#                        decode the same guest-visible bytes through
#                        execution-specs run_stateless_guest's input path
#     --random           shuffle fixtures into a random order before applying
#                        --limit; use to sample a different subset on each run
#                        and discover failures outside the default first-N fixtures
#     --seed N           integer seed for --random (default: auto-generated and
#                        printed so any discovery run can be exactly reproduced)
#     --tag TAG          EEST fixture tag (default $EEST_FIXTURE_TAG or zkevm@v0.4.0)
#
# Environment:
#   EEST_RUN_DIR         explicit conversion/result directory. When unset, each
#                        invocation uses a unique subdirectory under
#                        gen-out/eest-run so concurrent harness runs do not
#                        clobber each other.
#
# Exit:
#   0 -- ran to completion (baseline mode), or all --min-* thresholds met
#   1 -- build/convert failure, no fixtures, or a --min-{succ,full,root} regression
set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ALL=0
SKIP=0
LIMIT=50
FILTER=""
# Default step cap. ziskemu stops at the guest's halt, so this only bounds
# runaway/very-large runs. Keep the base harness high enough for current large
# EIP-7934 block-RLP-limit fixtures; normal blocks halt long before this and
# are not slowed.
STEPS="${EEST_STEPS:-1000000000}"
# Case-insensitive ERE matched against the ziskemu log when a run does NOT
# produce a valid 105-byte output, to tell "exhausted the --steps budget"
# (BUDGET, not a correctness failure) apart from a genuine ERROR. Override
# EEST_STEP_LIMIT_RE if your ziskemu build phrases step exhaustion
# differently; a non-match safely falls through to ERROR.
STEP_LIMIT_RE="${EEST_STEP_LIMIT_RE:-(step[s]? limit|maximum steps|max[_ ]*steps|exceeded.*step|step.*exceeded|out of steps|reached.*steps|step budget|EmulationNoCompleted)}"
JOBS="${EEST_JOBS:-auto}"
JOB_MEM_MIB="${EEST_JOB_MEM_MIB:-auto}"
JOB_CPU_THREADS="${EEST_JOB_CPU_THREADS:-auto}"
MEM_RESERVE_MIB="${EEST_MEM_RESERVE_MIB:-4096}"
MAX_FAILURES=""
RUN_DIR_OVERRIDE=""
QUIET_PASSES="${EEST_QUIET_PASSES:-0}"
BSR_WITNESS_CAP="${EEST_BSR_WITNESS_CAP:-}"
BSR_BAL_CAP="${EEST_BSR_BAL_CAP:-}"
MIN_SUCC=""
MIN_FULL=""
MIN_ROOT=""
TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
NO_BUILD="${EEST_NO_BUILD:-0}"
USER_GUEST_ELF="${GUEST_ELF:-}"
VERDICT_DEBUG="${EEST_VERDICT_DEBUG:-1}"
VERDICT_DEBUG_ELF=""
VERIFY_INPUT_PARITY="${EEST_VERIFY_INPUT_PARITY:-1}"
VERIFY_EXECUTION_SPEC_INPUT="${EEST_VERIFY_EXECUTION_SPEC_INPUT:-0}"
RANDOM_ORDER="${EEST_RANDOM_ORDER:-0}"
RANDOM_SEED="${EEST_RANDOM_SEED:-}"

usage() {
  cat <<'USAGE'
Usage:
  scripts/codegen-eest-stateless-check.sh [options]

Options:
  --all                    run every stateless block (slow); default: smoke subset
  --skip N                 skip first N selected stateless blocks after filtering
  --limit N                cap to N guest invocations (default 50)
  --filter SUBSTR          only fixtures whose relpath contains SUBSTR
  --steps N                ziskemu max steps (default $EEST_STEPS or 1000000000)
  --jobs N|auto            parallel ziskemu jobs (default $EEST_JOBS or auto)
  --max-failures N         stop after N FAIL/ERROR results
  --stop-after-failures N  alias for --max-failures
  --quiet-passes           suppress per-case PASS(full) lines
  --show-passes            print per-case PASS(full) lines, overriding EEST_QUIET_PASSES
  --bsr-witness-cap N      experimental: run with a proposed block_state_root witness cap
  --bsr-bal-cap N          experimental: add a lower block_state_root BAL row cap
  --job-mem-mib N|auto     memory budget per ziskemu job
  --min-succ N             exit 1 if fewer than N succ-bit matches
  --min-full N             exit 1 if fewer than N full matches
  --min-root N             exit 1 if fewer than N root matches
  --verify-input-parity    verify ziskemu inputs unpack to statelessInputBytes (default)
  --no-verify-input-parity skip the default ziskemu input parity check
  --verify-execution-spec-input
                           additionally decode guest bytes via execution-specs
  --tag TAG                EEST fixture tag (default $EEST_FIXTURE_TAG or zkevm@v0.4.0)
  --no-build               skip lake build + ELF emit (reuse existing gen-out/stateless_guest.elf)
  --no-verdict-debug       do not rerun fixed-size verdict probe on succ mismatches
  --random                 shuffle fixtures into a random order before --limit; run
                           repeatedly to sample different subsets and seek discoveries
  --seed N                 integer seed for --random (default: auto-generated and printed)
  --run-dir DIR            use DIR instead of gen-out/eest-run (enables parallel invocations)
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
    --steps) require_arg "$1" "${2:-}"; STEPS="$2"; shift 2 ;;
    --jobs) require_arg "$1" "${2:-}"; JOBS="$2"; shift 2 ;;
    --max-failures|--stop-after-failures) require_arg "$1" "${2:-}"; MAX_FAILURES="$2"; shift 2 ;;
    --quiet-passes) QUIET_PASSES=1; shift ;;
    --show-passes) QUIET_PASSES=0; shift ;;
    --bsr-witness-cap) require_arg "$1" "${2:-}"; BSR_WITNESS_CAP="$2"; shift 2 ;;
    --bsr-bal-cap) require_arg "$1" "${2:-}"; BSR_BAL_CAP="$2"; shift 2 ;;
    --job-mem-mib) require_arg "$1" "${2:-}"; JOB_MEM_MIB="$2"; shift 2 ;;
    --min-succ) require_arg "$1" "${2:-}"; MIN_SUCC="$2"; shift 2 ;;
    --min-full) require_arg "$1" "${2:-}"; MIN_FULL="$2"; shift 2 ;;
    --min-root) require_arg "$1" "${2:-}"; MIN_ROOT="$2"; shift 2 ;;
    --verify-input-parity) VERIFY_INPUT_PARITY=1; shift ;;
    --no-verify-input-parity) VERIFY_INPUT_PARITY=0; shift ;;
    --verify-execution-spec-input) VERIFY_EXECUTION_SPEC_INPUT=1; VERIFY_INPUT_PARITY=1; shift ;;
    --tag) require_arg "$1" "${2:-}"; TAG="$2"; shift 2 ;;
    --run-dir) require_arg "$1" "${2:-}"; RUN_DIR_OVERRIDE="$2"; shift 2 ;;
    --no-build) NO_BUILD=1; shift ;;
    --no-verdict-debug) VERDICT_DEBUG=0; shift ;;
    --random) RANDOM_ORDER=1; shift ;;
    --seed) require_arg "$1" "${2:-}"; RANDOM_SEED="$2"; shift 2 ;;
    *) echo "unknown arg: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if ! [[ "$SKIP" =~ ^[0-9]+$ ]]; then
  echo "--skip must be a nonnegative integer (got: $SKIP)" >&2
  exit 1
fi
if [[ "$JOBS" != "auto" ]] && { ! [[ "$JOBS" =~ ^[0-9]+$ ]] || [[ "$JOBS" -lt 1 ]]; }; then
  echo "--jobs must be a positive integer or auto (got: $JOBS)" >&2
  exit 1
fi
if [[ "$JOB_MEM_MIB" != "auto" ]] && { ! [[ "$JOB_MEM_MIB" =~ ^[0-9]+$ ]] || [[ "$JOB_MEM_MIB" -lt 1 ]]; }; then
  echo "--job-mem-mib must be a positive integer or auto (got: $JOB_MEM_MIB)" >&2
  exit 1
fi
if [[ "$JOB_CPU_THREADS" != "auto" ]] && { ! [[ "$JOB_CPU_THREADS" =~ ^[0-9]+$ ]] || [[ "$JOB_CPU_THREADS" -lt 1 ]]; }; then
  echo "EEST_JOB_CPU_THREADS must be a positive integer or auto (got: $JOB_CPU_THREADS)" >&2
  exit 1
fi
if [[ "$VERDICT_DEBUG" != "0" && "$VERDICT_DEBUG" != "1" ]]; then
  echo "EEST_VERDICT_DEBUG must be 0 or 1 (got: $VERDICT_DEBUG)" >&2
  exit 1
fi
if ! [[ "$VERIFY_INPUT_PARITY" =~ ^(0|1|true|false|yes|no)$ ]]; then
  echo "EEST_VERIFY_INPUT_PARITY must be 0/1/true/false/yes/no (got: $VERIFY_INPUT_PARITY)" >&2
  exit 1
fi
case "$VERIFY_INPUT_PARITY" in
  1|true|yes) VERIFY_INPUT_PARITY=1 ;;
  *) VERIFY_INPUT_PARITY=0 ;;
esac
if ! [[ "$VERIFY_EXECUTION_SPEC_INPUT" =~ ^(0|1|true|false|yes|no)$ ]]; then
  echo "EEST_VERIFY_EXECUTION_SPEC_INPUT must be 0/1/true/false/yes/no (got: $VERIFY_EXECUTION_SPEC_INPUT)" >&2
  exit 1
fi
case "$VERIFY_EXECUTION_SPEC_INPUT" in
  1|true|yes) VERIFY_EXECUTION_SPEC_INPUT=1; VERIFY_INPUT_PARITY=1 ;;
  *) VERIFY_EXECUTION_SPEC_INPUT=0 ;;
esac
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
if ! [[ "$QUIET_PASSES" =~ ^(0|1|true|false|yes|no)$ ]]; then
  echo "EEST_QUIET_PASSES must be 0/1/true/false/yes/no (got: $QUIET_PASSES)" >&2
  exit 1
fi
case "$QUIET_PASSES" in
  1|true|yes) QUIET_PASSES=1 ;;
  *) QUIET_PASSES=0 ;;
esac
if ! [[ "$MEM_RESERVE_MIB" =~ ^[0-9]+$ ]]; then
  echo "EEST_MEM_RESERVE_MIB must be a nonnegative integer (got: $MEM_RESERVE_MIB)" >&2
  exit 1
fi
if [[ "$RANDOM_ORDER" != "0" && "$RANDOM_ORDER" != "1" ]]; then
  echo "EEST_RANDOM_ORDER must be 0 or 1 (got: $RANDOM_ORDER)" >&2
  exit 1
fi
if [[ -n "$RANDOM_SEED" ]] && ! [[ "$RANDOM_SEED" =~ ^[0-9]+$ ]]; then
  echo "--seed must be a nonnegative integer (got: $RANDOM_SEED)" >&2
  exit 1
fi
if [[ -n "$RANDOM_SEED" && "$RANDOM_ORDER" -eq 0 ]]; then
  echo "--seed requires --random" >&2
  exit 1
fi

cleanup_children() {
  local pids
  pids="$(jobs -pr || true)"
  if [[ -n "$pids" ]]; then
    # shellcheck disable=SC2086
    kill $pids 2>/dev/null || true
    wait 2>/dev/null || true
  fi
}
trap 'cleanup_children; exit 130' INT TERM HUP

# --- locate ziskemu ---------------------------------------------------------
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

# --- pick parallelism based on the ziskemu build ----------------------------
# ziskemu's peak RSS is dominated by a fixed allocation built at ELF-load time,
# independent of the program or step budget. A stock build keeps every ROM
# instruction in one flat array indexed from the program base; because the
# embedded float library is linked ~127 MB above the program, that array spans
# the whole gap (~33M entries) and costs ~6.5 GB. A "PATCHED-lowmem" build moves
# the float library into its own array; tiny ELFs measure around 30 MB RSS, while
# the stateless guest measures around 700 MB RSS on real fixtures. We size this
# harness for the stateless workload.
ZISKEMU_VERSION="$("$ZISKEMU" --version 2>/dev/null || echo unknown)"
if [[ "$ZISKEMU_VERSION" == *PATCHED-lowmem* ]]; then
  ZISKEMU_FLAVOR="patched-lowmem"
  ZISKEMU_AUTO_JOB_MEM_MIB=1024
  ZISKEMU_AUTO_JOB_CPU_THREADS=1
else
  ZISKEMU_FLAVOR="stock"
  ZISKEMU_AUTO_JOB_MEM_MIB=7000
  ZISKEMU_AUTO_JOB_CPU_THREADS=4
fi
if [[ "$JOB_MEM_MIB" == "auto" ]]; then
  JOB_MEM_MIB="$ZISKEMU_AUTO_JOB_MEM_MIB"
fi
if [[ "$JOB_CPU_THREADS" == "auto" ]]; then
  JOB_CPU_THREADS="$ZISKEMU_AUTO_JOB_CPU_THREADS"
fi

compute_job_cap() {
  local mem_avail_kib mem_avail_mib mem_cap ncpu cpu_cap cap
  # Linux: read MemAvailable from /proc/meminfo
  mem_avail_kib="$(awk '/MemAvailable:/ {print $2}' /proc/meminfo 2>/dev/null || true)"
  if [[ -z "$mem_avail_kib" ]]; then
    # macOS: approximate available memory from vm_stat (pages * page_size / 1024)
    local page_size free_pages speculative inactive
    page_size="$(sysctl -n hw.pagesize 2>/dev/null || echo 4096)"
    free_pages="$(vm_stat 2>/dev/null | awk '/Pages free:/ {gsub(/\./,"",$3); print $3}')"
    speculative="$(vm_stat 2>/dev/null | awk '/Pages speculative:/ {gsub(/\./,"",$3); print $3}')"
    inactive="$(vm_stat 2>/dev/null | awk '/Pages inactive:/ {gsub(/\./,"",$3); print $3}')"
    if [[ -n "$free_pages" ]]; then
      mem_avail_kib=$(( (${free_pages:-0} + ${speculative:-0} + ${inactive:-0}) * page_size / 1024 ))
    fi
  fi
  if [[ -z "$mem_avail_kib" ]]; then
    mem_cap=1
  else
    mem_avail_mib=$((mem_avail_kib / 1024))
    if [[ "$mem_avail_mib" -le "$MEM_RESERVE_MIB" ]]; then
      mem_cap=1
    else
      mem_cap=$(((mem_avail_mib - MEM_RESERVE_MIB) / JOB_MEM_MIB))
      [[ "$mem_cap" -lt 1 ]] && mem_cap=1
    fi
  fi
  # nproc is Linux-specific; fall back to sysctl on macOS
  ncpu="$(nproc 2>/dev/null || sysctl -n hw.logicalcpu 2>/dev/null || echo 1)"
  cpu_cap=$((ncpu / JOB_CPU_THREADS))
  [[ "$cpu_cap" -lt 1 ]] && cpu_cap=1
  cap="$mem_cap"
  [[ "$cpu_cap" -lt "$cap" ]] && cap="$cpu_cap"
  echo "$cap"
}

CPUS="$(nproc 2>/dev/null || echo 1)"
JOB_CAP="$(compute_job_cap)"
if [[ "$JOBS" == "auto" ]]; then
  JOBS="$JOB_CAP"
elif [[ "$JOBS" -gt "$JOB_CAP" ]]; then
  echo "==> requested --jobs $JOBS capped to $JOB_CAP (job_mem=${JOB_MEM_MIB}MiB, reserve=${MEM_RESERVE_MIB}MiB, cpu_threads/job=$JOB_CPU_THREADS)" >&2
  JOBS="$JOB_CAP"
fi

echo "==> ziskemu: $ZISKEMU"
echo "    version: $ZISKEMU_VERSION"
echo "    flavor:  $ZISKEMU_FLAVOR (${JOB_MEM_MIB} MiB/proc budget) -> jobs=$JOBS (cpus=$CPUS)"

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
  RUN_DIR="$REPO_ROOT/gen-out/eest-run/run-$(date -u +%Y%m%dT%H%M%SZ)-$$"
fi
rm -rf "$RUN_DIR"
mkdir -p "$RUN_DIR"
GUEST_PREFIX="$RUN_DIR/stateless_guest"
GUEST_ELF="$GUEST_PREFIX.elf"

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

patch_bsr_caps_asm() {
  local asm="$1"
  local old_witness="  la t0, bsr_fail_code; sd zero, 0(t0); li t1, 262144; bgtu a2, t1, .Lbsr_cons_change_cap"
  local new_witness="  la t0, bsr_fail_code; sd zero, 0(t0); li t1, $BSR_WITNESS_CAP; bgtu a2, t1, .Lbsr_cons_change_cap"
  local old_bal=$'  li t0, 2000; divu t1, a0, t0\n  la t2, bsr_bal_count; ld t6, 0(t2); bgtu t6, t1, .Lbsr_cons_change_cap; add t0, s1, t6; li t1, 500018; bgtu t0, t1, .Lbsr_cons_change_cap'
  local new_bal=$'  li t0, 2000; divu t1, a0, t0\n  la t2, bsr_bal_count; ld t6, 0(t2); bgtu t6, t1, .Lbsr_cons_change_cap; li t1, '"$BSR_BAL_CAP"$'; bgtu t6, t1, .Lbsr_cons_change_cap; add t0, s1, t6; li t1, 500018; bgtu t0, t1, .Lbsr_cons_change_cap'
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
}

patch_bsr_caps_and_relink() {
  local asm="$GUEST_PREFIX.s"
  local obj="$GUEST_PREFIX.o"
  local elf="$GUEST_ELF"
  local as_tool ld_tool

  patch_bsr_caps_asm "$asm"

  as_tool="$(resolve_riscv_tool RISCV_AS riscv64-unknown-elf-as riscv64-elf-as)"
  ld_tool="$(resolve_riscv_tool RISCV_LD riscv64-unknown-elf-ld riscv64-elf-ld)"
  "$as_tool" -march=rv64imac -mno-relax -o "$obj" "$asm"
  "$ld_tool" -Ttext=0x80000000 -Tdata=0xa3000000 \
    --section-start=.sszscratch=0xbf500000 \
    -nostdlib --no-relax -o "$elf" "$obj"
}

if [[ "$NO_BUILD" -eq 0 ]]; then
  echo "==> lake build codegen"
  lake build codegen

  if [[ -n "$BSR_WITNESS_CAP" || -n "$BSR_BAL_CAP" ]]; then
    cap_note=""
    [[ -n "$BSR_WITNESS_CAP" ]] && cap_note="bsr_witness_cap=$BSR_WITNESS_CAP"
    [[ -n "$BSR_BAL_CAP" ]] && cap_note="${cap_note:+$cap_note, }bsr_bal_cap=$BSR_BAL_CAP"
    echo "==> emit stateless_guest assembly (experimental $cap_note)"
    lake exe codegen --program stateless_guest --halt linux93 -o "$GUEST_PREFIX" --asm-only
    patch_bsr_caps_and_relink
  else
    echo "==> emit stateless_guest ELF"
    lake exe codegen --program stateless_guest --halt linux93 -o "$GUEST_PREFIX"
  fi
else
  echo "==> skipping build (--no-build)"
  GUEST_ELF="${USER_GUEST_ELF:-$REPO_ROOT/gen-out/stateless_guest.elf}"
  if [[ ! -f "$GUEST_ELF" ]]; then
    echo "--no-build requested, but stateless_guest ELF does not exist: $GUEST_ELF" >&2
    echo "set GUEST_ELF=/path/to/stateless_guest.elf or run without --no-build" >&2
    exit 1
  fi
fi

format_verdict_debug() {
  local out="$1"
  local raw
  local -a labels=(
    verdict
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
    block_rlp_len
    brr_status
    brr_count
    brr_append
    brr0
    brr1
    brr2
  )
  local -a words=()
  local i value dbg=""

  raw="$(od -An -v -tu8 -N 168 "$out" 2>/dev/null | xargs || true)"
  read -r -a words <<< "$raw"
  for i in "${!labels[@]}"; do
    value="${words[$i]:-?}"
    dbg="${dbg:+$dbg }${labels[$i]}=$value"
  done
  if [[ "$(stat -c%s "$out" 2>/dev/null || echo 0)" -ge 232 ]]; then
    local recomputed_state_root payload_state_root
    recomputed_state_root="$(xxd -p -s 168 -l 32 "$out" 2>/dev/null | tr -d '\n' || true)"
    payload_state_root="$(xxd -p -s 200 -l 32 "$out" 2>/dev/null | tr -d '\n' || true)"
    if [[ -n "$recomputed_state_root" && -n "$payload_state_root" ]]; then
      dbg="$dbg recomputed_state_root=$recomputed_state_root payload_state_root=$payload_state_root"
    fi
  fi
  if [[ "$(stat -c%s "$out" 2>/dev/null || echo 0)" -ge 256 ]]; then
    raw="$(od -An -v -tu8 -j 232 -N 24 "$out" 2>/dev/null | xargs || true)"
    read -r -a words <<< "$raw"
    local -a gas_labels=(
      gas_arena_status
      gas_arena_tx_count
      gas_arena_runtime_count
    )
    for i in "${!gas_labels[@]}"; do
      value="${words[$i]:-?}"
      dbg="${dbg:+$dbg }${gas_labels[$i]}=$value"
    done
  fi
  echo "$dbg"
}

ensure_verdict_debug_probe() {
  local prefix asm obj as_tool ld_tool cap_note
  [[ "$VERDICT_DEBUG" -eq 1 ]] || return 1
  if [[ -n "$VERDICT_DEBUG_ELF" ]]; then
    return 0
  fi
  prefix="$RUN_DIR/zisk_stateless_verdict_v2_debug"
  asm="$prefix.s"
  obj="$prefix.o"
  VERDICT_DEBUG_ELF="$prefix.elf"
  if [[ -n "$BSR_WITNESS_CAP" || -n "$BSR_BAL_CAP" ]]; then
    cap_note=""
    [[ -n "$BSR_WITNESS_CAP" ]] && cap_note="bsr_witness_cap=$BSR_WITNESS_CAP"
    [[ -n "$BSR_BAL_CAP" ]] && cap_note="${cap_note:+$cap_note, }bsr_bal_cap=$BSR_BAL_CAP"
    echo "==> emit verdict debug probe (experimental $cap_note)" >&2
    lake exe codegen --program zisk_stateless_verdict_v2 --halt linux93 -o "$prefix" --asm-only >/dev/null
    patch_bsr_caps_asm "$asm"
    as_tool="$(resolve_riscv_tool RISCV_AS riscv64-unknown-elf-as riscv64-elf-as)"
    ld_tool="$(resolve_riscv_tool RISCV_LD riscv64-unknown-elf-ld riscv64-elf-ld)"
    "$as_tool" -march=rv64imac -mno-relax -o "$obj" "$asm"
    "$ld_tool" -Ttext=0x80000000 -Tdata=0xa3000000 \
      --section-start=.sszscratch=0xbf500000 \
      -nostdlib --no-relax -o "$VERDICT_DEBUG_ELF" "$obj"
  else
    echo "==> emit verdict debug probe" >&2
    lake exe codegen --program zisk_stateless_verdict_v2 --halt linux93 -o "$prefix" >/dev/null
  fi
}

verdict_debug_for_case() {
  local label="$1"
  local input="$2"
  local out="$RUN_DIR/$label.verdict-debug.output"
  local log="$RUN_DIR/$label.verdict-debug.log"
  ensure_verdict_debug_probe || return 0
  if ! "$ZISKEMU" -e "$VERDICT_DEBUG_ELF" -i "$input" -o "$out" \
        -n "$STEPS" >"$log" 2>&1 </dev/null; then
    echo "verdict_debug_error=exit"
    return 0
  fi
  format_verdict_debug "$out"
}

# --- convert fixtures -> ziskemu inputs + manifest --------------------------
conv_args=(--fixtures-dir "$FX" --out-dir "$RUN_DIR")
[[ "$SKIP" != "0" ]] && conv_args+=(--skip "$SKIP")
[[ "$ALL" -eq 0 ]] && conv_args+=(--limit "$LIMIT")
[[ -n "$FILTER" ]] && conv_args+=(--filter "$FILTER")
[[ "$VERIFY_INPUT_PARITY" -eq 1 ]] && conv_args+=(--verify-input-parity)
[[ "$VERIFY_EXECUTION_SPEC_INPUT" -eq 1 ]] && conv_args+=(--verify-execution-spec-input)
selection="$([[ $ALL -eq 1 ]] && echo all || echo "limit=$LIMIT")"
[[ "$SKIP" != "0" ]] && selection="$selection, skip=$SKIP"
[[ -n "$FILTER" ]] && selection="$selection, filter=$FILTER"
[[ "$VERIFY_INPUT_PARITY" -eq 1 ]] && selection="$selection, input-parity"
[[ "$VERIFY_EXECUTION_SPEC_INPUT" -eq 1 ]] && selection="$selection, execution-spec-input"
echo "==> convert fixtures (tag=$TAG, $selection)"
echo "    run dir: $RUN_DIR"
if [[ "$VERIFY_EXECUTION_SPEC_INPUT" -eq 1 ]]; then
  uv run --directory execution-specs --quiet python3 \
    "$REPO_ROOT/scripts/eest-stateless-to-input.py" "${conv_args[@]}"
else
  python3 scripts/eest-stateless-to-input.py "${conv_args[@]}"
fi

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
  echo "==> random order: seed=$RANDOM_SEED (pass --seed $RANDOM_SEED to reproduce this run)"
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

case_identity() {
  local label="$1"
  local relpath="$2"
  local manifest_row="${manifestRowByLabel[$label]:-?}"
  local id="$relpath (label=$label manifest_row=$manifest_row/$selectedCount"
  if [[ "$manifest_row" != "?" ]]; then
    id="$id rerun_skip=$((SKIP + manifest_row - 1)) rerun_limit=1"
  fi
  if [[ "$RANDOM_ORDER" -eq 1 ]]; then
    id="$id random_seed=$RANDOM_SEED"
  fi
  printf '%s)' "$id"
}

run_case() {
  local line="$1"
  local label input expected_hex succ_bit input_len gas_limit relpath
  IFS=$'\t' read -r label input expected_hex succ_bit input_len gas_limit relpath <<< "$line"
  local out="$RUN_DIR/$label.output"
  local log="$RUN_DIR/$label.emu.log"
  local result="$RUN_DIR/$label.result.tsv"
  local tmp_result="$result.tmp.$$"
  local actual_hex

  if ! "$ZISKEMU" -e "$GUEST_ELF" -i "$input" -o "$out" \
        -n "$STEPS" >"$log" 2>&1 </dev/null; then
    # Distinguish a --steps budget exhaustion (sha256-heavy merkleization,
    # not a wrong answer) from a genuine error. Non-match => ERROR (no
    # behaviour change vs before this distinction was added).
    if grep -qiE "$STEP_LIMIT_RE" "$log" 2>/dev/null; then
      printf 'BUDGET\tsteps:%s\n' "$STEPS" > "$tmp_result"
    else
      printf 'ERROR\texit\n' > "$tmp_result"
    fi
    mv "$tmp_result" "$result"
    return 0
  fi
  actual_hex="$(xxd -p -l 105 "$out" 2>/dev/null | tr -d '\n' || true)"
  if [[ "${#actual_hex}" -lt 210 ]]; then
    # A zero-exit run that produced no valid output but whose log shows the
    # step cap was hit is also a budget exhaustion, not a correctness error.
    if grep -qiE "$STEP_LIMIT_RE" "$log" 2>/dev/null; then
      printf 'BUDGET\tsteps:%s\n' "$STEPS" > "$tmp_result"
    else
      printf 'ERROR\tshort:%s\n' "${#actual_hex}" > "$tmp_result"
    fi
    mv "$tmp_result" "$result"
    return 0
  fi
  printf 'OK\t%s\n' "$actual_hex" > "$tmp_result"
  mv "$tmp_result" "$result"
}

wait_for_one_worker() {
  local rc
  set +e
  wait -n
  rc=$?
  set -e
  return "$rc"
}

# --- classify ---------------------------------------------------------------
# The 105-byte SszStatelessValidationResult decomposes into three
# independently-checkable regions, so we report each separately to show
# exactly where the guest stands (not just full-vs-not):
#   root [0:32]   = new_payload_request_root  (hex chars 0..64)
#   succ [32]     = successful_validation     (hex chars 64..66)
#   tail [33:105] = u32 offset (=37) + 68-byte chain_config (hex 66..210)
declare -A classifiedLabels=()
total=0 err=0 full=0 succ=0 root=0 tail=0 fail=0 rod=0 budget=0

classify_case_result() {
  local line="$1"
  local require_result="${2:-0}"
  local label input expected_hex succ_bit input_len gas_limit relpath result status actual_hex exp r s t
  IFS=$'\t' read -r label input expected_hex succ_bit input_len gas_limit relpath <<< "$line"
  if [[ -n "${classifiedLabels[$label]+x}" ]]; then
    return 0
  fi
  result="$RUN_DIR/$label.result.tsv"
  if [[ ! -f "$result" ]]; then
    if [[ "$require_result" -eq 0 ]]; then
      return 1
    fi
    classifiedLabels["$label"]=1
    total=$((total + 1))
    err=$((err + 1))
    echo "  ERROR(missing) $(case_identity "$label" "$relpath")"
    return 0
  fi
  classifiedLabels["$label"]=1
  total=$((total + 1))
  IFS=$'\t' read -r status actual_hex < "$result"
  if [[ "$status" == "BUDGET" ]]; then
    # Step-budget exhaustion: counted separately, NOT a correctness failure.
    budget=$((budget + 1))
    echo "  BUDGET(steps) $(case_identity "$label" "$relpath") (${actual_hex#steps:} steps)"
    return 0
  fi
  if [[ "$status" != "OK" ]]; then
    err=$((err + 1))
    case "$actual_hex" in
      exit) echo "  ERROR(exit)   $(case_identity "$label" "$relpath")" ;;
      short:*) echo "  ERROR(short)  $(case_identity "$label" "$relpath") (${actual_hex#short:} hex chars)" ;;
      *) echo "  ERROR($actual_hex) $(case_identity "$label" "$relpath")" ;;
    esac
    return 0
  fi
  exp="${expected_hex:0:210}"

  # Per-region matches.
  [[ "${actual_hex:0:64}"   == "${exp:0:64}"   ]] && { root=$((root + 1)); r=root; } || r=----
  [[ "${actual_hex:64:2}"   == "${exp:64:2}"   ]] && { succ=$((succ + 1)); s=succ; } || s=----
  [[ "${actual_hex:66:144}" == "${exp:66:144}" ]] && { tail=$((tail + 1)); t=tail; } || t=----

  if [[ "$actual_hex" == "$exp" ]]; then
    full=$((full + 1))
    [[ "$QUIET_PASSES" -eq 1 ]] || echo "  PASS(full)        $(case_identity "$label" "$relpath")"
  else
    fail=$((fail + 1))
    # root-only diff: succ + tail already match, ONLY the 32-byte root
    # differs -- i.e. this block is exactly one field (the NPR root) from
    # a full match. This is the precise "distance to crown jewel" metric.
    [[ "$s" == "succ" && "$t" == "tail" && "$r" == "----" ]] && rod=$((rod + 1))
    local dbg=""
    if [[ "${actual_hex:64:2}" != "${exp:64:2}" ]]; then
      dbg="$(verdict_debug_for_case "$label" "$input")"
      [[ -n "$dbg" ]] && dbg=" dbg=[$dbg]"
    fi
    echo "  FAIL [$r/$s/$t]  $(case_identity "$label" "$relpath") (succ guest=${actual_hex:64:2} exp=${exp:64:2})$dbg"
  fi
  return 0
}

classify_completed_results() {
  local line
  for line in "${manifestLines[@]}"; do
    classify_case_result "$line" 0 || true
    if failure_limit_reached; then
      return 0
    fi
  done
}

classify_missing_results() {
  local line
  for line in "${manifestLines[@]}"; do
    classify_case_result "$line" 1 || true
  done
}

failure_limit_reached() {
  [[ -n "$MAX_FAILURES" && $((fail + err)) -ge "$MAX_FAILURES" ]]
}

stopEarly=0
worker_fail=0
run_note=""
[[ -n "$MAX_FAILURES" ]] && run_note=", max_failures=$MAX_FAILURES"
echo "==> run stateless_guest on $selectedCount input(s) (jobs=$JOBS$run_note)"
if [[ "$JOBS" -eq 1 ]]; then
  for line in "${manifestLines[@]}"; do
    run_case "$line"
    classify_case_result "$line" 1
    if failure_limit_reached; then
      stopEarly=1
      break
    fi
  done
else
  active=0
  nextLine=0
  while [[ "$nextLine" -lt "$selectedCount" || "$active" -gt 0 ]]; do
    while [[ "$nextLine" -lt "$selectedCount" && "$active" -lt "$JOBS" ]]; do
      if failure_limit_reached; then
        break
      fi
      run_case "${manifestLines[$nextLine]}" &
      active=$((active + 1))
      nextLine=$((nextLine + 1))
    done

    if failure_limit_reached; then
      stopEarly=1
      cleanup_children
      active=0
      classify_completed_results
      break
    fi
    if [[ "$active" -eq 0 ]]; then
      break
    fi

    wait_for_one_worker || worker_fail=1
    active=$((active - 1))
    classify_completed_results
    if failure_limit_reached; then
      stopEarly=1
      cleanup_children
      active=0
      classify_completed_results
      break
    fi
  done
  if [[ "$worker_fail" -ne 0 ]]; then
    echo "==> warning: at least one worker exited unexpectedly; classifying available results" >&2
  fi
fi
if [[ "$stopEarly" -eq 0 ]]; then
  classify_missing_results
fi
if [[ "$stopEarly" -eq 1 ]]; then
  echo "==> stopped after $((fail + err)) failure(s) (--max-failures $MAX_FAILURES)"
fi

ran=$((total - err - budget))
# --- summary + baseline file ------------------------------------------------
BASELINE="$RUN_DIR/eest-baseline.txt"
{
  echo "EEST stateless-guest baseline"
  echo "  generated:   $(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  echo "  fixture tag: $TAG"
  echo "  selection:   $selection"
  echo "  ziskemu:     $ZISKEMU (steps=$STEPS)"
  echo "  zisk build:  $ZISKEMU_FLAVOR -- $ZISKEMU_VERSION"
  echo "  jobs:        $JOBS (cpus=$CPUS, ${JOB_MEM_MIB} MiB/proc budget)"
  echo "  selected:    $selectedCount"
  [[ "$stopEarly" -eq 1 ]] && echo "  stopped:     after $((fail + err)) failure(s) (--max-failures $MAX_FAILURES)"
  echo "  total:       $total"
  echo "  errored:     $err"
  echo "  budget:      $budget   (--steps exhausted before halt; NOT a correctness failure)"
  echo "  ran:         $ran"
  echo "  full match:    $full   (all 105 bytes)"
  echo "  root match:    $root   (bytes 0:32  = new_payload_request_root)"
  echo "  succ match:    $succ   (byte 32     = successful_validation)"
  echo "  tail match:    $tail   (bytes 33:105 = offset + chain_config)"
  echo "  root-only diff:$rod   (succ+tail match; ONLY root differs => 1 field from full)"
  echo "  fail:          $fail"
} | tee "$BASELINE"

echo "==> wrote baseline: $BASELINE"
cp "$BASELINE" "$REPO_ROOT/gen-out/eest-baseline.txt"
echo "==> updated latest baseline: $REPO_ROOT/gen-out/eest-baseline.txt"

rc=0
if [[ -n "$MIN_SUCC" && "$succ" -lt "$MIN_SUCC" ]]; then
  echo "==> REGRESSION: succ match $succ < --min-succ $MIN_SUCC" >&2; rc=1
fi
if [[ -n "$MIN_FULL" && "$full" -lt "$MIN_FULL" ]]; then
  echo "==> REGRESSION: full match $full < --min-full $MIN_FULL" >&2; rc=1
fi
if [[ -n "$MIN_ROOT" && "$root" -lt "$MIN_ROOT" ]]; then
  echo "==> REGRESSION: root match $root < --min-root $MIN_ROOT" >&2; rc=1
fi
exit $rc
