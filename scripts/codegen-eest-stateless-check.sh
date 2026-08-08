#!/usr/bin/env bash
# codegen-eest-stateless-check.sh -- Run the RISC-V stateless guest against
# the EEST "zkevm" conformance fixtures and report a pass/fail baseline.
#
# Pipeline (end to end):
#   1. build the `stateless_guest` ELF via codegen -> as -> ld;
#   2. convert EEST zkevm fixtures (Amsterdam / Glamsterdam) into guest
#      input blobs + a manifest via scripts/eest-stateless-to-input.py;
#   3. run each guest input on the selected emulator and compare its output
#      against the fixture's recorded `statelessOutputBytes`.
#
# Fixtures come from the release tarball fetched by
# scripts/eest-fetch-fixtures.sh (NOT re-filled locally). zkevm stateless
# fixtures are published from ethereum/execution-specs releases. If a requested
# fixture tag's upstream release/asset has not been published yet, the fetch
# script records `.not-available`; this harness reports that as a neutral skip
# instead of a regression.
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
#   * tail   -- bytes after the success bit match the expected SSZ tail
#               (normally u32 offset + chain_config; shorter for decode failures).
#   * full   -- exact fixture output bytes match (105 bytes for normal Amsterdam outputs; 73 bytes for the deserialize-failure sentinel).
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
#     --steps N          ziskemu max steps (default $EEST_STEPS or 5000000000)
#     --budget-retry-steps N
#                        retry high-gas BUDGET rows at N steps before classifying
#                        them as BUDGET (default $EEST_BUDGET_RETRY_STEPS or 50000000000;
#                        0 disables)
#     --budget-retry-min-gas N
#                        only retry BUDGET rows whose manifest gas_limit is at
#                        least N (default $EEST_BUDGET_RETRY_MIN_GAS or 100000000)
#     --jobs N|auto      parallel guest-emulator jobs (default $EEST_JOBS or auto,
#                        capped by the automatic memory/CPU cap).
#                        Auto per-job budgets are sized for the uncached ELF->ROM
#                        transpile; when the ziskemu ROM cache is detected via the
#                        first-case warmup (see below) they are relaxed and the
#                        job count is recomputed up to the same automatic cap.
#     --max-failures N   stop after N FAIL/ERROR results (default: disabled)
#     --stop-after-failures N
#                        alias for --max-failures
#     --quiet-passes     suppress per-case PASS(full) lines
#     --progress         print a running "N/total processed, eta ..." line as
#                        cases complete. The ETA is extrapolated from elapsed
#                        wall time and the number of rows done so far
#                        (eta = remaining * elapsed / done).
#     --bsr-witness-cap N
#                        experimental: patch the emitted block_state_root
#                        witness cap before relinking (default: guest default)
#     --bsr-bal-cap N
#                        experimental: patch the emitted block_state_root
#                        BAL row cap before relinking (default: guest default)
#     --job-mem-mib N|auto
#                        memory budget per guest-emulator job (default $EEST_JOB_MEM_MIB
#                        or auto). Auto is derived from the selected backend:
#                        stock ziskemu budgets ~7000 MiB/process; patched lowmem
#                        ziskemu budgets 1024 MiB/process; spike defaults to
#                        $EEST_SPIKE_JOB_MEM_MIB or 1024 MiB.
#                        CPU cap uses one core/job on patched ziskemu/spike and
#                        four cores/job on stock ziskemu unless EEST_JOB_CPU_THREADS is set.
#     --min-succ N       exit 1 if fewer than N succ-bit matches (regression gate)
#     --min-full N       exit 1 if fewer than N full (105-byte) matches (regression gate)
#     --min-root N       exit 1 if fewer than N root matches (regression gate)
#     --no-verify-input-parity
#                        skip the default byte-for-byte check that ziskemu -i
#                        inputs unpack to fixture statelessInputBytes
#     --verify-execution-spec-input
#                        decode the same guest-visible bytes through
#                        execution-specs run_stateless_guest's input path
#     --specref-oracle   also run SpecRef on each input and fail on any
#                        byte-for-byte guest↔SpecRef divergence
#     --random           sample individual stateless blocks uniformly before
#                        applying --limit; use a seed to reproduce a sample
#                        and discover failures outside the default first-N fixtures
#     --seed N           integer seed for --random (default: auto-generated and
#                        printed so any discovery run can be exactly reproduced)
#     --reverse          process the selected fixtures last-to-first; use to
#                        surface failures hiding at the tail of the default
#                        first-N selection without shuffling. Applied after
#                        --random when both are given (reverses the shuffle).
#     --tag TAG          EEST fixture tag (default $EEST_FIXTURE_TAG or scripts/eest-fixture-tag.txt)
#     --guest-elf PATH   run PATH instead of building a guest. This is the ONLY
#                        supported way to override the guest, and it implies
#                        --no-build. See "Guest identity" below.
#
# Guest identity (GH #10617):
#   The resolved guest path and its sha256 are echoed at the start of every run
#   and recorded in $RUN_DIR/run-provenance.tsv, so a result can never be
#   silently about a different artifact than the one that was chosen.
#
#   The former `GUEST_ELF` environment override is REMOVED: having it PRESENT in
#   the environment -- even empty, even alongside a correct `--guest-elf` -- is a
#   hard error. It read `USER_GUEST_ELF="${GUEST_ELF:-...}"`, where
#   USER_GUEST_ELF is the script's *internal* name -- so exporting the internal
#   name was silently ignored and ran the default guest with no error and no
#   warning. Three consecutive sweeps reported clean passes on an artifact
#   nobody had chosen, and a 120-row false-reject population was wrongly
#   declared fixed on that evidence. A misspelled *argument* fails loudly; a
#   misspelled *variable* is indistinguishable from not setting one. Removing
#   the mechanism beats promising to remember it.
#
# Environment:
#   EEST_RUN_DIR         explicit conversion/result directory. When unset, each
#                        invocation uses a unique subdirectory under
#                        gen-out/eest-run so concurrent harness runs do not
#                        clobber each other.
#
# Exit:
#   0 -- ran to completion (baseline mode), or all --min-* thresholds met
#   0 -- fixtures not available upstream for TAG yet (neutral skip)
#   1 -- build/convert failure, no fixtures, or a --min-{succ,full,root} regression
set -euo pipefail

# The directory the caller invoked us from, captured BEFORE the cd below so a
# relative `--guest-elf` path resolves against the caller's cwd rather than
# silently against the repo root (GH #10617: a path that resolves somewhere
# unexpected is the same class of bug as an override that is not read at all).
INVOCATION_CWD="$PWD"
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

# ziskemu startup accelerator (options-only; no zisk/ziskemu change required).
# Every `ziskemu --elf` re-runs the full RISC-V->ZisK transpile of the ~447MB
# stateless_guest ELF (~56.7M instructions); that ELF->ROM build dominates
# per-fixture startup. These stock glibc malloc tunables (honored by glibc
# 2.35+) make the transpile's large allocations cheaper: hugetlb madvises the
# multi-GB arenas onto 2MB transparent hugepages (host THP must be
# always/madvise), a single arena avoids per-thread setup, and disabling trim
# keeps the arena warm across fixtures. Measured on stateless_guest.elf
# (ziskemu --elf ... -n 1 -m, ROM-build dominated):
#   stock: wall 53.5s, sys 26.2s, minor-faults 10.0M, maxRSS 24.7GB
#   tuned: wall 34.4s, sys 19.6s, minor-faults  25k,  maxRSS 25.0GB
# => ~36% faster startup, ~400x fewer page faults, maxRSS ~unchanged (OOM-safe).
# Speeds up docker/CI/local runs alike. Respect any caller-provided value.
if [[ -z "${GLIBC_TUNABLES:-}" ]]; then
  export GLIBC_TUNABLES="glibc.malloc.hugetlb=1:glibc.malloc.arena_max=1:glibc.malloc.trim_threshold=-1:glibc.malloc.top_pad=1073741824"
fi
: "${MALLOC_ARENA_MAX:=1}"
export MALLOC_ARENA_MAX

ALL=0
SKIP=0
LIMIT=50
# No default scope: --limit N or --all must be chosen explicitly (see the
# hard error below).  LIMIT keeps a value so the smoke path is unchanged
# once the flag IS passed; LIMIT_SET records whether it was.
LIMIT_SET=0
FILTER=""
# Default step cap. ziskemu stops at the guest's halt, so this only bounds
# runaway/very-large runs; a case that halts earlier consumes only the steps it
# needs. The EIP-8037 state_gas_reservoir max-gas fixture can require more than
# the default on current ziskemu builds, so high-gas BUDGET rows get one larger
# retry before they are reported as budget exhaustion.
# No default backend (GH #10533).  EEST_BACKEND remains an opt-in override
# for scripted callers; what was removed is the fallback when neither the
# flag nor the variable is set.
BACKEND="${EEST_BACKEND:-}"
STEPS="${EEST_STEPS:-5000000000}"
BUDGET_RETRY_STEPS="${EEST_BUDGET_RETRY_STEPS:-50000000000}"
BUDGET_RETRY_MIN_GAS="${EEST_BUDGET_RETRY_MIN_GAS:-100000000}"
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
PROGRESS="${EEST_PROGRESS:-0}"
BSR_WITNESS_CAP="${EEST_BSR_WITNESS_CAP:-}"
BSR_BAL_CAP="${EEST_BSR_BAL_CAP:-}"
MIN_SUCC=""
MIN_FULL=""
MIN_ROOT=""
# GH #11737: a fixture failure must make the RUN fail.  Until this existed the
# script exited 0 with any number of failing rows unless an opt-in --min-*
# threshold happened to be passed, so `harness && echo ok` printed ok on a run
# with 116 of 648 rows failing.  That is the dangerous direction: a tool that
# errors loudly gets fixed, one that reports success gets trusted.  Callers that
# genuinely want the summary regardless of the outcome must say so explicitly.
EXIT_ZERO_ON_FAILURES="${EEST_EXIT_ZERO_ON_FAILURES:-0}"
DEFAULT_TAG="$(tr -d '[:space:]' < scripts/eest-fixture-tag.txt 2>/dev/null || true)"
DEFAULT_TAG="${DEFAULT_TAG:-$(cat scripts/eest-fixture-tag.txt)}"
TAG="${EEST_FIXTURE_TAG:-$DEFAULT_TAG}"
NO_BUILD="${EEST_NO_BUILD:-0}"
# GH #10617: the guest override is a FLAG, never an environment variable.  Both
# the old public name and the old internal name are rejected loudly here rather
# than honoured or ignored -- an ignored override is the most persuasive wrong
# answer available, because its output is exactly what a working setup produces.
#
# Three deliberate choices:
#  * PRESENCE, not a non-empty value (`${var+x}`, not `-n`): an empty export is
#    still someone attempting an override, and deserves the same complaint.
#  * unconditional, even when --guest-elf is also given: a lingering export beside
#    a correct flag is ambiguous about intent, and a stale export in a shell
#    profile or a wrapper is exactly how someone comes to believe a run used an
#    artifact it did not. Failing on presence is unambiguous; precedence is not.
#  * before argument parsing, so no run can begin under an ambiguous guest.
for stale_var in GUEST_ELF USER_GUEST_ELF; do
  if [[ -n "${!stale_var+x}" ]]; then
    echo "error: $stale_var is no longer supported; pass --guest-elf <path> instead (GH #10617)." >&2
    echo "  unset $stale_var and put the path in the flag${!stale_var:+, e.g.: --guest-elf ${!stale_var}}" >&2
    echo "  (the variable was silently ignored in one of its two spellings, which" >&2
    echo "   reported clean passes on the default guest; the flag fails loudly.)" >&2
    exit 1
  fi
done
GUEST_ELF_OVERRIDE=""
VERDICT_DEBUG="${EEST_VERDICT_DEBUG:-1}"
VERDICT_DEBUG_ELF=""
VERIFY_INPUT_PARITY="${EEST_VERIFY_INPUT_PARITY:-1}"
VERIFY_EXECUTION_SPEC_INPUT="${EEST_VERIFY_EXECUTION_SPEC_INPUT:-0}"
SPECREF_ORACLE="${EEST_SPECREF_ORACLE:-0}"
RANDOM_ORDER="${EEST_RANDOM_ORDER:-0}"
RANDOM_SEED="${EEST_RANDOM_SEED:-}"
REVERSE_ORDER="${EEST_REVERSE_ORDER:-0}"
PREFLIGHT_REPORT="${EEST_PREFLIGHT_REPORT:-budget}"
SPIKE_RUN="${SPIKE_RUN:-$REPO_ROOT/scripts/spike/spike_run}"

usage() {
  cat <<'USAGE'
Usage:
  scripts/codegen-eest-stateless-check.sh [options]

Options:
  --all                    run every stateless block (slow); default: smoke subset
  --exit-zero-on-failures  exit 0 even when rows FAIL or ERROR (GH #11737). Default is
                           to exit non-zero, so a failing run cannot read as green.
                           Use only when the summary is wanted regardless of outcome.
  --skip N                 skip first N selected stateless blocks after filtering
  --limit N                cap to N guest invocations (default 50)
  --filter SUBSTR          only fixtures whose relpath contains SUBSTR
  --backend ziskemu|spike  guest emulator backend (default $EEST_BACKEND or ziskemu)
  --steps N                ziskemu max steps (default $EEST_STEPS or 5000000000)
  --budget-retry-steps N   retry high-gas BUDGET rows at N steps before final BUDGET classification (0 disables)
  --budget-retry-min-gas N only retry BUDGET rows with manifest gas_limit >= N
  --jobs N|auto            parallel guest-emulator jobs (default $EEST_JOBS or auto, capped by the automatic memory/CPU cap);
                           per-job budgets relax automatically (up to the same caps)
                           when the ziskemu ROM cache is detected by the first-case warmup
  --max-failures N         stop after N FAIL/ERROR results
  --stop-after-failures N  alias for --max-failures
  --quiet-passes           suppress per-case PASS(full) lines
  --show-passes            print per-case PASS(full) lines, overriding EEST_QUIET_PASSES
  --progress               print "N/total processed, eta ..." as cases complete
                           (ETA extrapolated from elapsed time and rows done)
  --bsr-witness-cap N      experimental: run with a proposed block_state_root witness cap
  --bsr-bal-cap N          experimental: add a lower block_state_root BAL row cap
  --job-mem-mib N|auto     memory budget per ziskemu job
  --min-succ N             exit 1 if fewer than N succ-bit matches
  --min-full N             exit 1 if fewer than N full matches
  --min-root N             exit 1 if fewer than N root matches
  --verify-input-parity    verify guest inputs unpack to statelessInputBytes (default)
  --no-verify-input-parity skip the default input parity check
  --verify-execution-spec-input
                           additionally decode guest bytes via execution-specs
  --specref-oracle         compare every guest output byte-for-byte with SpecRef;
                           classify verdict differences as false-accept/reject
  --tag TAG                EEST fixture tag (default $EEST_FIXTURE_TAG or scripts/eest-fixture-tag.txt)
  --no-build               skip lake build + ELF emit (reuse existing gen-out/stateless_guest.elf)
  --guest-elf PATH         run PATH instead of building a guest (implies --no-build).
                           The ONLY supported guest override; the GUEST_ELF
                           environment variable is removed and is now an error.
                           The resolved path and its sha256 are echoed and
                           recorded in the run's run-provenance.tsv.
  --no-verdict-debug       do not rerun fixed-size verdict probe on succ mismatches
  --random                 after --filter, sample individual stateless blocks
                           uniformly WITHOUT replacement BEFORE --limit
                           (requires --seed)
  --seed N                 integer seed for --random (default: auto-generated and printed)
  --reverse                process the selected fixtures last-to-first (applied after --random)
  --preflight-report MODE  emit decoded 200M resource dimensions: budget (default), always, never
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
    --exit-zero-on-failures) EXIT_ZERO_ON_FAILURES=1; shift ;;
    --all) ALL=1; shift ;;
    --backend) require_arg "$1" "${2:-}"; BACKEND="$2"; shift 2 ;;
    --skip) require_arg "$1" "${2:-}"; SKIP="$2"; shift 2 ;;
    --limit) require_arg "$1" "${2:-}"; LIMIT="$2"; LIMIT_SET=1; shift 2 ;;
    --filter) require_arg "$1" "${2:-}"; FILTER="$2"; shift 2 ;;
    --steps) require_arg "$1" "${2:-}"; STEPS="$2"; shift 2 ;;
    --budget-retry-steps) require_arg "$1" "${2:-}"; BUDGET_RETRY_STEPS="$2"; shift 2 ;;
    --budget-retry-min-gas) require_arg "$1" "${2:-}"; BUDGET_RETRY_MIN_GAS="$2"; shift 2 ;;
    --jobs) require_arg "$1" "${2:-}"; JOBS="$2"; shift 2 ;;
    --max-failures|--stop-after-failures) require_arg "$1" "${2:-}"; MAX_FAILURES="$2"; shift 2 ;;
    --quiet-passes) QUIET_PASSES=1; shift ;;
    --show-passes) QUIET_PASSES=0; shift ;;
    --progress) PROGRESS=1; shift ;;
    --bsr-witness-cap) require_arg "$1" "${2:-}"; BSR_WITNESS_CAP="$2"; shift 2 ;;
    --bsr-bal-cap) require_arg "$1" "${2:-}"; BSR_BAL_CAP="$2"; shift 2 ;;
    --job-mem-mib) require_arg "$1" "${2:-}"; JOB_MEM_MIB="$2"; shift 2 ;;
    --min-succ) require_arg "$1" "${2:-}"; MIN_SUCC="$2"; shift 2 ;;
    --min-full) require_arg "$1" "${2:-}"; MIN_FULL="$2"; shift 2 ;;
    --min-root) require_arg "$1" "${2:-}"; MIN_ROOT="$2"; shift 2 ;;
    --verify-input-parity) VERIFY_INPUT_PARITY=1; shift ;;
    --no-verify-input-parity) VERIFY_INPUT_PARITY=0; shift ;;
    --verify-execution-spec-input) VERIFY_EXECUTION_SPEC_INPUT=1; VERIFY_INPUT_PARITY=1; shift ;;
    --specref-oracle) SPECREF_ORACLE=1; shift ;;
    --tag) require_arg "$1" "${2:-}"; TAG="$2"; shift 2 ;;
    --run-dir) require_arg "$1" "${2:-}"; RUN_DIR_OVERRIDE="$2"; shift 2 ;;
    --no-build) NO_BUILD=1; shift ;;
    --guest-elf) require_arg "$1" "${2:-}"; GUEST_ELF_OVERRIDE="$2"; shift 2 ;;
    --no-verdict-debug) VERDICT_DEBUG=0; shift ;;
    --random) RANDOM_ORDER=1; shift ;;
    --seed) require_arg "$1" "${2:-}"; RANDOM_SEED="$2"; shift 2 ;;
    --reverse) REVERSE_ORDER=1; shift ;;
    --preflight-report) require_arg "$1" "${2:-}"; PREFLIGHT_REPORT="$2"; shift 2 ;;
    *) echo "unknown arg: $1" >&2; usage >&2; exit 1 ;;
  esac
done

MISSING_CHOICE=0

if [[ "$ALL" -eq 0 && "$LIMIT_SET" -eq 0 ]]; then
  MISSING_CHOICE=1
  cat >&2 <<'SCOPE_ERR'
error: a run scope is required (no default).

  --all         the full 26104-case corpus.  Required for a HIGH-BLAST-RADIUS
                change -- a gas constant, a shared helper, anywhere you cannot
                trust path-targeting -- and for re-baselining after main moves.
                Use --backend spike; it is parallel-tolerant.
  --limit N     a subset of N cases.  Use for iteration, and for a FOCUSED run
                on a targeted change: known-failing cases, plus fixtures
                touching the changed path, plus a random control drawn from the
                PASSING set (a focused set built only from known-failing and
                path-touching cases is blind in the OK->FR direction).

Pick deliberately, and state the scope with every number you report.  A subset
run reports honestly over its N cases and reads exactly like a corpus pass, so
an unscoped run is how a 50-case result gets mistaken for a 26104-case one.

(If you invoked a wrapper script rather than this one, add the flag to that
wrapper's own invocation.)
SCOPE_ERR
fi

if [[ -z "$BACKEND" ]]; then
  MISSING_CHOICE=1
  cat >&2 <<'BACKEND_ERR'
error: --backend is required (no default).

  --backend spike     fast verdict-level A/B gate; parallel-tolerant.
                      Use for anything whose observable effect is a verdict or
                      gas outcome, and for full-corpus sweeps (--jobs 30).
  --backend ziskemu   ground-truth oracle. Use to CONFIRM a divergence Spike
                      reported, and for probes needing the real loader or the
                      accelerators. MUST be run serially (--jobs 1): it is
                      memory-hungry and an earlyoom kill presents as a 0-byte
                      log plus a non-zero exit that looks like a real failure.

  If Spike and ziskemu disagree, ziskemu wins.

EEST_BACKEND=spike|ziskemu also works, for scripted callers.

If you reached this from one of the codegen-eest-*-check.sh probes rather than
by running this script directly: those inherited the old silent default and now
have to say what they mean. Pick the backend for what THAT probe measures, and
add the flag to its own invocation. Background: GH #10533, GH #10582.
BACKEND_ERR
fi

if [[ "$MISSING_CHOICE" -eq 1 ]]; then
  exit 1
fi

case "$BACKEND" in
  ziskemu|spike) ;;
  *) echo "--backend/EEST_BACKEND must be ziskemu or spike (got: $BACKEND)" >&2; exit 1 ;;
esac

if [[ -n "$GUEST_ELF_OVERRIDE" ]]; then
  # Resolve against the CALLER's cwd and fail if it is not a readable file.  An
  # override that names a nonexistent path must not fall back to the default
  # guest -- that fallback is the incident this flag replaces.
  [[ "$GUEST_ELF_OVERRIDE" == /* ]] || GUEST_ELF_OVERRIDE="$INVOCATION_CWD/$GUEST_ELF_OVERRIDE"
  if [[ ! -f "$GUEST_ELF_OVERRIDE" ]]; then
    echo "--guest-elf: not a readable file: $GUEST_ELF_OVERRIDE" >&2
    exit 1
  fi
  GUEST_ELF_OVERRIDE="$(cd "$(dirname "$GUEST_ELF_OVERRIDE")" && pwd)/$(basename "$GUEST_ELF_OVERRIDE")"
  # An override supplies the artifact, so building one would either overwrite it
  # or (worse) run a different guest than the one named.
  if [[ "$NO_BUILD" -eq 0 ]]; then
    echo "==> --guest-elf implies --no-build (using the supplied artifact, not building one)"
    NO_BUILD=1
  fi
  if [[ -n "$BSR_WITNESS_CAP" || -n "$BSR_BAL_CAP" ]]; then
    echo "--guest-elf cannot be combined with --bsr-witness-cap/--bsr-bal-cap:" >&2
    echo "  those patch the emitted assembly and relink, which requires a build." >&2
    exit 1
  fi
fi

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
if ! [[ "$STEPS" =~ ^[0-9]+$ ]] || [[ "$STEPS" -lt 1 ]]; then
  echo "--steps/EEST_STEPS must be a positive integer (got: $STEPS)" >&2
  exit 1
fi
if ! [[ "$BUDGET_RETRY_STEPS" =~ ^[0-9]+$ ]]; then
  echo "--budget-retry-steps/EEST_BUDGET_RETRY_STEPS must be a nonnegative integer (got: $BUDGET_RETRY_STEPS)" >&2
  exit 1
fi
if ! [[ "$BUDGET_RETRY_MIN_GAS" =~ ^[0-9]+$ ]]; then
  echo "--budget-retry-min-gas/EEST_BUDGET_RETRY_MIN_GAS must be a nonnegative integer (got: $BUDGET_RETRY_MIN_GAS)" >&2
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
if [[ "$SPECREF_ORACLE" != "0" && "$SPECREF_ORACLE" != "1" ]]; then
  echo "EEST_SPECREF_ORACLE must be 0 or 1 (got: $SPECREF_ORACLE)" >&2
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
if ! [[ "$QUIET_PASSES" =~ ^(0|1|true|false|yes|no)$ ]]; then
  echo "EEST_QUIET_PASSES must be 0/1/true/false/yes/no (got: $QUIET_PASSES)" >&2
  exit 1
fi
case "$QUIET_PASSES" in
  1|true|yes) QUIET_PASSES=1 ;;
  *) QUIET_PASSES=0 ;;
esac
if ! [[ "$PROGRESS" =~ ^(0|1|true|false|yes|no)$ ]]; then
  echo "EEST_PROGRESS must be 0/1/true/false/yes/no (got: $PROGRESS)" >&2
  exit 1
fi
case "$PROGRESS" in
  1|true|yes) PROGRESS=1 ;;
  *) PROGRESS=0 ;;
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
if [[ "$REVERSE_ORDER" != "0" && "$REVERSE_ORDER" != "1" ]]; then
  echo "EEST_REVERSE_ORDER must be 0 or 1 (got: $REVERSE_ORDER)" >&2
  exit 1
fi
case "$PREFLIGHT_REPORT" in
  budget|always|never) ;;
  *) echo "--preflight-report/EEST_PREFLIGHT_REPORT must be budget, always, or never (got: $PREFLIGHT_REPORT)" >&2; exit 1 ;;
esac

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

# --- locate guest emulator --------------------------------------------------
ZISKEMU="${ZISKEMU:-}"
if [[ "$BACKEND" == "ziskemu" ]]; then
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
else
  if [[ ! -x "$SPIKE_RUN" ]]; then
    echo "spike backend requested, but spike_run is not executable: $SPIKE_RUN" >&2
    echo "  build it with: SPIKE_SRC=/path/to/riscv-isa-sim scripts/spike/build.sh" >&2
    exit 1
  fi
fi

# --- pick parallelism based on the guest emulator build ----------------------
# ziskemu's peak RSS is dominated by a fixed allocation built at ELF-load time,
# independent of the program or step budget. A stock build keeps every ROM
# instruction in one flat array indexed from the program base; because the
# embedded float library is linked ~127 MB above the program, that array spans
# the whole gap (~33M entries) and costs ~6.5 GB. A "PATCHED-lowmem" build moves
# the float library into its own array; tiny ELFs measure around 30 MB RSS, while
# the stateless guest measures around 700 MB RSS on real fixtures. We size this
# harness for the stateless workload.
if [[ "$BACKEND" == "ziskemu" ]]; then
  ZISKEMU_VERSION="$($ZISKEMU --version 2>/dev/null || echo unknown)"
  if [[ "$ZISKEMU_VERSION" == *PATCHED-lowmem* ]]; then
    ZISKEMU_FLAVOR="patched-lowmem"
    ZISKEMU_AUTO_JOB_MEM_MIB=1024
    ZISKEMU_AUTO_JOB_CPU_THREADS=1
  else
    ZISKEMU_FLAVOR="stock"
    ZISKEMU_AUTO_JOB_MEM_MIB=7000
    ZISKEMU_AUTO_JOB_CPU_THREADS=4
  fi
else
  ZISKEMU_VERSION="n/a"
  ZISKEMU_FLAVOR="spike"
  ZISKEMU_AUTO_JOB_MEM_MIB="${EEST_SPIKE_JOB_MEM_MIB:-1024}"
  ZISKEMU_AUTO_JOB_CPU_THREADS="${EEST_SPIKE_JOB_CPU_THREADS:-1}"
fi
JOB_MEM_MIB_AUTO=0
JOB_CPU_THREADS_AUTO=0
if [[ "$JOB_MEM_MIB" == "auto" ]]; then
  JOB_MEM_MIB="$ZISKEMU_AUTO_JOB_MEM_MIB"
  JOB_MEM_MIB_AUTO=1
fi
if [[ "$JOB_CPU_THREADS" == "auto" ]]; then
  JOB_CPU_THREADS="$ZISKEMU_AUTO_JOB_CPU_THREADS"
  JOB_CPU_THREADS_AUTO=1
fi

# --- ziskemu ROM cache awareness ---------------------------------------------
# Newer ziskemu builds cache the transpiled compact ROM keyed by the ELF bytes
# under $ZISKEMU_ROM_CACHE (or $XDG_CACHE_HOME/ziskemu, or ~/.cache/ziskemu;
# ZISKEMU_ROM_CACHE=off|0 disables it). A cache hit skips the ELF->ROM
# transpile entirely. Spike does not use this path.
ROM_CACHE_ENABLED=1
ROM_CACHE_DIR=""
case "${ZISKEMU_ROM_CACHE:-}" in
  off|0) ROM_CACHE_ENABLED=0 ;;
  "") ROM_CACHE_DIR="${XDG_CACHE_HOME:-$HOME/.cache}/ziskemu" ;;
  *) ROM_CACHE_DIR="$ZISKEMU_ROM_CACHE" ;;
esac
ZISKEMU_CACHED_JOB_MEM_MIB="${EEST_CACHED_JOB_MEM_MIB:-5500}"
ZISKEMU_CACHED_JOB_CPU_THREADS="${EEST_CACHED_JOB_CPU_THREADS:-1}"
ROM_CACHE_WARMUP_FAST_SECS="${EEST_ROM_CACHE_WARMUP_FAST_SECS:-15}"

compute_job_cap() {
  local mem_avail_kib mem_avail_mib mem_cap ncpu cpu_cap cap
  mem_avail_kib="$(awk '/MemAvailable:/ {print $2}' /proc/meminfo 2>/dev/null || true)"
  if [[ -z "$mem_avail_kib" ]]; then
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
  ncpu="$(nproc 2>/dev/null || sysctl -n hw.logicalcpu 2>/dev/null || echo 1)"
  cpu_cap=$((ncpu / JOB_CPU_THREADS))
  [[ "$cpu_cap" -lt 1 ]] && cpu_cap=1
  cap="$mem_cap"
  [[ "$cpu_cap" -lt "$cap" ]] && cap="$cpu_cap"
  echo "$cap"
}

CPUS="$(nproc 2>/dev/null || echo 1)"
if [[ "$BACKEND" == "ziskemu" && "$JOBS" != "1" ]]; then
  echo "==> WARNING: --backend ziskemu forces --jobs 1 (requested: $JOBS)." >&2
  echo "    ziskemu is memory-hungry; in parallel an earlyoom kill presents as a" >&2
  echo "    0-byte log plus a non-zero exit that looks like a real failure." >&2
  echo "    Use --backend spike if you want parallelism (GH #10533)." >&2
  JOBS=1
fi

JOBS_REQUESTED="$JOBS"
JOB_CAP="$(compute_job_cap)"
if [[ "$JOBS" == "auto" ]]; then
  JOBS="$JOB_CAP"
elif [[ "$JOBS" -gt "$JOB_CAP" ]]; then
  echo "==> requested --jobs $JOBS capped to $JOB_CAP (job_mem=${JOB_MEM_MIB}MiB, reserve=${MEM_RESERVE_MIB}MiB, cpu_threads/job=$JOB_CPU_THREADS); rechecked after ROM-cache warmup" >&2
  JOBS="$JOB_CAP"
fi

recalibrate_jobs_for_rom_cache() {
  local warmup_secs="$1" stamp="$2" cached=0 new_cap
  [[ "$BACKEND" == "ziskemu" ]] || return 0
  [[ "$ROM_CACHE_ENABLED" -eq 1 && -n "$ROM_CACHE_DIR" ]] || return 0
  [[ "$ZISKEMU_FLAVOR" == "stock" ]] || return 0
  [[ "$JOB_MEM_MIB_AUTO" -eq 1 || "$JOB_CPU_THREADS_AUTO" -eq 1 ]] || return 0
  if [[ "$warmup_secs" -lt "$ROM_CACHE_WARMUP_FAST_SECS" ]]; then
    cached=1
  elif [[ -n "$(find "$ROM_CACHE_DIR" -maxdepth 1 -name '*.zisk-rom' -newer "$stamp" -print -quit 2>/dev/null)" ]]; then
    cached=1
  fi
  if [[ "$cached" -ne 1 ]]; then
    echo "==> ROM cache not detected (warmup ${warmup_secs}s, no fresh entry in $ROM_CACHE_DIR); keeping jobs=$JOBS"
    return 0
  fi
  [[ "$JOB_MEM_MIB_AUTO" -eq 1 ]] && JOB_MEM_MIB="$ZISKEMU_CACHED_JOB_MEM_MIB"
  [[ "$JOB_CPU_THREADS_AUTO" -eq 1 ]] && JOB_CPU_THREADS="$ZISKEMU_CACHED_JOB_CPU_THREADS"
  new_cap="$(compute_job_cap)"
  if [[ "$JOBS_REQUESTED" == "auto" ]]; then
    JOBS="$new_cap"
  else
    JOBS="$JOBS_REQUESTED"
    [[ "$JOBS" -gt "$new_cap" ]] && JOBS="$new_cap"
  fi
  echo "==> ROM cache active (warmup ${warmup_secs}s): jobs=$JOBS (job_mem=${JOB_MEM_MIB}MiB, cpu_threads/job=$JOB_CPU_THREADS)"
}

if [[ "$BACKEND" == "ziskemu" ]]; then
  echo "==> backend: ziskemu"
  echo "    ziskemu: $ZISKEMU"
  echo "    version: $ZISKEMU_VERSION"
  echo "    flavor:  $ZISKEMU_FLAVOR (${JOB_MEM_MIB} MiB/proc budget) -> jobs=$JOBS (cpus=$CPUS)"
else
  echo "==> backend: spike"
  echo "    spike_run: $SPIKE_RUN"
  echo "    flavor:    $ZISKEMU_FLAVOR (${JOB_MEM_MIB} MiB/proc budget) -> jobs=$JOBS (cpus=$CPUS)"
fi

# --- locate fixtures --------------------------------------------------------
FX="${EEST_FIXTURES_DIR:-$REPO_ROOT/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
if [[ ! -d "$FX" ]]; then
  unavailable_marker="$REPO_ROOT/gen-out/eest-fixtures/$TAG/.not-available"
  if [[ -f "$unavailable_marker" ]]; then
    echo "EEST fixtures not available for $TAG (upstream release not published yet) -- skipping" >&2
    sed 's/^/  /' "$unavailable_marker" >&2
    exit 0
  fi
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
RESOLVED_GUEST_ELF="$GUEST_PREFIX.elf"

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
  local old_witness="  la t0, bsr_fail_code; sd zero, 0(t0); li t1, 524288; bgtu a2, t1, .Lbsr_cons_change_cap"
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
}

patch_bsr_caps_and_relink() {
  local asm="$GUEST_PREFIX.s"
  local obj="$GUEST_PREFIX.o"
  local elf="$RESOLVED_GUEST_ELF"
  local as_tool ld_tool

  patch_bsr_caps_asm "$asm"

  as_tool="$(resolve_riscv_tool RISCV_AS riscv64-unknown-elf-as riscv64-elf-as)"
  ld_tool="$(resolve_riscv_tool RISCV_LD riscv64-unknown-elf-ld riscv64-elf-ld)"
  "$as_tool" -march=rv64imac -mno-relax -o "$obj" "$asm"
  "$ld_tool" -Ttext=0x80000000 -Tdata=0xa3000000 \
    --section-start=.bss=0xa4000000 \
    --section-start=.sszscratch=0xbf800000 \
    -nostdlib --no-relax -o "$elf" "$obj"
}

if [[ "$NO_BUILD" -eq 0 ]]; then
  build_targets=(codegen)
  [[ "$SPECREF_ORACLE" -eq 1 ]] && build_targets+=(specref-eest-check)
  echo "==> lake build ${build_targets[*]}"
  lake build "${build_targets[@]}"

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
  RESOLVED_GUEST_ELF="${GUEST_ELF_OVERRIDE:-$REPO_ROOT/gen-out/stateless_guest.elf}"
  if [[ ! -f "$RESOLVED_GUEST_ELF" ]]; then
    echo "--no-build requested, but stateless_guest ELF does not exist: $RESOLVED_GUEST_ELF" >&2
    echo "pass --guest-elf /path/to/stateless_guest.elf, or run without --no-build" >&2
    exit 1
  fi
fi

# GH #10617: state the artifact's identity before it is used, and record it in
# the run dir.  This is the property that makes a result self-describing: no
# comparison can silently be about a different guest than the one printed here,
# whatever mechanism supplied it.
GUEST_ELF_SHA256="$(sha256sum "$RESOLVED_GUEST_ELF" | cut -d' ' -f1)"
if [[ -n "$GUEST_ELF_OVERRIDE" ]]; then
  GUEST_ELF_SOURCE="--guest-elf"
elif [[ "$NO_BUILD" -eq 1 ]]; then
  GUEST_ELF_SOURCE="no-build-default"
else
  GUEST_ELF_SOURCE="built"
fi
echo "==> guest ELF: $RESOLVED_GUEST_ELF"
echo "    sha256:    $GUEST_ELF_SHA256  (source: $GUEST_ELF_SOURCE)"
GUEST_PROVENANCE="$RUN_DIR/run-provenance.tsv"
{
  printf '# schema=run-provenance-v1\n'
  printf 'field\tvalue\n'
  printf 'guest_elf\t%s\n' "$RESOLVED_GUEST_ELF"
  printf 'guest_elf_sha256\t%s\n' "$GUEST_ELF_SHA256"
  printf 'guest_elf_source\t%s\n' "$GUEST_ELF_SOURCE"
  printf 'guest_elf_bytes\t%s\n' "$(stat -c %s "$RESOLVED_GUEST_ELF")"
  printf 'backend\t%s\n' "$BACKEND"
  printf 'fixture_tag\t%s\n' "$TAG"
  printf 'repo_head\t%s\n' "$(git -C "$REPO_ROOT" rev-parse HEAD 2>/dev/null || echo unknown)"
  printf 'repo_dirty\t%s\n' "$([[ -n "$(git -C "$REPO_ROOT" status --porcelain 2>/dev/null)" ]] && echo 1 || echo 0)"
  printf 'generated\t%s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
} > "$GUEST_PROVENANCE"
echo "    provenance: $GUEST_PROVENANCE"


run_guest_elf() {
  local elf="$1" input="$2" out="$3" log="$4" steps="$5"
  if [[ "$BACKEND" == "ziskemu" ]]; then
    "$ZISKEMU" -e "$elf" -i "$input" -o "$out" -n "$steps" >"$log" 2>&1 </dev/null
  else
    "$SPIKE_RUN" "$elf" "$input" "$out" >"$log" 2>&1 </dev/null
  fi
}

format_verdict_debug() {
  local out="$1"
  local raw
  # GH #11738: THESE OFFSETS DESCRIBE THE DIAGNOSTIC BUILD'S OUTPUT, NOT THE
  # PRODUCTION GUEST'S.  The two layouts are different and neither is self-
  # describing:
  #   diagnostic : 21 u64 words from +0 -- verdict@+0, bv_fail@+8, ...,
  #                tx_state0@+104, tx_state1@+112, then two 32-byte roots at
  #                +168 (sv_recomputed) and +200 (payload state root).
  #   production : bytes 0:32 are the new_payload_request_root, byte 32 is
  #                successful_validation, and the rest is the SSZ tail.
  # Decoding a PRODUCTION .out at the offsets below yields plausible garbage with
  # no error -- a keccak digest read as `verdict` produced 1841024047515375962
  # while investigating #11306.  The guard below refuses that rather than
  # returning numbers that look like measurements.
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
    block_inc0
    block_inc1
    tx_state0
    tx_state1
    exact_net_status
    exact_net_index
    exact_block_status
    exact_header_gas_used
    exact_expected_gas_used
    receipt1_cumulative
  )
  local -a words=()
  local i value dbg=""

  raw="$(od -An -v -tu8 -N 168 "$out" 2>/dev/null | xargs || true)"
  read -r -a words <<< "$raw"
  # Shape gate (GH #11738).  In the diagnostic layout word[0] is the verdict BIT,
  # so it is 0 or 1.  In a production artefact word[0] is the first 8 bytes of a
  # keccak digest, which exceeds 1 with probability 1 - 2^-63.  Refuse loudly
  # instead of emitting a decode of the wrong shape.
  if [[ -n "${words[0]:-}" && "${words[0]}" =~ ^[0-9]+$ && "${words[0]}" -gt 1 ]]; then
    echo "dbg=[UNDECODABLE: word0=${words[0]} is not a verdict bit (0|1) -- this looks like a PRODUCTION output, whose bytes 0:32 are the new_payload_request_root and byte 32 successful_validation. format_verdict_debug decodes the DIAGNOSTIC build only; see GH #11738]"
    return 0
  fi
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
  if [[ "$(stat -c%s "$out" 2>/dev/null || echo 0)" -ge 376 ]]; then
    raw="$(od -An -v -tu8 -j 344 -N 32 "$out" 2>/dev/null | xargs || true)"
    read -r -a words <<< "$raw"
    local -a simple_transfer_labels=(
      st_status
      st_sender_status
      st_recipient_status
      st_fee_status
    )
    for i in "${!simple_transfer_labels[@]}"; do
      value="${words[$i]:-?}"
      dbg="${dbg:+$dbg }${simple_transfer_labels[$i]}=$value"
    done
  fi
  if [[ "$(stat -c%s "$out" 2>/dev/null || echo 0)" -ge 392 ]]; then
    raw="$(od -An -v -tu8 -j 376 -N 16 "$out" 2>/dev/null | xargs || true)"
    read -r -a words <<< "$raw"
    local -a withdrawals_root_labels=(
      wd_root_status
      wd_root_valid
    )
    for i in "${!withdrawals_root_labels[@]}"; do
      value="${words[$i]:-?}"
      dbg="${dbg:+$dbg }${withdrawals_root_labels[$i]}=$value"
    done
  fi
  if [[ "$(stat -c%s "$out" 2>/dev/null || echo 0)" -ge 408 ]]; then
    raw="$(od -An -v -tu8 -j 392 -N 16 "$out" 2>/dev/null | xargs || true)"
    read -r -a words <<< "$raw"
    local -a tx_root_labels=(
      tx_root_status
      tx_count
    )
    for i in "${!tx_root_labels[@]}"; do
      value="${words[$i]:-?}"
      dbg="${dbg:+$dbg }${tx_root_labels[$i]}=$value"
    done
  fi
  if [[ "$(stat -c%s "$out" 2>/dev/null || echo 0)" -ge 424 ]]; then
    raw="$(od -An -v -tu8 -j 408 -N 16 "$out" 2>/dev/null | xargs || true)"
    read -r -a words <<< "$raw"
    local -a receipts_gate_labels=(
      receipts_shape
      receipts_enforce
    )
    for i in "${!receipts_gate_labels[@]}"; do
      value="${words[$i]:-?}"
      dbg="${dbg:+$dbg }${receipts_gate_labels[$i]}=$value"
    done
  fi
  if [[ "$(stat -c%s "$out" 2>/dev/null || echo 0)" -ge 432 ]]; then
    raw="$(od -An -v -tu8 -j 424 -N 8 "$out" 2>/dev/null | xargs || true)"
    read -r -a words <<< "$raw"
    value="${words[0]:-?}"
    dbg="${dbg:+$dbg }receipts_validator_status=$value"
  fi
  if [[ "$(stat -c%s "$out" 2>/dev/null || echo 0)" -ge 440 ]]; then
    raw="$(od -An -v -tu8 -j 432 -N 8 "$out" 2>/dev/null | xargs || true)"
    read -r -a words <<< "$raw"
    value="${words[0]:-?}"
    dbg="${dbg:+$dbg }receipts_encoder_status=$value"
  fi
  if [[ "$(stat -c%s "$out" 2>/dev/null || echo 0)" -ge 456 ]]; then
    raw="$(od -An -v -tu8 -j 440 -N 16 "$out" 2>/dev/null | xargs || true)"
    read -r -a words <<< "$raw"
    local -a receipts_log_labels=(
      receipt_logs_status
      block_log_overflow
    )
    for i in "${!receipts_log_labels[@]}"; do
      value="${words[$i]:-?}"
      dbg="${dbg:+$dbg }${receipts_log_labels[$i]}=$value"
    done
  fi
  if [[ "$(stat -c%s "$out" 2>/dev/null || echo 0)" -ge 464 ]]; then
    raw="$(od -An -v -tu8 -j 456 -N 8 "$out" 2>/dev/null | xargs || true)"
    read -r -a words <<< "$raw"
    value="${words[0]:-?}"
    dbg="${dbg:+$dbg }dispatch_runtime_status=$value"
  fi
  if [[ "$(stat -c%s "$out" 2>/dev/null || echo 0)" -ge 472 ]]; then
    raw="$(od -An -v -tu8 -j 464 -N 8 "$out" 2>/dev/null | xargs || true)"
    read -r -a words <<< "$raw"
    value="${words[0]:-?}"
    dbg="${dbg:+$dbg }runtime_completeness_status=$value"
  fi
  if [[ "$(stat -c%s "$out" 2>/dev/null || echo 0)" -ge 488 ]]; then
    raw="$(od -An -v -tu8 -j 472 -N 16 "$out" 2>/dev/null | xargs || true)"
    read -r -a words <<< "$raw"
    local -a committed_labels=(
      mtx_committed_overflow
      mtx_committed_count
    )
    for i in "${!committed_labels[@]}"; do
      value="${words[$i]:-?}"
      dbg="${dbg:+$dbg }${committed_labels[$i]}=$value"
    done
  fi
  if [[ "$(stat -c%s "$out" 2>/dev/null || echo 0)" -ge 536 ]]; then
    raw="$(od -An -v -tu8 -j 488 -N 48 "$out" 2>/dev/null | xargs || true)"
    read -r -a words <<< "$raw"
    local -a system_capture_labels=(
      system_capture_status
      system_capture_start
      system_capture_end
      system_capture_rows
      system_capture_old_count
      system_capture_new_count
    )
    for i in "${!system_capture_labels[@]}"; do
      value="${words[$i]:-?}"
      dbg="${dbg:+$dbg }${system_capture_labels[$i]}=$value"
    done
  fi
  if [[ "$(stat -c%s "$out" 2>/dev/null || echo 0)" -ge 672 ]]; then
    raw="$(od -An -v -tu8 -j 536 -N 136 "$out" 2>/dev/null | xargs || true)"
    read -r -a words <<< "$raw"
    local -a witness_lookup_labels=(
      widx_build_status
      widx_build_section_len
      widx_build_count
      widx_enabled
      wlh_lookup_calls
      wlh_indexed_calls
      wlh_indexed_hits
      wlh_indexed_misses
      wlh_linear_calls
      wlh_linear_hits
      wlh_linear_misses
      wlh_linear_iterations
      wlh_linear_last_section_len
      wlh_linear_max_section_len
      svf_codes_len
      svf_headers_len
      svf_headers_count
    )
    for i in "${!witness_lookup_labels[@]}"; do
      value="${words[$i]:-?}"
      dbg="${dbg:+$dbg }${witness_lookup_labels[$i]}=$value"
    done
  fi
  if [[ "$(stat -c%s "$out" 2>/dev/null || echo 0)" -ge 1128 ]]; then
    raw="$(od -An -v -tu8 -j 1032 -N 96 "$out" 2>/dev/null | xargs || true)"
    read -r -a words <<< "$raw"
    local -a witness_code_lookup_labels=(
      wcidx_build_status
      wcidx_build_section_len
      wcidx_build_count
      wcidx_enabled
      wclh_lookup_calls
      wclh_indexed_calls
      wclh_indexed_hits
      wclh_indexed_misses
      wclh_linear_calls
      wclh_linear_hits
      wclh_linear_misses
      wclh_linear_iterations
    )
    for i in "${!witness_code_lookup_labels[@]}"; do
      value="${words[$i]:-?}"
      dbg="${dbg:+$dbg }${witness_code_lookup_labels[$i]}=$value"
    done
  fi
  if [[ "$(stat -c%s "$out" 2>/dev/null || echo 0)" -ge 768 ]]; then
    raw="$(od -An -v -tu8 -j 672 -N 96 "$out" 2>/dev/null | xargs || true)"
    read -r -a words <<< "$raw"
    local -a request_body_labels=(
      request_dstatus
      request_dlen
      request_dbody_cap
      request_log_records_cap
      request_wlen
      request_clen
      request_system_body_cap
      request_er_assembled_len
      request_er_assembled_cap
      request_erh_status
      request_erh_blob_cap
      request_notx_deposit_len
    )
    for i in "${!request_body_labels[@]}"; do
      value="${words[$i]:-?}"
      dbg="${dbg:+$dbg }${request_body_labels[$i]}=$value"
    done
  fi
  if [[ "$(stat -c%s "$out" 2>/dev/null || echo 0)" -ge 896 ]]; then
    raw="$(od -An -v -tu8 -j 768 -N 128 "$out" 2>/dev/null | xargs || true)"
    read -r -a words <<< "$raw"
    local -a mtx_cap_labels=(
      mtx_arena_tx_cap
      mtx_full_200m_tx_cap
      mtx_u64_arena_bytes
      mtx_log_window_bytes
      mtx_skip_list_cap
      mtx_skip_count
      mtx_loop_index
      mtx_sender_count_cap
      mtx_sender_count
      mtx_sender_balance_cap
      mtx_sender_balance_count
      mtx_committed_chunk_cap
      mtx_committed_chunk_bytes
      mtx_nonce_seen_count
      mtx_nonce_seen_cap
      mtx_tx_count
    )
    for i in "${!mtx_cap_labels[@]}"; do
      value="${words[$i]:-?}"
      dbg="${dbg:+$dbg }${mtx_cap_labels[$i]}=$value"
    done
  fi
  if [[ "$(stat -c%s "$out" 2>/dev/null || echo 0)" -ge 1032 ]]; then
    raw="$(od -An -v -tu8 -j 896 -N 136 "$out" 2>/dev/null | xargs || true)"
    read -r -a words <<< "$raw"
    local -a receipt_log_cap_labels=(
      receipt_record_count
      receipt_record_cap
      receipt_records_status
      receipt_append_status
      block_log_count
      block_log_desc_cap
      block_log_data_used
      block_log_data_cap
      logs_rlp_arena_used
      logs_rlp_arena_cap
      logs_rlp_last_len
      receipts_rlp_len
      receipts_rlp_cap
      record_bloom_bytes_used
      record_bloom_bytes_cap
      receipt_logs_status_mirror
      block_log_overflow_mirror
    )
    for i in "${!receipt_log_cap_labels[@]}"; do
      value="${words[$i]:-?}"
      dbg="${dbg:+$dbg }${receipt_log_cap_labels[$i]}=$value"
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
      --section-start=.bss=0xa4000000 \
      --section-start=.sszscratch=0xbf800000 \
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
  if ! run_guest_elf "$VERDICT_DEBUG_ELF" "$input" "$out" "$log" "$STEPS"; then
    echo "verdict_debug_error=exit"
    return 0
  fi
  format_verdict_debug "$out"
}

# --- convert fixtures -> ziskemu inputs + manifest --------------------------
conv_args=(--fixtures-dir "$FX" --out-dir "$RUN_DIR")
[[ "$SKIP" != "0" ]] && conv_args+=(--skip "$SKIP")
[[ "$ALL" -eq 0 ]] && conv_args+=(--limit "$LIMIT")
# GH #10596: the SHUFFLE must happen before the cap, so it belongs in the
# converter. Shuffling here (after conversion) only reordered an already
# truncated manifest.
if [[ "$RANDOM_ORDER" -eq 1 ]]; then
  if [[ -z "$RANDOM_SEED" ]]; then
    RANDOM_SEED="$(python3 -c 'import random; print(random.randint(0, 2**31-1))')"
  fi
  conv_args+=(--random --seed "$RANDOM_SEED")
fi
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
  # The converter sampled individual blocks with this seed; preserve that
  # selected order rather than building a second full permutation merely to
  # alter execution order.
  echo "==> random block selection: seed=$RANDOM_SEED (pass --seed $RANDOM_SEED to reproduce this run)"
  selection="$selection, random-blocks(seed=$RANDOM_SEED)"
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

# GH #11308: the optional third argument is manifest column 8, which is the
# `case_id` -- a SHA-256 over (fixture relpath, full test name, block index,
# ORIGINAL stateless input bytes), written by scripts/eest-stateless-to-input.py.
# It is a CASE IDENTITY, not a hash of the input file on disk: a file overwritten
# after generation still matches its case_id (see #11301), so a case_id match
# does NOT establish file integrity.  It is printed with an explicit `case_id=`
# prefix because an unlabelled 64-hex string beside a path reads as a content
# hash -- that misreading cost a spurious fixture-identity mismatch on #11362.
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

run_case() {
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
  local log="$RUN_DIR/$label.emu.log"
  local result="$RUN_DIR/$label.result.tsv"
  # `run_case` runs in background workers.  `$$` remains the parent shell's
  # PID in those workers, so it races when several cases finish together.
  # `BASHPID` is unique to each worker subshell and keeps the final rename
  # atomic without letting one case publish another case's result.
  local tmp_result="$result.tmp.$BASHPID"
  local actual_hex run_steps

  run_specref_oracle() {
    [[ "$SPECREF_ORACLE" -eq 1 ]] || return 0
    local oracle_out="$RUN_DIR/$label.specref.output"
    local oracle_log="$RUN_DIR/$label.specref.log"
    local oracle_hex
    if ! lake exe specref-eest-check "$input" "$oracle_out" >"$oracle_log" 2>&1; then
      printf 'ERROR\tspecref\n' > "$tmp_result"
      mv "$tmp_result" "$result"
      return 1
    fi
    oracle_hex="$(xxd -p "$oracle_out" 2>/dev/null | tr -d '\n' || true)"
    printf 'OK\t%s\t%s\n' "$actual_hex" "$oracle_hex" > "$tmp_result"
    mv "$tmp_result" "$result"
  }

  run_steps="$STEPS"
  run_emulator_case() {
    local steps="$1"
    local run_log="$2"
    run_guest_elf "$RESOLVED_GUEST_ELF" "$input" "$out" "$run_log" "$steps"
  }

  retry_budget_case() {
    [[ "$BUDGET_RETRY_STEPS" -gt "$run_steps" && "$gas_limit" -ge "$BUDGET_RETRY_MIN_GAS" ]] || return 1
    run_steps="$BUDGET_RETRY_STEPS"
    log="$RUN_DIR/$label.emu.retry-$run_steps.log"
    run_emulator_case "$run_steps" "$log"
  }

  if ! run_emulator_case "$run_steps" "$log"; then
    # Distinguish a --steps budget exhaustion (sha256-heavy merkleization,
    # not a wrong answer) from a genuine error. Non-match => ERROR (no
    # behaviour change vs before this distinction was added).
    if [[ "$BACKEND" == "ziskemu" ]] && grep -qiE "$STEP_LIMIT_RE" "$log" 2>/dev/null; then
      if retry_budget_case; then
        :
      elif [[ "$BACKEND" == "ziskemu" ]] && grep -qiE "$STEP_LIMIT_RE" "$log" 2>/dev/null; then
        printf 'BUDGET\tsteps:%s\n' "$run_steps" > "$tmp_result"
        mv "$tmp_result" "$result"
        return 0
      else
        printf 'ERROR\texit\n' > "$tmp_result"
        mv "$tmp_result" "$result"
        return 0
      fi
    else
      printf 'ERROR\texit\n' > "$tmp_result"
      mv "$tmp_result" "$result"
      return 0
    fi
  fi
  local expected_bytes=$(( ${#expected_hex} / 2 ))
  actual_hex="$(xxd -p -l "$expected_bytes" "$out" 2>/dev/null | tr -d '\n' || true)"
  if [[ "${#actual_hex}" -lt "${#expected_hex}" ]]; then
    # A zero-exit run that produced no valid output but whose log shows the
    # step cap was hit is also a budget exhaustion, not a correctness error.
    if [[ "$BACKEND" == "ziskemu" ]] && grep -qiE "$STEP_LIMIT_RE" "$log" 2>/dev/null; then
      if retry_budget_case; then
        actual_hex="$(xxd -p -l "$expected_bytes" "$out" 2>/dev/null | tr -d '\n' || true)"
        if [[ "${#actual_hex}" -ge "${#expected_hex}" ]]; then
          if [[ "$SPECREF_ORACLE" -eq 1 ]]; then
            run_specref_oracle || true
          else
            printf 'OK\t%s\n' "$actual_hex" > "$tmp_result"
            mv "$tmp_result" "$result"
          fi
          return 0
        fi
      fi
      if [[ "$BACKEND" == "ziskemu" ]] && grep -qiE "$STEP_LIMIT_RE" "$log" 2>/dev/null; then
        printf 'BUDGET\tsteps:%s\n' "$run_steps" > "$tmp_result"
      else
        printf 'ERROR\tshort:%s\n' "${#actual_hex}" > "$tmp_result"
      fi
    else
      printf 'ERROR\tshort:%s\n' "${#actual_hex}" > "$tmp_result"
    fi
    mv "$tmp_result" "$result"
    return 0
  fi
  if [[ "$SPECREF_ORACLE" -eq 1 ]]; then
    run_specref_oracle || true
  else
    printf 'OK\t%s\n' "$actual_hex" > "$tmp_result"
    mv "$tmp_result" "$result"
  fi
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
# Most successful Amsterdam SszStatelessValidationResult values are 105 bytes,
# but execution-specs' deserialize-failure sentinel is 73 bytes. Compare the
# exact fixture-provided length; the region counters below still classify the
# common 105-byte layout where present.
#   root [0:32]   = new_payload_request_root  (hex chars 0..64)
#   succ [32]     = successful_validation     (hex chars 64..66)
#   tail [33:]    = remaining expected SSZ tail (hex 66..)
declare -A classifiedLabels=()
total=0 err=0 full=0 succ=0 root=0 tail=0 fail=0 rod=0 budget=0
oracleMatch=0 oracleDiff=0 guestFalseAccept=0 guestFalseReject=0
# Progress tracking (--progress): RUN_START is stamped just before the run loop;
# lastProgressTotal suppresses duplicate lines when `total` has not advanced.
RUN_START=0
lastProgressTotal=-1

format_duration() {
  local s="$1"
  if ! [[ "$s" =~ ^[0-9]+$ ]]; then printf '?'; return; fi
  local h=$((s / 3600)) m=$(((s % 3600) / 60)) sec=$((s % 60))
  if [[ "$h" -gt 0 ]]; then printf '%dh%02dm%02ds' "$h" "$m" "$sec"
  elif [[ "$m" -gt 0 ]]; then printf '%dm%02ds' "$m" "$sec"
  else printf '%ds' "$sec"; fi
}

# Emit "N/total processed, elapsed ..., eta ..." when --progress is set and the
# processed count has advanced since the last line. ETA is a linear
# extrapolation from rows done so far: remaining * elapsed / done.
print_progress() {
  [[ "$PROGRESS" -eq 1 ]] || return 0
  [[ "$total" -ne "$lastProgressTotal" ]] || return 0
  lastProgressTotal="$total"
  local now elapsed remaining eta_str
  now="$(date +%s)"
  elapsed=$((now - RUN_START))
  remaining=$((selectedCount - total))
  [[ "$remaining" -lt 0 ]] && remaining=0
  if [[ "$total" -le 0 || "$elapsed" -le 0 ]]; then
    eta_str="estimating"
  else
    eta_str="$(format_duration $((remaining * elapsed / total)))"
  fi
  printf '  [progress] %d/%d cases, elapsed %s, eta %s\n' \
    "$total" "$selectedCount" "$(format_duration "$elapsed")" "$eta_str"
}

classify_case_result() {
  local line="$1"
  local require_result="${2:-0}"
  local label input expected_hex succ_bit input_len gas_limit relpath case_id result status actual_hex oracle_hex exp r s t
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
    echo "  ERROR(missing) $(case_identity "$label" "$relpath" "$case_id")"
    return 0
  fi
  classifiedLabels["$label"]=1
  total=$((total + 1))
  # Result schema: TWO fields ("OK\t<hex>", "BUDGET\tsteps:N", "ERROR\t<reason>")
  # on every write except the --specref-oracle path, which appends a third
  # (oracle_hex).  Reading with three names is therefore correct: oracle_hex is
  # empty whenever the oracle is off.
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
  # ⚠️ Reachability, measured rather than assumed: BOTH harnesses run an
  # UNCONDITIONAL `rm -rf "$RUN_DIR"` at startup, including when the directory came
  # from --run-dir or EEST_RUN_DIR.  So two SEQUENTIAL runs against one directory
  # cannot mis-read each other -- the second deletes the first's outputs outright.
  # The mis-read is reachable only when the two run CONCURRENTLY against one
  # directory.  That `rm -rf` race is a separate and larger hazard, NOT addressed
  # here.
  #
  # The _extra sink below catches only a file with MORE fields than this schema,
  # i.e. a future intra-harness schema drift -- the GH #11308 class recurring.
  IFS=$'\t' read -r status actual_hex oracle_hex _extra < "$result"
  if [[ -n "$_extra" ]]; then
    err=$((err + 1))
    echo "  ERROR(schema)  $(case_identity "$label" "$relpath" "$case_id") (expected 3 fields in $result, found more: is another harness writing this directory?)"
    return 0
  fi
  if [[ "$status" == "BUDGET" ]]; then
    # Step-budget exhaustion: counted separately, NOT a correctness failure.
    budget=$((budget + 1))
    echo "  BUDGET(steps) $(case_identity "$label" "$relpath" "$case_id") (${actual_hex#steps:} steps)"
    return 0
  fi
  if [[ "$status" != "OK" ]]; then
    err=$((err + 1))
    case "$actual_hex" in
      exit) echo "  ERROR(exit)   $(case_identity "$label" "$relpath" "$case_id")" ;;
      short:*) echo "  ERROR(short)  $(case_identity "$label" "$relpath" "$case_id") (${actual_hex#short:} hex chars)" ;;
      *) echo "  ERROR($actual_hex) $(case_identity "$label" "$relpath" "$case_id")" ;;
    esac
    return 0
  fi
  if [[ "$SPECREF_ORACLE" -eq 1 ]]; then
    if [[ "$actual_hex" == "$oracle_hex" ]]; then
      oracleMatch=$((oracleMatch + 1))
    else
      oracleDiff=$((oracleDiff + 1))
      local guest_verdict="${actual_hex:64:2}" oracle_verdict="${oracle_hex:64:2}" oracle_class="output"
      if [[ "$guest_verdict" == "01" && "$oracle_verdict" == "00" ]]; then
        guestFalseAccept=$((guestFalseAccept + 1)); oracle_class="guest-false-accept"
      elif [[ "$guest_verdict" == "00" && "$oracle_verdict" == "01" ]]; then
        guestFalseReject=$((guestFalseReject + 1)); oracle_class="guest-false-reject"
      fi
      echo "  ORACLE-DIFF[$oracle_class] $(case_identity "$label" "$relpath" "$case_id") (succ guest=$guest_verdict specref=$oracle_verdict)"
    fi
  fi
  exp="$expected_hex"

  # Per-region matches.
  [[ "${actual_hex:0:64}"   == "${exp:0:64}"   ]] && { root=$((root + 1)); r=root; } || r=----
  [[ "${actual_hex:64:2}"   == "${exp:64:2}"   ]] && { succ=$((succ + 1)); s=succ; } || s=----
  [[ "${actual_hex:66:144}" == "${exp:66:144}" ]] && { tail=$((tail + 1)); t=tail; } || t=----

  if [[ "$actual_hex" == "$exp" ]]; then
    full=$((full + 1))
    [[ "$QUIET_PASSES" -eq 1 ]] || echo "  PASS(full)        $(case_identity "$label" "$relpath" "$case_id")"
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
    echo "  FAIL [$r/$s/$t]  $(case_identity "$label" "$relpath" "$case_id") (succ guest=${actual_hex:64:2} exp=${exp:64:2})$dbg"
  fi
  return 0
}

# Dispatched-but-unclassified cases, keyed by manifest index. Scanning only
# this set after each worker completion keeps the bookkeeping O(jobs) per
# case; the previous full-manifest rescan cost ~5s per completion at ~23k
# selected cases (O(N^2) overall) and serialized the whole run on bash.
declare -A inflightByIdx=()

classify_inflight_results() {
  local i
  for i in "${!inflightByIdx[@]}"; do
    if classify_case_result "${inflightByIdx[$i]}" 0; then
      unset 'inflightByIdx[$i]'
    fi
    if failure_limit_reached; then
      break
    fi
  done
  print_progress
}

classify_missing_results() {
  local line
  for line in "${manifestLines[@]}"; do
    classify_case_result "$line" 1 || true
  done
  print_progress
}

emit_preflight_report() {
  local status_filter="${1:-}"
  local -a report_args=(--manifest "$MANIFEST" --results-dir "$RUN_DIR")
  [[ -n "$status_filter" ]] && report_args+=(--status-only "$status_filter")
  [[ -n "$BSR_WITNESS_CAP" ]] && report_args+=(--bsr-cap "$BSR_WITNESS_CAP")
  [[ -n "$BSR_BAL_CAP" ]] && report_args+=(--bsr-bal-cap "$BSR_BAL_CAP")

  echo "==> EEST 200M resource preflight diagnostics${status_filter:+ ($status_filter rows)}"
  if command -v uv >/dev/null 2>&1 && [[ -d execution-specs ]]; then
    local uv_manifest="$MANIFEST"
    local uv_results="$RUN_DIR"
    [[ "$uv_manifest" = /* ]] || uv_manifest="../$uv_manifest"
    [[ "$uv_results" = /* ]] || uv_results="../$uv_results"
    local -a uv_args=(--manifest "$uv_manifest" --results-dir "$uv_results")
    [[ -n "$status_filter" ]] && uv_args+=(--status-only "$status_filter")
    [[ -n "$BSR_WITNESS_CAP" ]] && uv_args+=(--bsr-cap "$BSR_WITNESS_CAP")
    [[ -n "$BSR_BAL_CAP" ]] && uv_args+=(--bsr-bal-cap "$BSR_BAL_CAP")
    uv run --directory execution-specs --quiet python3 \
      ../scripts/eest-bal-replay-report.py "${uv_args[@]}" || \
      echo "  warn: 200M resource preflight diagnostics failed" >&2
  else
    python3 scripts/eest-bal-replay-report.py "${report_args[@]}" || \
      echo "  warn: 200M resource preflight diagnostics failed" >&2
  fi
}

failure_limit_reached() {
  [[ -n "$MAX_FAILURES" && $((fail + err)) -ge "$MAX_FAILURES" ]]
}

stopEarly=0
worker_fail=0
run_note=""
[[ -n "$MAX_FAILURES" ]] && run_note=", max_failures=$MAX_FAILURES"
echo "==> run stateless_guest on $selectedCount input(s) (backend=$BACKEND, jobs=$JOBS$run_note)"
RUN_START="$(date +%s)"
if [[ "$JOBS" -eq 1 ]]; then
  for line in "${manifestLines[@]}"; do
    run_case "$line"
    classify_case_result "$line" 1
    print_progress
    if failure_limit_reached; then
      stopEarly=1
      break
    fi
  done
else
  # Serial first-case warmup: for ziskemu, populates the ROM cache on a cold start
  # (so the fan-out below never races N concurrent multi-GB transpiles) and
  # detects whether cached-run job budgets apply (see
  # recalibrate_jobs_for_rom_cache). The case is a real one; its result counts.
  romCacheStamp="$RUN_DIR/.rom-cache-stamp"
  touch "$romCacheStamp"
  warmupStart="$(date +%s)"
  run_case "${manifestLines[0]}"
  classify_case_result "${manifestLines[0]}" 1
  print_progress
  recalibrate_jobs_for_rom_cache "$(( $(date +%s) - warmupStart ))" "$romCacheStamp"

  active=0
  nextLine=1
  while [[ "$nextLine" -lt "$selectedCount" || "$active" -gt 0 ]]; do
    while [[ "$nextLine" -lt "$selectedCount" && "$active" -lt "$JOBS" ]]; do
      if failure_limit_reached; then
        break
      fi
      run_case "${manifestLines[$nextLine]}" &
      inflightByIdx[$nextLine]="${manifestLines[$nextLine]}"
      active=$((active + 1))
      nextLine=$((nextLine + 1))
    done

    if failure_limit_reached; then
      stopEarly=1
      cleanup_children
      active=0
      classify_inflight_results
      break
    fi
    if [[ "$active" -eq 0 ]]; then
      break
    fi

    wait_for_one_worker || worker_fail=1
    active=$((active - 1))
    classify_inflight_results
    if failure_limit_reached; then
      stopEarly=1
      cleanup_children
      active=0
      classify_inflight_results
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
if [[ "$PREFLIGHT_REPORT" == "always" ]]; then
  emit_preflight_report
elif [[ "$PREFLIGHT_REPORT" == "budget" && "$budget" -gt 0 ]]; then
  emit_preflight_report BUDGET
fi

ran=$((total - err - budget))
# --- summary + baseline file ------------------------------------------------
BASELINE="$RUN_DIR/eest-baseline.txt"
{
  echo "EEST stateless-guest baseline"
  echo "  generated:   $(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  echo "  fixture tag: $TAG"
  echo "  selection:   $selection"
  echo "  guest elf:   $RESOLVED_GUEST_ELF ($GUEST_ELF_SOURCE)"
  echo "  guest sha256:$GUEST_ELF_SHA256"
  echo "  backend:     $BACKEND"
  if [[ "$BACKEND" == "ziskemu" ]]; then
    echo "  ziskemu:     $ZISKEMU (steps=$STEPS, budget_retry_steps=$BUDGET_RETRY_STEPS, budget_retry_min_gas=$BUDGET_RETRY_MIN_GAS)"
    echo "  zisk build:  $ZISKEMU_FLAVOR -- $ZISKEMU_VERSION"
  else
    echo "  spike_run:   $SPIKE_RUN"
  fi
  echo "  jobs:        $JOBS (cpus=$CPUS, ${JOB_MEM_MIB} MiB/proc budget)"
  echo "  selected:    $selectedCount"
  [[ "$stopEarly" -eq 1 ]] && echo "  stopped:     after $((fail + err)) failure(s) (--max-failures $MAX_FAILURES)"
  echo "  total:       $total"
  echo "  errored:     $err"
  echo "  fail:        $fail"
  echo "  budget:      $budget   (--steps exhausted before halt; NOT a correctness failure)"
  echo "  ran:         $ran"
  echo "  full match:    $full   (exact fixture output bytes)"
  echo "  root match:    $root   (bytes 0:32  = new_payload_request_root)"
  echo "  succ match:    $succ   (byte 32     = successful_validation)"
  echo "  tail match:    $tail   (bytes after successful_validation)"
  echo "  root-only diff:$rod   (succ+tail match; ONLY root differs => 1 field from full)"
  if [[ "$SPECREF_ORACLE" -eq 1 ]]; then
    echo "  oracle match:  $oracleMatch   (exact guest↔SpecRef bytes)"
    echo "  oracle diff:   $oracleDiff"
    echo "    guest false-accept: $guestFalseAccept"
    echo "    guest false-reject: $guestFalseReject"
  fi
} | tee "$BASELINE"

echo "==> wrote baseline: $BASELINE"
# No global "latest baseline" copy.  It was only ever a convenience, and during
# a parallel A/B it is actively wrong: both legs raced to write one file and the
# second writer silently won, so anyone reading gen-out/eest-baseline.txt got
# the other leg's numbers.  The per-run baseline above is the authoritative
# artifact and is already scoped to its own --run-dir.

rc=0
if [[ "$SPECREF_ORACLE" -eq 1 && "$oracleDiff" -gt 0 ]]; then
  echo "==> ORACLE REGRESSION: $oracleDiff guest↔SpecRef divergence(s)" >&2; rc=1
fi
if [[ -n "$MIN_SUCC" && "$succ" -lt "$MIN_SUCC" ]]; then
  echo "==> REGRESSION: succ match $succ < --min-succ $MIN_SUCC" >&2; rc=1
fi
if [[ -n "$MIN_FULL" && "$full" -lt "$MIN_FULL" ]]; then
  echo "==> REGRESSION: full match $full < --min-full $MIN_FULL" >&2; rc=1
fi
if [[ -n "$MIN_ROOT" && "$root" -lt "$MIN_ROOT" ]]; then
  echo "==> REGRESSION: root match $root < --min-root $MIN_ROOT" >&2; rc=1
fi
# GH #11737: fixture failures and infrastructure errors now fail the run.  Both
# counts are reported because they mean different things: `fail` is a guest/
# fixture mismatch, `err` is the harness or emulator not completing a row.
# `budget` is deliberately NOT included -- the summary already labels it "NOT a
# correctness failure".
if [[ "$fail" -gt 0 || "$err" -gt 0 ]]; then
  if [[ "$EXIT_ZERO_ON_FAILURES" -eq 1 ]]; then
    echo "==> $fail fixture failure(s) and $err error(s); exiting 0 because --exit-zero-on-failures was given" >&2
  else
    echo "==> FAILURES: fail=$fail errored=$err of selected=$selectedCount (ran=$ran, full match=$full)" >&2
    echo "    read the summary block above for the verdict; pass --exit-zero-on-failures only if you need the summary regardless of outcome" >&2
    rc=1
  fi
fi
exit $rc
