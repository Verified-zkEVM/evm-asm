#!/usr/bin/env bash
#
# check-no-warnings.sh — fail when `lake build` emits warnings on files
# under EvmAsm/.
#
# Why: warnings (e.g. linter.unusedSimpArgs, unused-variable) tend to
# silently accumulate. The repo policy in evm-asm-4bv is "zero warnings
# from EvmAsm/ source paths"; this script enforces that policy in CI so
# warnings don't drift back. See AGENTS.md and the closed task
# evm-asm-4bv (cleanup) / evm-asm-1hz (this CI check).
#
# Out of scope: warnings emitted by upstream dependencies under
# .lake/packages/, including the LeanRV64D Sail-generated spec, are
# ignored (we cannot fix those here).
#
# Usage:
#   scripts/check-no-warnings.sh             # build fresh, then check
#   scripts/check-no-warnings.sh <log-file>  # check an existing build log
#   scripts/check-no-warnings.sh --report    # print all warnings, exit 0
#
# When invoked with no arguments, this runs `lake build` and captures
# its output. CI generally prefers passing a pre-captured log so the
# build-cache step can be reused (see .github/workflows/build.yml).
#
# POSIX/bash, no external deps beyond grep/awk/mktemp.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

mode="enforce"
log_file=""
cleanup_log=0

for arg in "$@"; do
  case "$arg" in
    --report)
      mode="report"
      ;;
    -*)
      echo "check-no-warnings.sh: unknown option: $arg" >&2
      exit 2
      ;;
    *)
      if [[ -n "$log_file" ]]; then
        echo "check-no-warnings.sh: multiple log files specified" >&2
        exit 2
      fi
      log_file="$arg"
      ;;
  esac
done

if [[ -z "$log_file" ]]; then
  log_file="$(mktemp -t evm-asm-build.XXXXXX.log)"
  cleanup_log=1
  echo "check-no-warnings.sh: running 'lake build' (capturing to $log_file)..." >&2
  # We want to keep going even if lake build fails so we still report
  # the warnings — but we must propagate the build failure as the final
  # exit code if it happened, since a failed build may produce spurious
  # or missing warning output.
  set +e
  lake build 2>&1 | tee "$log_file"
  build_status=${PIPESTATUS[0]}
  set -e
  if (( build_status != 0 )); then
    echo "check-no-warnings.sh: lake build exited $build_status; not analyzing warnings." >&2
    [[ $cleanup_log == 1 ]] && rm -f "$log_file"
    exit "$build_status"
  fi
fi

if [[ ! -f "$log_file" ]]; then
  echo "check-no-warnings.sh: log file not found: $log_file" >&2
  exit 2
fi

# Lean warning lines look like:
#   warning: ./EvmAsm/.../Foo.lean:123:4: <message>
#   ./EvmAsm/.../Foo.lean:123:4: warning: <message>
# We accept both shapes. Filter to lines that mention an EvmAsm/ path
# (anchored to the start of the path component, so "EvmAsm/" appearing
# inside a longer path under .lake/packages/ is excluded).
warnings=$(
  awk '
    # Path-prefixed form: "EvmAsm/...:line:col: warning:" or
    # "./EvmAsm/...:line:col: warning:".
    /^(\.\/)?EvmAsm\/[^:]+\.lean:[0-9]+:[0-9]+: warning:/ { print; next }
    # Lean prefix form: "warning: EvmAsm/...:line:col:" or
    # "warning: ./EvmAsm/...:line:col:".
    /^warning: (\.\/)?EvmAsm\/[^:]+\.lean:[0-9]+:[0-9]+:/ { print; next }
  ' "$log_file" || true
)

count=0
if [[ -n "$warnings" ]]; then
  count=$(printf '%s\n' "$warnings" | wc -l | tr -d ' ')
fi

if [[ "$mode" == "report" ]]; then
  if (( count == 0 )); then
    echo "check-no-warnings.sh: no warnings under EvmAsm/."
  else
    printf '%d warning(s) under EvmAsm/:\n' "$count"
    printf '%s\n' "$warnings"
  fi
  [[ $cleanup_log == 1 ]] && rm -f "$log_file"
  exit 0
fi

if (( count > 0 )); then
  cat >&2 <<EOF

==================================================================
check-no-warnings.sh failed: ${count} warning(s) under EvmAsm/.

EOF
  printf '%s\n' "$warnings" >&2
  cat >&2 <<'EOF'

Repo policy: zero warnings from files under EvmAsm/. Do NOT silence
these — fix the underlying issue. See AGENTS.md and the closed beads
task evm-asm-4bv for guidance:

  - linter.unusedSimpArgs: remove the unused lemma names from the
    simp/simp_all call list (don't disable the linter).
  - unused variable: remove the unused parameter from the signature
    AND fix call sites (don't rename to _x to silence).
  - If a warning resists clean removal, restructure the proof
    (split into a `have`, tighten `simp only [...]`, or move to
    a `rw [...]` step) rather than silencing it.

This guard only inspects EvmAsm/ paths; warnings from upstream
dependencies (LeanRV64D, Sail, mathlib) are out of scope.
==================================================================
EOF
  [[ $cleanup_log == 1 ]] && rm -f "$log_file"
  exit 1
fi

[[ $cleanup_log == 1 ]] && rm -f "$log_file"
echo "check-no-warnings.sh: 0 warnings under EvmAsm/."
