#!/usr/bin/env bash
# report-fresh-lean.sh -- run a `lake exe` report tool against a FRESHLY
# BUILT module, writing stdout to a file BYTE-EXACTLY (GH #12652).
#
# Problem this solves: under LAKE_ARTIFACT_CACHE mode, `lake exe <tool>`
# can succeed while the executable behind the stdout is STALE — the cache
# satisfies the target without replaying the tool's lean-side messages,
# so the report text reflects an older tree.  A `--write` regen built on
# such output commits the stale figures and exits ZERO, and the follow-up
# `--check` then compares two copies of the same stale text and passes —
# a false green with no signal at any stage.  This bit PR #12649:
# drift-report.sh --write printed "Wrote DRIFT.md", exited 0, and left
# DRIFT.md at the pre-move coverage figure; only a manual VALUE diff
# against the expectation caught it.
#
# Template: scripts/check-axioms.sh (GH #10601) forces
#   LAKE_ARTIFACT_CACHE=false lake build "$WITNESS_MODULE"
# before reading reports, and (a) does not suppress stderr, (b) treats a
# zero-report output as a harness failure rather than an empty success.
# This helper ports the same three mechanisms to the lake-exe report
# consumers (drift-report.sh, progress-report.sh, progress-cockpit.sh).
#
# Usage:
#   source scripts/lib/report-fresh-lean.sh
#   report_fresh_lean <out-file> <lake-exe-args...>
# e.g.
#   report_fresh_lean "$TMP" progress-report drift
# On success the tool's stdout is in <out-file> BYTE-EXACT (a plain file
# redirect — command substitution would strip trailing newlines and
# silently change `--check` diffs), and the tool's stderr has surfaced.
# On any failure the script EXITS NON-ZERO with an actionable message;
# callers need no further error handling.

report_fresh_lean() {
  if [ "$#" -lt 2 ]; then
    echo "report-fresh-lean.sh: internal error: need an output file and at least one lake-exe argument" >&2
    exit 2
  fi
  local __out_file="$1"; shift
  local __module="MainProgress"
  local __raw
  __raw="$(mktemp)"

  # Force the module backing the report tool to be BUILT, not cache-served.
  # The override is local to this invocation; the rest of a developer's
  # build may keep using the artifact cache.
  if ! LAKE_ARTIFACT_CACHE=false lake build "$__module" > "$__raw" 2>&1; then
    echo "report-fresh-lean: 'lake build $__module' failed — output follows:" >&2
    cat "$__raw" >&2
    rm -f "$__raw"
    exit 1
  fi

  # Run the tool with stderr UNSUPPRESSED so an underlying lean/lake
  # failure surfaces instead of being discarded by a caller-side
  # 2>/dev/null (the old failure-hiding shape).  stdout goes through a
  # plain redirect so every byte — including trailing newlines — is
  # preserved for the caller's diff.
  if ! lake exe "$@" > "$__out_file" 2>"$__raw"; then
    echo "report-fresh-lean: 'lake exe $*' failed — stderr follows:" >&2
    cat "$__raw" >&2
    rm -f "$__raw"
    exit 1
  fi
  rm -f "$__raw"

  # Zero-report guard (check-axioms RAW_WITNESS_LINES pattern): an empty
  # or near-empty report is a harness failure, not an empty success.
  # Progress-report emits hundreds of lines even on a tiny registry;
  # single-digit output means the tool is broken.
  local __lines
  __lines="$(grep -c . "$__out_file" || true)"
  if [ "$__lines" -lt 10 ]; then
    echo "report-fresh-lean: 'lake exe $*' produced only $__lines non-empty lines — refusing to trust it as a report (stale or broken tool?)" >&2
    exit 1
  fi
}
