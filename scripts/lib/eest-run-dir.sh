#!/usr/bin/env bash
# Shared ownership guard for EEST harness run directories -- GH #11748.
#
# Both EEST harnesses used to run an UNCONDITIONAL `rm -rf "$RUN_DIR"` at
# startup, including when the directory came from --run-dir or EEST_RUN_DIR.
# Two consequences, both silent in the way that matters -- the deleting run
# proceeds normally and reports its own results, while the damage lands
# somewhere else:
#
#   * pointing a harness at a directory containing anything else destroys it;
#   * a concurrent run deletes the other run's inputs mid-flight.
#
# The category is the one this repo keeps meeting: SAFE BY CONVENTION, NOT BY
# CONSTRUCTION.  Nothing in the code prevented either case; only the current
# call pattern did.
#
# The guard here converts that to safe-by-construction by recording ownership in
# a marker file and refusing to delete anything this harness did not create.
#
# ⚠️ The clean-slate semantics are PRESERVED deliberately and must stay.
# docs/eest-stateless-testing.md documents that an EEST_RUN_DIR "is recreated at
# the start of the invocation", and the A/B workflow in docs/sasm-howto.md
# reuses one directory per leg across runs.  Partial cleaning would be worse
# than either extreme: leftover `<label>.result.tsv` files from an earlier,
# larger selection are counted by eest-run-monitor.sh (which globs
# `*.result.tsv`) and joined by the report scripts, so a half-cleaned directory
# turns a loud destructive bug into a silent measurement one.

EEST_RUN_DIR_MARKER=".eest-run-dir"

# eest_prepare_run_dir <dir> <owner>
#
# Ensures <dir> exists and is a clean, owned run directory, or fails without
# deleting anything.  <owner> is a stable harness identifier, e.g. the script
# basename.  Returns non-zero (and prints to stderr) rather than exiting, so the
# caller decides how to fail.
eest_prepare_run_dir() {
  local dir="$1"
  local owner="$2"
  local marker="$dir/$EEST_RUN_DIR_MARKER"

  if [[ -z "$dir" || -z "$owner" ]]; then
    echo "eest_prepare_run_dir: internal error: dir and owner are required" >&2
    return 1
  fi

  # Never created, nothing to destroy: make it and claim it.
  if [[ ! -e "$dir" ]]; then
    mkdir -p "$dir" || return 1
    _eest_write_marker "$marker" "$owner"
    return 0
  fi

  if [[ ! -d "$dir" ]]; then
    echo "run directory exists and is not a directory: $dir" >&2
    return 1
  fi

  if [[ -f "$marker" ]]; then
    local prev_owner prev_pid
    read -r prev_owner prev_pid _ < "$marker"

    if [[ "$prev_owner" != "$owner" ]]; then
      echo "refusing to delete a run directory created by a different harness:" >&2
      echo "  directory:   $dir" >&2
      echo "  created by:  $prev_owner" >&2
      echo "  this run is: $owner" >&2
      echo "  Two harnesses must not share a run directory (GH #11746, GH #11748)." >&2
      echo "  Use a separate --run-dir, or delete that directory yourself." >&2
      return 1
    fi

    # Same harness, but a run may still be live in there. PID reuse can make
    # this a false refusal; refusing is the safe direction and the message says
    # how to proceed.
    if [[ -n "$prev_pid" ]] && kill -0 "$prev_pid" 2>/dev/null; then
      echo "refusing to delete a run directory that is still in use:" >&2
      echo "  directory: $dir" >&2
      echo "  owned by:  $prev_owner (pid $prev_pid, still running)" >&2
      echo "  Use a separate --run-dir, or wait for that run to finish." >&2
      return 1
    fi

    # Ours, and idle: recreate it, which is the documented behaviour.
    rm -rf "$dir" || return 1
    mkdir -p "$dir" || return 1
    _eest_write_marker "$marker" "$owner"
    return 0
  fi

  # Exists, no marker: adopt it only if it is empty, so we delete nothing.
  if [[ -n "$(ls -A "$dir" 2>/dev/null)" ]]; then
    echo "refusing to delete a non-empty directory this harness did not create:" >&2
    echo "  directory: $dir" >&2
    echo "  It has no $EEST_RUN_DIR_MARKER marker, so its contents are not ours" >&2
    echo "  to remove (GH #11748). Point --run-dir at a new or empty directory," >&2
    echo "  or delete this one yourself if it is disposable." >&2
    return 1
  fi

  _eest_write_marker "$marker" "$owner"
  return 0
}

_eest_write_marker() {
  local marker="$1"
  local owner="$2"
  # owner, pid, and a human timestamp. Read back positionally by field.
  printf '%s %s %s\n' "$owner" "$$" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" > "$marker"
}
