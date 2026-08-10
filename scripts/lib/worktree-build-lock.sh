#!/usr/bin/env bash
# Serialize build/codegen drivers that write a worktree's Lake artefacts.
#
# The lock lives outside the worktree: artifact-cache materialisation can make
# .lake/build read-only, and a lock file there would turn that environmental
# condition into a second failure mode.
#
# Acquisition (never runs unlocked):
#   1. flock when available (Linux/GNU) — fd held until this process exits,
#      including on crash. Behaviour identical to the historical helper.
#   2. Else atomic mkdir (portable; macOS has no flock). Released via EXIT
#      trap; stale dir from a dead pid is reclaimed once. If acquisition
#      fails, exit 75 — same as the flock busy path.
#
# Lock key: sha256 of the absolute worktree path, first 16 hex chars. Prefer
# sha256sum (GNU); else shasum -a 256. Both emit the same hex digest for the
# same bytes, so an existing lock file remains recognised across tools.
set -euo pipefail

if [[ $# -eq 0 ]]; then
  echo "usage: $0 COMMAND [ARG ...]" >&2
  exit 2
fi

repo_root="$(cd "$(dirname "$0")/../.." && pwd -P)"
lock_dir="${EVMASM_BUILD_LOCK_DIR:-${TMPDIR:-/tmp}}"

if command -v sha256sum >/dev/null 2>&1; then
  lock_key="$(printf '%s' "$repo_root" | sha256sum | cut -c1-16)"
elif command -v shasum >/dev/null 2>&1; then
  lock_key="$(printf '%s' "$repo_root" | shasum -a 256 | cut -c1-16)"
else
  echo "worktree-build-lock: required command 'sha256sum' or 'shasum' is missing" >&2
  exit 2
fi

lock_file="${EVMASM_BUILD_LOCK_FILE:-$lock_dir/evm-asm-build-$lock_key.lock}"
mkdir -p "$(dirname "$lock_file")"

busy() {
  echo "worktree-build-lock: another build/regen driver is already running" >&2
  echo "  worktree: $repo_root" >&2
  echo "  lock:     $1" >&2
  echo "  wait for it to finish before retrying" >&2
  exit 75
}

if command -v flock >/dev/null 2>&1; then
  # --- GNU/Linux path (unchanged semantics) ---------------------------------
  exec 9>"$lock_file"
  if ! flock -n 9; then
    busy "$lock_file"
  fi
  echo "==> acquired worktree build lock: $lock_file"
  EVMASM_BUILD_LOCK_HELD=1 "$@"
  exit $?
fi

# --- Portable fallback: atomic mkdir (no unlocked run) ----------------------
mkdir_lock="${lock_file}.d"

acquire_mkdir_lock() {
  if mkdir "$mkdir_lock" 2>/dev/null; then
    printf '%s\n' "$$" >"$mkdir_lock/pid"
    return 0
  fi
  # One stale reclaim if the holder pid is dead.
  if [[ -f "$mkdir_lock/pid" ]]; then
    local old_pid
    old_pid="$(cat "$mkdir_lock/pid" 2>/dev/null || true)"
    if [[ "$old_pid" =~ ^[0-9]+$ ]] && ! kill -0 "$old_pid" 2>/dev/null; then
      rm -rf "$mkdir_lock"
      if mkdir "$mkdir_lock" 2>/dev/null; then
        printf '%s\n' "$$" >"$mkdir_lock/pid"
        return 0
      fi
    fi
  fi
  return 1
}

if ! acquire_mkdir_lock; then
  busy "$mkdir_lock"
fi

release_mkdir_lock() {
  if [[ -d "$mkdir_lock" ]] && [[ -f "$mkdir_lock/pid" ]] \
      && [[ "$(cat "$mkdir_lock/pid" 2>/dev/null || true)" == "$$" ]]; then
    rm -rf "$mkdir_lock"
  fi
}
trap release_mkdir_lock EXIT INT TERM

echo "==> acquired worktree build lock: $mkdir_lock (mkdir fallback; flock missing)"
EVMASM_BUILD_LOCK_HELD=1 "$@"
exit $?
