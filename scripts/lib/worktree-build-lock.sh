#!/usr/bin/env bash
# Serialize build/codegen drivers that write a worktree's Lake artefacts.
#
# The lock lives outside the worktree: artifact-cache materialisation can make
# .lake/build read-only, and a lock file there would turn that environmental
# condition into a second failure mode. flock releases it automatically when
# the driver exits, including on a crash.
set -euo pipefail

if [[ $# -eq 0 ]]; then
  echo "usage: $0 COMMAND [ARG ...]" >&2
  exit 2
fi

command -v flock >/dev/null 2>&1 || {
  echo "worktree-build-lock: required command 'flock' is missing" >&2
  exit 2
}

repo_root="$(cd "$(dirname "$0")/../.." && pwd -P)"
lock_dir="${EVMASM_BUILD_LOCK_DIR:-${TMPDIR:-/tmp}}"
lock_key="$(printf '%s' "$repo_root" | sha256sum | cut -c1-16)"
lock_file="${EVMASM_BUILD_LOCK_FILE:-$lock_dir/evm-asm-build-$lock_key.lock}"
mkdir -p "$(dirname "$lock_file")"

exec 9>"$lock_file"
if ! flock -n 9; then
  echo "worktree-build-lock: another build/regen driver is already running" >&2
  echo "  worktree: $repo_root" >&2
  echo "  lock:     $lock_file" >&2
  echo "  wait for it to finish before retrying" >&2
  exit 75
fi

echo "==> acquired worktree build lock: $lock_file"
EVMASM_BUILD_LOCK_HELD=1 "$@"
