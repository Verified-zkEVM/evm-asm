#!/usr/bin/env bash
# Run a command and explain cache-backed permission failures without changing
# the command's output or exit status.
set -uo pipefail

if [[ $# -eq 0 ]]; then
  echo "usage: $0 COMMAND [ARG ...]" >&2
  exit 2
fi

log="$(mktemp -t evm-asm-lake.XXXXXX)"
trap 'rm -f "$log"' EXIT

set +e
"$@" 2>&1 | tee "$log"
status="${PIPESTATUS[0]}"
set -e

cache_enabled=0
case "${LAKE_ARTIFACT_CACHE:-}" in
  1|true|TRUE|yes|YES) cache_enabled=1 ;;
esac
build_dir="${EVMASM_LAKE_BUILD_DIR:-$PWD/.lake/build}"

if (( status != 0 && cache_enabled )) \
   && grep -qiE 'permission denied|error code: 13|EACCES' "$log"; then
  readonly_count="$(find "$build_dir" -type f ! -perm -u+w -print 2>/dev/null | wc -l | tr -d ' ')"
  if [[ "$readonly_count" -gt 0 ]]; then
    echo "lake-cache-diagnostic: command failed with a permission error while" >&2
    echo "  LAKE_ARTIFACT_CACHE is enabled and $readonly_count read-only artefact(s)" >&2
    echo "  are present under $build_dir." >&2
    echo "  Re-run with LAKE_ARTIFACT_CACHE=false to materialize private outputs." >&2
    echo "  Do not chmod .lake/build: cache entries may be hardlinks into the shared cache." >&2
  fi
fi

exit "$status"
