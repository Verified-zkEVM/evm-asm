#!/usr/bin/env bash
# 0-FA guard for an omitted recipient BAL storage row when runtime effects did
# not materialize.  The fixture is execution-specs-derived from v0.6.2 03099.
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
run_dir="${RUN_DIR:-$repo_root/gen-out/eest-run/kat-recipient-storage-arena}"

echo "== KAT recipient storage arena fail-closed (0-FA) =="
EEST_FIXTURES_DIR="$repo_root/fixtures/kat/recipient-storage-arena" \
EEST_RUN_DIR="$run_dir" \
  "$repo_root/scripts/codegen-eest-stateless-check.sh" \
  --backend spike \
  --filter recipient_storage_arena_fail_closed \
  --limit 1 --jobs 1 \
  --no-verdict-debug \
  --min-succ 1 \
  "$@"

echo "== OK: re-rooted recipient-storage omission rejected =="
