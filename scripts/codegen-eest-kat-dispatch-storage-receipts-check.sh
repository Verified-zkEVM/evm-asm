#!/usr/bin/env bash
# 0-FA guard: an incomplete runtime dispatch must not accept attacker-pinned
# receipts/state commitments after a BAL storage tuple is omitted.
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
run_dir="${RUN_DIR:-$repo_root/gen-out/eest-run/kat-dispatch-storage-receipts}"

echo "== KAT dispatch storage/receipts fail-closed (0-FA) =="
EEST_FIXTURES_DIR="$repo_root/fixtures/kat/dispatch-storage-receipts" \
EEST_RUN_DIR="$run_dir" \
  "$repo_root/scripts/codegen-eest-stateless-check.sh" \
  --backend spike \
  --filter dispatch_storage_receipts_fail_closed \
  --limit 1 --jobs 1 \
  --no-verdict-debug \
  --min-succ 1 \
  "$@"

echo "== OK: incomplete-runtime storage omission rejected =="
