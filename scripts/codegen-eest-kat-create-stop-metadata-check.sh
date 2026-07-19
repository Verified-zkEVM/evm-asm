#!/usr/bin/env bash
# codegen-eest-kat-create-stop-metadata-check.sh -- regression guard for
# depth-indexed CREATE metadata when a CREATE child halts with STOP.
#
# In the canonical Amsterdam v0.6.2 CALLCODE fixtures, d2/d3 create a contract
# whose initcode creates another contract and then STOPs.  The outer deposit
# must use its own creator metadata after the nested CREATE, not the inner
# frame's metadata.  These upstream EEST vectors are the canonical red cases;
# keep them external rather than vendoring their generated full inputs.
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
run_dir="${RUN_DIR:-$repo_root/gen-out/eest-run/kat-create-stop-metadata}"

echo "== KAT CREATE STOP metadata restoration =="

EEST_RUN_DIR="$run_dir" \
  "$repo_root/scripts/codegen-eest-stateless-check.sh" \
  --all \
  --backend spike \
  --filter 'test_callcode_dynamic_code' \
  --limit 4 --jobs 1 \
  --no-verdict-debug \
  --min-full 4 \
  "$@"

echo "== OK: nested CREATE STOP metadata matches execution-specs =="
