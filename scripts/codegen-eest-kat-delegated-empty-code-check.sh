#!/usr/bin/env bash
# Regression guard for EIP-7702 delegation to an authenticated empty-code target.
#
# The canonical Amsterdam v0.6.2 witness-codes case has a delegated target
# whose authenticated account carries EMPTY_CODE_HASH but has no code-section
# entry. execution-specs resolves it as empty code; the guest must do the same.
# Keep the upstream fixture external as the oracle.
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
run_dir="${RUN_DIR:-$repo_root/gen-out/eest-run/kat-delegated-empty-code}"

echo "== KAT delegated empty code =="
EEST_RUN_DIR="$run_dir" \
  "$repo_root/scripts/codegen-eest-stateless-check.sh" \
  --backend spike \
  --filter 'test_witness_codes_delegation_to_empty_account' \
  --limit 1 --jobs 1 \
  --no-verdict-debug \
  --min-full 1 \
  "$@"

echo "== OK: delegated EMPTY_CODE_HASH target executes as empty code =="
