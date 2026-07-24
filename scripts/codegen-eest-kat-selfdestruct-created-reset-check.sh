#!/usr/bin/env bash
# Regression guard for tx-local CREATE liveness used by SELFDESTRUCT's
# NEW_ACCOUNT state-gas surcharge.
#
# The canonical Amsterdam vectors create and destroy contracts in tx0, then
# execute a further destruction in tx1.  The CREATE-address table is a
# tx-local liveness aid: it must suppress the surcharge for an account created
# earlier in the *same* transaction, but it must be empty for tx1 so a genuinely
# new beneficiary is still charged.  These upstream EEST fixtures exercise
# both sides on the normal full-guest path.
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
run_dir="${RUN_DIR:-$repo_root/gen-out/eest-run/kat-selfdestruct-created-reset}"

echo "== KAT SELFDESTRUCT tx-local created-account reset =="

EEST_RUN_DIR="$run_dir" \
  "$repo_root/scripts/codegen-eest-stateless-check.sh" \
  --all \
  --backend spike \
  --filter 'test_create_multiple_contracts_destroy_one_then_destroy_other_next_tx' \
  --limit 2 --jobs 1 \
  --no-verdict-debug \
  --min-full 2 \
  "$@"

echo "== OK: SELFDESTRUCT created-account liveness is tx-local =="
