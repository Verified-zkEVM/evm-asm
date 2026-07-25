#!/usr/bin/env bash
# codegen-eest-kat-root-construction-forgery-check.sh -- 0-FA root-completeness guard.
#
# The three typed Amsterdam v0.6.2 inputs preserve SSZ framing and re-pin the
# payload header/hash after dropping receipts, execution requests, or one
# EIP-4895 withdrawal. execution-specs rejects all three. In particular the
# withdrawal case retains the original BAL/state credit while shortening the
# body, exercising the unbound BAL/body false-accept fixed by lukr5.
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
run_dir="${RUN_DIR:-$repo_root/gen-out/eest-run/kat-root-construction-forgery}"

echo "== KAT root-construction forgery (0-FA body/BAL completeness guard) =="
echo "   fixtures: $repo_root/fixtures/kat/root-construction-forgery"
echo "   run dir:  $run_dir"

EEST_FIXTURES_DIR="$repo_root/fixtures/kat/root-construction-forgery" \
EEST_RUN_DIR="$run_dir" \
  "$repo_root/scripts/codegen-eest-stateless-check.sh" \
  --backend spike \
  --filter root_construction_forgery \
  --limit 3 --jobs 1 \
  --no-verdict-debug \
  --min-succ 3 \
  "$@"

echo "== OK: receipt/request/withdrawal root forgeries rejected =="
