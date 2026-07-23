#!/usr/bin/env bash
# codegen-eest-kat-bounded-storage-full-clear-check.sh -- regression guard for
# bounded storage-root reconstruction when every pre-state slot is deleted.
#
# The two canonical Amsterdam v0.6.2 EEST cases below begin with a populated
# storage trie and clear it entirely.  They must rebuild EMPTY_TRIE_ROOT, not
# reuse a stale failed-builder result.  Keep these upstream cases external to
# avoid vendoring their 600KiB fixture JSON; the pinned fixture tag is the
# reproducible source of truth.
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
run_dir="${RUN_DIR:-$repo_root/gen-out/eest-run/kat-bounded-storage-full-clear}"

echo "== KAT bounded storage full-clear (EMPTY_TRIE_ROOT reconstruction) =="

EEST_RUN_DIR="$run_dir" \
  "$repo_root/scripts/codegen-eest-stateless-check.sh" \
  --all \
  --backend spike \
  --filter 'exceed_gas_refund_limit_' \
  --limit 2 --jobs 1 \
  --no-verdict-debug \
  --min-full 2 \
  "$@"

echo "== OK: both full-storage-clear fixtures match execution-specs =="
