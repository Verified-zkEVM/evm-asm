#!/usr/bin/env bash
# Regression guard for an authenticated absent recipient with BAL storage keys.
#
# `test_clz_from_set_code` has no recipient account in the parent witness, but
# its BAL carries slots 0, 1, and 2 for that recipient.  execution-specs reads
# those pre-state slots as zero through EMPTY_TRIE_ROOT.  The dispatch preload
# must do the same rather than conservatively bailing before receipt gas can be
# materialized.  Keep the canonical Amsterdam v0.6.2 fixture external rather
# than vendoring it; the pinned EEST fixture tag is the reproducible oracle.
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
run_dir="${RUN_DIR:-$repo_root/gen-out/eest-run/kat-absent-recipient-storage-preload}"

echo "== KAT absent recipient storage preload =="
EEST_RUN_DIR="$run_dir" \
  "$repo_root/scripts/codegen-eest-stateless-check.sh" \
  --backend spike \
  --filter 'test_clz_from_set_code' \
  --limit 1 --jobs 1 \
  --no-verdict-debug \
  --min-full 1 \
  "$@"

echo "== OK: absent recipient storage slots preload as authenticated zero =="
