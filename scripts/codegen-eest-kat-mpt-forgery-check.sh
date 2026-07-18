#!/usr/bin/env bash
# codegen-eest-kat-mpt-forgery-check.sh -- full-guest 0-FA MPT/BAL guard.
#
# `mpt_forgery_control` holds an expected-valid v0.6.2 Amsterdam block and
# 1023/1024-byte unused-node boundary controls.  The
# eight `mpt_forgery_exploits` preserve host/SSZ framing while respectively
# forge a witness node, RLP envelope, node size, BAL account post-value, or BAL
# storage post-value.  The control must full-match.  Each exploit must match
# the only semantic property of a rejected block: byte 32 is zero.  In
# particular, the 1025-byte ByteList is rejected by execution-specs during SSZ
# deserialization (zero request root) and by the guest at its later per-node
# cap (payload-derived request root); neither root is observable once succ=0.
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
run_dir="${RUN_DIR:-$repo_root/gen-out/eest-run/kat-mpt-forgery}"
extra_args=("$@")

echo "== KAT mpt-forgery (0-FA witness/BAL trust-boundary guard) =="
echo "   fixtures: $repo_root/fixtures/kat/mpt-forgery"
echo "   run dir:  $run_dir"

EEST_FIXTURES_DIR="$repo_root/fixtures/kat/mpt-forgery" \
EEST_RUN_DIR="$run_dir" \
  "$repo_root/scripts/codegen-eest-stateless-check.sh" \
  --backend spike \
  --filter mpt_forgery_control \
  --limit 3 --jobs 2 \
  --no-verdict-debug \
  --min-full 3 \
  "${extra_args[@]}"

EEST_FIXTURES_DIR="$repo_root/fixtures/kat/mpt-forgery" \
EEST_RUN_DIR="$run_dir/exploits" \
  "$repo_root/scripts/codegen-eest-stateless-check.sh" \
  --backend spike \
  --filter mpt_forgery_exploits \
  --limit 8 --jobs 2 \
  --no-verdict-debug \
  --min-succ 8 \
  "${extra_args[@]}"

echo "== OK: canonical controls accepted + eight witness/BAL forgeries rejected =="
