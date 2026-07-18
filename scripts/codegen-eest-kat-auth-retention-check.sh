#!/usr/bin/env bash
# codegen-eest-kat-auth-retention-check.sh — 0-FA regression guard for
# bmvmx.5.5.11.1 (EIP-8037 auth state-gas retention at the sequential
# inclusion gate).
#
# Runs the two tracked KAT fixtures under fixtures/kat/eip8037-auth-retention/
# through the stateless guest (spike backend) and requires BOTH to byte-match
# their fixture `statelessOutputBytes`:
#   - auth_retention_control  (byte32 = 1: valid block, ACCEPTED)
#   - auth_retention_exploit  (byte32 = 0: invalid block, REJECTED)
# The exploit crafts a failed 7702 tx whose new-account authority charge
# (218,790 state gas) the reference retains toward the block state budget,
# followed by a tx that fits only if that charge is under-counted. A guest
# that accepts it under-counts retained auth state gas at the inclusion gate.
#
# Regenerate the fixtures with the committed generator spec:
#   scripts/kat/test_auth_retention_kat.py  (fill recipe in its header).
#
# Usage: scripts/codegen-eest-kat-auth-retention-check.sh [--no-build]
# Exit: 0 = guard holds (both fixtures byte-match); non-zero = FAIL.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
RUN_DIR="${RUN_DIR:-$REPO_ROOT/gen-out/eest-run/kat-auth-retention}"
EXTRA_ARGS=("$@")

echo "== KAT eip8037-auth-retention (0-FA guard, bmvmx.5.5.11.1) =="
echo "   fixtures: $REPO_ROOT/fixtures/kat/eip8037-auth-retention"
echo "   run dir:  $RUN_DIR"

EEST_FIXTURES_DIR="$REPO_ROOT/fixtures/kat/eip8037-auth-retention" \
EEST_RUN_DIR="$RUN_DIR" \
  "$REPO_ROOT/scripts/codegen-eest-stateless-check.sh" \
  --backend spike \
  --filter auth_retention \
  --limit 2 --jobs 2 \
  --no-verdict-debug \
  --min-full 2 \
  "${EXTRA_ARGS[@]}"

echo "== OK: control accepted + exploit rejected (byte-exact) =="
