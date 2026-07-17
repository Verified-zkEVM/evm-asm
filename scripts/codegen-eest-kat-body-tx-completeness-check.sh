#!/usr/bin/env bash
# codegen-eest-kat-body-tx-completeness-check.sh — 0-FA regression guard for
# evm-asm-pnq91 (body-tx completeness vs BAL/state_root).
#
# Runs the tracked KAT fixtures under fixtures/kat/body-tx-completeness/
# through the stateless guest (spike backend):
#   - body_tx_completeness_control  (byte32 = 1: valid multi-tx block, ACCEPTED)
#   - body_tx_completeness_primary  (byte32 = 0: drop final tx + body-consistent
#       header re-pin of gas/receipts/bloom/block_hash while retaining N-tx
#       BAL/state_root — REJECTED by execution-specs)
#
# Primary is currently a confirmed guest false-accept (pnq91) until the
# body-tx justification fix lands (same body-op-justification family as
# lukr5 withdrawals / rgtkz BAL storage / 7rbp3). Expect RED until fix;
# after fix this guard must stay GREEN.
#
# Optional full exploit bundle (9 ref-rejected variants) via --with-exploits.
#
# Regenerate fixtures:
#   EEST_FIXTURES_DIR=... uv run --directory execution-specs --quiet python3 \
#     scripts/kat/make_body_tx_completeness_kat.py
#
# Usage: scripts/codegen-eest-kat-body-tx-completeness-check.sh [--no-build] [--with-exploits]
# Exit: 0 = guard holds; non-zero = FAIL (expected while pnq91 unfixed on primary).
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
RUN_DIR="${RUN_DIR:-$REPO_ROOT/gen-out/eest-run/kat-body-tx-completeness}"
WITH_EXPLOITS=0
EXTRA_ARGS=()
for arg in "$@"; do
  case "$arg" in
    --with-exploits) WITH_EXPLOITS=1 ;;
    *) EXTRA_ARGS+=("$arg") ;;
  esac
done

echo "== KAT body-tx-completeness (0-FA guard, evm-asm-pnq91) =="
echo "   fixtures: $REPO_ROOT/fixtures/kat/body-tx-completeness"
echo "   run dir:  $RUN_DIR"

EEST_FIXTURES_DIR="$REPO_ROOT/fixtures/kat/body-tx-completeness" \
EEST_RUN_DIR="$RUN_DIR" \
  "$REPO_ROOT/scripts/codegen-eest-stateless-check.sh" \
  --backend spike \
  --filter body_tx_completeness_control \
  --limit 1 --jobs 1 \
  --no-verdict-debug \
  --min-full 1 \
  "${EXTRA_ARGS[@]}"

# Primary must match fixture succ=0 (ref-rejected). Guest currently false-accepts
# until the body-tx justification fix lands — this step is the red->green gate.
EEST_FIXTURES_DIR="$REPO_ROOT/fixtures/kat/body-tx-completeness" \
EEST_RUN_DIR="$RUN_DIR/primary" \
  "$REPO_ROOT/scripts/codegen-eest-stateless-check.sh" \
  --backend spike \
  --filter body_tx_completeness_primary \
  --limit 1 --jobs 1 \
  --no-verdict-debug \
  --min-succ 1 \
  "${EXTRA_ARGS[@]}"

if [[ "$WITH_EXPLOITS" -eq 1 ]]; then
  EEST_FIXTURES_DIR="$REPO_ROOT/fixtures/kat/body-tx-completeness" \
  EEST_RUN_DIR="$RUN_DIR/exploits" \
    "$REPO_ROOT/scripts/codegen-eest-stateless-check.sh" \
    --backend spike \
    --filter body_tx_completeness_exploits \
    --limit 9 --jobs 2 \
    --no-verdict-debug \
    --min-succ 9 \
    "${EXTRA_ARGS[@]}"
fi

echo "== OK: control accepted + primary (and optional exploits) rejected =="
