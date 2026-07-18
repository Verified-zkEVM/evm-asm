#!/usr/bin/env bash
# codegen-eest-kat-body-multi-drop-check.sh — 0-FA regression guard for
# evm-asm-lljmj (multi-drop body-tx + body-withdrawals vs BAL/state_root).
#
# Runs tracked KAT fixtures under fixtures/kat/body-multi-drop/ through the
# stateless guest (spike backend):
#   - body_multi_drop_control  (byte32 = 1: honest block with body wd + tx)
#   - body_multi_drop_primary  (byte32 = 0: empty body + body-consistent header
#       re-pin while retaining BAL/state_root — REJECTED by execution-specs)
#
# Primary is currently a confirmed guest false-accept (lljmj = pnq91+lukr5
# extreme) until the body-op justification fix lands. Expect RED until fix;
# after fix this guard must stay GREEN.
#
# Optional full exploit bundle via --with-exploits.
#
# Regenerate fixtures:
#   EEST_FIXTURES_DIR=... uv run --directory execution-specs --quiet python3 \
#     scripts/kat/make_body_multi_drop_kat.py
#
# Usage: scripts/codegen-eest-kat-body-multi-drop-check.sh [--no-build] [--with-exploits]
# Exit: 0 = guard holds; non-zero = FAIL (expected while lljmj unfixed on primary).
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
RUN_DIR="${RUN_DIR:-$REPO_ROOT/gen-out/eest-run/kat-body-multi-drop}"
WITH_EXPLOITS=0
EXTRA_ARGS=()
for arg in "$@"; do
  case "$arg" in
    --with-exploits) WITH_EXPLOITS=1 ;;
    *) EXTRA_ARGS+=("$arg") ;;
  esac
done

echo "== KAT body-multi-drop (0-FA guard, evm-asm-lljmj) =="
echo "   fixtures: $REPO_ROOT/fixtures/kat/body-multi-drop"
echo "   run dir:  $RUN_DIR"

EEST_FIXTURES_DIR="$REPO_ROOT/fixtures/kat/body-multi-drop" \
EEST_RUN_DIR="$RUN_DIR" \
  "$REPO_ROOT/scripts/codegen-eest-stateless-check.sh" \
  --backend spike \
  --filter body_multi_drop_control \
  --limit 1 --jobs 1 \
  --no-verdict-debug \
  --min-full 1 \
  "${EXTRA_ARGS[@]}"

# Primary must match fixture succ=0 (ref-rejected). Guest currently false-accepts
# until the body-op justification fix lands — this step is the red->green gate.
EEST_FIXTURES_DIR="$REPO_ROOT/fixtures/kat/body-multi-drop" \
EEST_RUN_DIR="$RUN_DIR/primary" \
  "$REPO_ROOT/scripts/codegen-eest-stateless-check.sh" \
  --backend spike \
  --filter body_multi_drop_primary \
  --limit 1 --jobs 1 \
  --no-verdict-debug \
  --min-succ 1 \
  "${EXTRA_ARGS[@]}"

if [[ "$WITH_EXPLOITS" -eq 1 ]]; then
  EEST_FIXTURES_DIR="$REPO_ROOT/fixtures/kat/body-multi-drop" \
  EEST_RUN_DIR="$RUN_DIR/exploits" \
    "$REPO_ROOT/scripts/codegen-eest-stateless-check.sh" \
    --backend spike \
    --filter body_multi_drop_exploits \
    --limit 4 --jobs 2 \
    --no-verdict-debug \
    --min-succ 4 \
    "${EXTRA_ARGS[@]}"
fi

echo "== OK: control accepted + primary (and optional exploits) rejected =="
