#!/usr/bin/env bash
# codegen-eest-failed-tx-paris-layout-check.sh
#
# The Paris failed_tx_xcf416c53 fixture has block_gas_limit=200,000,000. The
# 1G static BSR/BAL layout must let this fixture launch through ziskemu instead
# of classifying it as layout-incompatible before execution.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.5.0}"
JOBS="${EEST_FAILED_TX_PARIS_JOBS:-${EEST_JOBS:-2}}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

RUN_DIR="${RUN_DIR:-gen-out/eest-failed-tx-paris-layout}"
JOBS="${EEST_FAILED_TX_PARIS_JOBS:-${EEST_JOBS:-2}}"
case "$RUN_DIR" in
  /*) ;;
  *) RUN_DIR="$PWD/$RUN_DIR" ;;
esac
rm -rf "$RUN_DIR"
mkdir -p "$RUN_DIR"

LOG="${LOG:-gen-out/eest-failed-tx-paris-layout.log}"
case "$LOG" in
  /*) ;;
  *) LOG="$PWD/$LOG" ;;
esac
rm -f "$LOG"

echo "==> run failed_tx Paris high-gas launch check"
scripts/codegen-eest-stateless-check.sh \
  --filter failed_tx_xcf416c53_paris \
  --limit 10 \
  --jobs "$JOBS" \
  --max-failures 1 \
  --quiet-passes \
  --steps "${EEST_FAILED_TX_PARIS_STEPS:-${EEST_STEPS:-1000000000}}" \
  --run-dir "$RUN_DIR" \
  >"$LOG" 2>&1

require_log() {
  local pattern="$1"
  if ! grep -Fq "$pattern" "$LOG"; then
    echo "missing expected output: $pattern" >&2
    sed -n '1,220p' "$LOG" >&2
    exit 1
  fi
}

require_log "filter=failed_tx_xcf416c53_paris"
require_log "selected:    1"
require_log "errored:     0"
require_log "ran:         1"

if grep -Fq "ERROR(layout)" "$LOG"; then
  echo "unexpected layout error for high-gas Paris fixture" >&2
  sed -n '1,220p' "$LOG" >&2
  exit 1
fi

if ! find "$RUN_DIR" -name '*.emu.log' -print -quit | grep -q .; then
  echo "expected ziskemu log was not found; high-gas fixture should launch guest" >&2
  find "$RUN_DIR" -maxdepth 2 -type f -print >&2
  exit 1
fi

echo "==> PASS: failed_tx Paris high-gas fixture launches without layout error"
