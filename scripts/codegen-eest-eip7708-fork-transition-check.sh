#!/usr/bin/env bash
# Run the EIP-7708 fork-transition transfer/burn log stateless EEST frontier.
#
# The wrapper derives the run size from the converted manifest so new
# fork-transition rows in future EEST tags are included automatically.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-$(cat scripts/eest-fixture-tag.txt)}"
JOBS="${EEST_EIP7708_FORK_TRANSITION_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP7708_FORK_TRANSITION_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP7708_FORK_TRANSITION_RUN_DIR:-gen-out/eest-eip7708-fork-transition}"
FILTER="${EEST_EIP7708_FORK_TRANSITION_FILTER:-eip7708_eth_transfer_logs/fork_transition}"

FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

COUNT_DIR="$(pwd)/gen-out/eest-eip7708-fork-transition-count"
rm -rf "$COUNT_DIR"
mkdir -p "$COUNT_DIR"

echo "==> count EIP-7708 fork-transition fixtures (tag=$TAG)"
python3 scripts/eest-stateless-to-input.py \
  --fixtures-dir "$FX" \
  --out-dir "$COUNT_DIR" \
  --filter "$FILTER" \
  >/dev/null

MANIFEST="$COUNT_DIR/manifest.tsv"
[[ -s "$MANIFEST" ]] || { echo "no EIP-7708 fork-transition stateless blocks selected" >&2; exit 1; }
TOTAL="$(wc -l < "$MANIFEST" | tr -d ' ')"
echo "==> EIP-7708 fork-transition selected: $TOTAL"

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --limit "$TOTAL" \
  --jobs "$JOBS" \
  --quiet-passes \
  --min-full "$TOTAL" \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  "$@"

echo "==> PASS: EIP-7708 fork-transition rows full-match ($TOTAL case(s))"
