#!/usr/bin/env bash
# codegen-eest-eip7708-mainnet-check.sh -- focused EIP-7708 mainnet log gate.
#
# These rows were ERROR(exit) in the 2026-06-04 broad EEST log under a smaller
# step budget. Current main full-matches them with the standard larger budget;
# keep the subset covered while broader EIP-7708 transfer/burn log support is
# expanded in the implementation stack.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.5.0}"
JOBS="${EEST_EIP7708_MAINNET_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP7708_MAINNET_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP7708_MAINNET_RUN_DIR:-gen-out/eest-eip7708-mainnet}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_EIP7708_MAINNET_FILTER:-eip7708_eth_transfer_logs/eip_mainnet}"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-eip7708-mainnet-count"
rm -rf "$count_dir"
mkdir -p "$count_dir"
python3 scripts/eest-stateless-to-input.py \
  --fixtures-dir "$FX" \
  --out-dir "$count_dir" \
  --filter "$FILTER" \
  >/dev/null

manifest="$count_dir/manifest.tsv"
[[ -s "$manifest" ]] || { echo "no stateless blocks selected for $FILTER" >&2; exit 1; }
COUNT="$(wc -l < "$manifest" | tr -d " ")"

for required in \
  "eip7708_eth_transfer_logs/eip_mainnet/call_with_value_mainnet.json" \
  "eip7708_eth_transfer_logs/eip_mainnet/selfdestruct_mainnet.json" \
  "eip7708_eth_transfer_logs/eip_mainnet/simple_transfer_mainnet.json"; do
  if ! awk -F'\t' -v required="$required" '$7 ~ required { found = 1 } END { exit found ? 0 : 1 }' "$manifest"; then
    echo "required EIP-7708 mainnet fixture not selected by $FILTER: $required" >&2
    exit 1
  fi
done

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --limit "$COUNT" \
  --jobs "$JOBS" \
  --quiet-passes \
  --min-full "$COUNT" \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  "$@"

echo "==> PASS: EIP-7708 mainnet transfer-log frontier full-matched $COUNT row(s)"
