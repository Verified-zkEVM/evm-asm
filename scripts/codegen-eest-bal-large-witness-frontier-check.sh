#!/usr/bin/env bash
# Probe the large remaining EIP-7002 withdrawal-request BAL replay frontier.
#
# The default 64 KiB block_state_root witness cap conservatively misses this
# fixture. Raising the experimental cap to 256 KiB exposes the next blocker
# directly: the guest currently exits before completing the replay.
set -euo pipefail

cd "$(dirname "$0")/.."

JOBS="${EEST_BAL_LARGE_WITNESS_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_BAL_LARGE_WITNESS_STEPS:-${EEST_STEPS:-2000000000}}"
BSR_WITNESS_CAP="${EEST_BSR_WITNESS_CAP:-262144}"
RUN_DIR="${EEST_RUN_DIR:-gen-out/eest-run/bal-large-witness-frontier-$(date -u +%Y%m%dT%H%M%SZ)-$$}"
export EEST_RUN_DIR="$RUN_DIR"

emit_witness_report() {
  local manifest="$RUN_DIR/manifest.tsv"
  local uv_manifest="$manifest"
  [[ -f "$manifest" ]] || return 0
  echo "==> BAL large-witness resource diagnostics"
  if command -v uv >/dev/null 2>&1 && [[ -d execution-specs ]]; then
    [[ "$uv_manifest" = /* ]] || uv_manifest="../$uv_manifest"
    uv run --directory execution-specs --quiet python3 \
      ../scripts/eest-bal-replay-report.py \
      --manifest "$uv_manifest" \
      --bsr-cap "$BSR_WITNESS_CAP" \
      --filter withdrawal_requests \
      --limit 1 || echo "  warn: witness resource diagnostics failed" >&2
  else
    python3 scripts/eest-bal-replay-report.py \
      --manifest "$manifest" \
      --bsr-cap "$BSR_WITNESS_CAP" \
      --filter withdrawal_requests \
      --limit 1 || echo "  warn: witness resource diagnostics failed" >&2
  fi
}

status=0
scripts/codegen-eest-stateless-check.sh \
  --filter withdrawal_requests \
  --skip 87 \
  --limit 1 \
  --jobs "$JOBS" \
  --quiet-passes \
  --max-failures 1 \
  --bsr-witness-cap "$BSR_WITNESS_CAP" \
  --steps "$STEPS" \
  "$@" || status=$?

emit_witness_report

if [[ "$status" -ne 0 ]]; then
  exit "$status"
fi

echo "==> PASS: BAL large-witness frontier probe completed with bsr_witness_cap=$BSR_WITNESS_CAP"
