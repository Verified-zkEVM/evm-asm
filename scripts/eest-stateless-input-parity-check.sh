#!/usr/bin/env bash
# eest-stateless-input-parity-check.sh -- Check that EEST zkevm guest inputs
# are passed to the RISC-V guest with the same bytes Python execution-specs
# run_stateless_guest consumes.
set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
FX="${EEST_FIXTURES_DIR:-$REPO_ROOT/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
RUN_DIR="${EEST_INPUT_PARITY_RUN_DIR:-$REPO_ROOT/gen-out/eest-input-parity}"
LIMIT="${EEST_INPUT_PARITY_LIMIT:-2}"

usage() {
  cat <<'USAGE'
Usage:
  scripts/eest-stateless-input-parity-check.sh [options]

Options:
  --tag TAG              EEST fixture tag (default $EEST_FIXTURE_TAG or zkevm@v0.4.0)
  --fixtures-dir DIR     fixture root (default gen-out/eest-fixtures/$TAG/fixtures/fixtures)
  --run-dir DIR          output directory (default gen-out/eest-input-parity)
  --limit N              cases per representative filter (default 2)
  -h, --help             show this help

The script checks two representative fixture classes when available:
  * blockchain_tests/for_amsterdam/frontier
  * blockchain_tests/for_amsterdam/osaka

For each selected block, scripts/eest-stateless-to-input.py verifies that:
  * the emitted ziskemu -i file unpacks to exactly statelessInputBytes; and
  * execution-specs can decode those same statelessInputBytes through the
    input path used by run_stateless_guest.
USAGE
}

require_arg() {
  local opt="$1"
  if [[ $# -lt 2 || -z "${2:-}" ]]; then
    echo "$opt requires an argument" >&2
    usage >&2
    exit 1
  fi
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) usage; exit 0 ;;
    --tag) require_arg "$1" "${2:-}"; TAG="$2"; FX="${EEST_FIXTURES_DIR:-$REPO_ROOT/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"; shift 2 ;;
    --fixtures-dir) require_arg "$1" "${2:-}"; FX="$2"; shift 2 ;;
    --run-dir) require_arg "$1" "${2:-}"; RUN_DIR="$2"; shift 2 ;;
    --limit) require_arg "$1" "${2:-}"; LIMIT="$2"; shift 2 ;;
    *) echo "unknown arg: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if ! [[ "$LIMIT" =~ ^[0-9]+$ ]] || [[ "$LIMIT" -lt 1 ]]; then
  echo "--limit must be a positive integer (got: $LIMIT)" >&2
  exit 1
fi
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

mkdir -p "$RUN_DIR"

run_filter() {
  local name="$1"
  local filter="$2"
  local out="$RUN_DIR/$name"
  echo "==> parity check: $filter (limit=$LIMIT)"
  uv run --directory execution-specs --quiet python3 \
    "$REPO_ROOT/scripts/eest-stateless-to-input.py" \
    --fixtures-dir "$FX" \
    --out-dir "$out" \
    --filter "$filter" \
    --limit "$LIMIT" \
    --verify-input-parity \
    --verify-execution-spec-input
  [[ -s "$out/manifest.tsv" ]] || { echo "no stateless blocks selected for $filter" >&2; exit 1; }
}

run_filter amsterdam_frontier blockchain_tests/for_amsterdam/frontier
run_filter amsterdam_osaka blockchain_tests/for_amsterdam/osaka

echo "PASS: stateless guest input parity checks passed"
