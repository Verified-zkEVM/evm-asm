#!/usr/bin/env bash
# Compatibility wrapper for the current opcode regression runner.
#
# The opcode testcase registry now includes runtime-only fields such as
# calldata, storage preload, halt-kind, post-state storage, and event-log
# expectations. The old per-case data-baked runner ignored those columns and
# produced false failures for valid runtime dispatcher cases. Keep this script
# name for existing callers, but execute the runtime runner as the source of
# truth.
set -euo pipefail

cd "$(dirname "$0")/.."
exec scripts/codegen-opcodes-runtime-check.sh "$@"
