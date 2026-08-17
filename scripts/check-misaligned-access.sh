#!/usr/bin/env bash
# check-misaligned-access.sh — blocking gate for emitted wide-access traps.
#
# The linked guest's .s is the input: run codegen-stateless-link-check.sh first.
# The self-test deliberately plants an INPUT_BASE+2 LD in a temporary fixture
# and requires this same scanner to return exit 1, so a clean report cannot be
# mistaken for a gate that never learned how to fail.
set -euo pipefail
cd "$(dirname "$0")/.."

OUT_PREFIX="${CODEGEN_STATELESS_LINK_OUT:-gen-out/stateless-link-check/stateless_guest}"
ASM="${MISALIGNED_ACCESS_ASM:-${OUT_PREFIX}.s}"

if [[ ! -s "$ASM" ]]; then
  echo "check-misaligned-access: missing emitted assembly: $ASM" >&2
  echo "run scripts/codegen-stateless-link-check.sh first" >&2
  exit 2
fi

python3 scripts/audit-misaligned-access.py --self-test
exec python3 scripts/audit-misaligned-access.py --gate \
  --exclude-routine validate_parent_hash_link "$ASM"
