#!/usr/bin/env bash
# check-misaligned-access.sh — partial gate for emitted wide-access traps.
#
# Scope: detects statically-resolvable misaligned wide accesses only.  Bases
# arriving as callee arguments, sp-relative bases, and bases clobbered across
# calls are classified UNKNOWN and are reported but NOT checked by this gate.
#
# The linked guest's .s is the input: run codegen-stateless-link-check.sh first.
# The self-test deliberately plants an INPUT_BASE+2 LD in a temporary fixture
# and requires this same scanner to return exit 1.  The real pre-fix
# validate_parent_hash_link control is run informationally below: objdump
# confirms four misaligned childBase+fo LDs there, while this scanner reports
# them as UNKNOWN.  It is excluded from the actionable gate until its separate
# fix lands; this command documents the blind spot rather than hiding it.
set -euo pipefail
cd "$(dirname "$0")/.."

OUT_PREFIX="${CODEGEN_STATELESS_LINK_OUT:-gen-out/stateless-link-check/stateless_guest}"
ASM="${MISALIGNED_ACCESS_ASM:-${OUT_PREFIX}.s}"

if [[ ! -s "$ASM" ]]; then
  echo "check-misaligned-access: missing emitted assembly: $ASM" >&2
  echo "run scripts/codegen-stateless-link-check.sh first" >&2
  exit 2
fi

# GH #13256: the scanned assembly must be traced to THIS checkout's emitted
# image, or the gate reports bytes the guest does not actually contain.  The
# default ${OUT_PREFIX}.s is produced fresh by codegen-stateless-link-check.sh
# and is tied by construction.  An explicit MISALIGNED_ACCESS_ASM override is
# the untied path: CI once fed a stale /tmp fixture here and the gate scanned
# bytes that were not the emitted image.  When a reference emits exists,
# require byte-identity; otherwise refuse loudly.  The escape hatch exists
# for scanning a deliberately different image and must be named, not silently
# plausible.
if [[ -n "${MISALIGNED_ACCESS_ASM:-}" ]]; then
  if [[ -s "${OUT_PREFIX}.s" ]]; then
    if ! cmp -s "$ASM" "${OUT_PREFIX}.s"; then
      if [[ "${MISALIGNED_ACCESS_ALLOW_STALE:-0}" != 1 ]]; then
        echo "check-misaligned-access: MISALIGNED_ACCESS_ASM=$ASM differs from the emitted ${OUT_PREFIX}.s" >&2
        echo "refusing to scan an untied assembly input; set MISALIGNED_ACCESS_ALLOW_STALE=1 only to" >&2
        echo "scan a deliberately different image (fixture/alternate build)" >&2
        exit 3
      fi
      echo "check-misaligned-access: WARNING scanning $ASM (differs from emitted ${OUT_PREFIX}.s)" >&2
    fi
  else
    if [[ "${MISALIGNED_ACCESS_ALLOW_STALE:-0}" != 1 ]]; then
      echo "check-misaligned-access: MISALIGNED_ACCESS_ASM=$ASM set but no emitted ${OUT_PREFIX}.s to tie against" >&2
      echo "run scripts/codegen-stateless-link-check.sh first, or set MISALIGNED_ACCESS_ALLOW_STALE=1" >&2
      exit 3
    fi
  fi
fi

python3 scripts/audit-misaligned-access.py --self-test
echo 'REAL CONTROL (known pre-fix scanner miss): validate_parent_hash_link'
python3 scripts/audit-misaligned-access.py --routine validate_parent_hash_link "$ASM"
exec python3 scripts/audit-misaligned-access.py --gate \
  --exclude-routine validate_parent_hash_link "$ASM"
