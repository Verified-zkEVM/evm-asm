#!/usr/bin/env bash
# check-hed-arity-guard.sh — CI entry for GH #12462.
#
# Assert from the *linked* stateless_guest ELF disassembly that every JAL
# targeting header_extended_decode is preceded (same function, linear reverse
# scan) by a JAL to header_extended_decode_arity_check.
#
# Why: the decoder accepts a canonical 20-field list while the spec rejects it.
# Production safety is only the call-site convention that both JALs sit behind
# the arity check. Nothing else enforces that — a third caller without the
# check makes the false accept live. This is the gate that would have caught
# #12438 (checker linked, zero callers).
#
# Belongs in the BUILD job (needs gen-out/regionmap/stateless_guest.elf), like
# check-orphan-blocks / check-rowed-liveness. Authority is the linked image,
# never Lean source / GuestAddrs literals.
#
# Always run --self-test first: a gate that cannot demonstrate catching a
# planted unguarded jal is itself unaudited.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

mode="${1:-}"
case "$mode" in
  ""|--elf)
    ;;
  --self-test)
    exec python3 scripts/hed_arity_guard.py --self-test
    ;;
  *)
    echo "usage: $0 [--self-test]  or  $0 --elf PATH" >&2
    exit 2
    ;;
esac

python3 scripts/hed_arity_guard.py --self-test

# Do NOT honor a bare `ELF=` env var — other harnesses export that name for
# unrelated images. Explicit override only via --elf or HED_ARITY_GUEST_ELF.
ELF="${HED_ARITY_GUEST_ELF:-gen-out/regionmap/stateless_guest.elf}"
if [[ "${1:-}" == "--elf" ]]; then
  ELF="${2:?path required after --elf}"
fi

# Rebuild when missing. Prefer an already-emitted ELF from an earlier lane step
# (region-map / link-check) so we do not emit twice in the parallel codegen lane.
if [[ ! -f "$ELF" ]]; then
  echo "hed_arity_guard: emitting $ELF"
  mkdir -p "$(dirname "$ELF")"
  lake exe codegen --program stateless_guest --halt linux93 \
    -o "${ELF%.elf}" >/dev/null
fi

exec python3 scripts/hed_arity_guard.py --elf "$ELF"
