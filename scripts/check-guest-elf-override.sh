#!/usr/bin/env bash
# check-guest-elf-override.sh -- negative control on the guest-ELF override guard.
#
# GH #10617. The harness used to resolve its guest as
# `USER_GUEST_ELF="${GUEST_ELF:-…}"`, where `USER_GUEST_ELF` was the *internal*
# variable. Exporting the internal name was therefore silently ignored: three
# consecutive sweeps ran the DEFAULT guest, reported clean passes, and a 120-row
# false-reject population was declared fixed on that evidence.
#
# The override is now a flag and the environment names are rejected. This script
# is the mechanism that keeps it that way, because the review of the fix found the
# same failure one layer up: the guard was written with `-n` (a NON-EMPTY test),
# the change was verified by exporting a *path*, and so the one case that
# distinguishes `-n` from a presence test -- an EMPTY export -- was the case never
# exercised. A claim about the empty case needs the empty case run. That is what
# this file does, on every push, instead of asking anyone to remember.
#
# Each assertion below is a case where a WRONG implementation still looks right:
#   * `-n` instead of `${var+x}`  -> an empty export sails through (case 1)
#   * honouring the flag but not rejecting a stale export -> ambiguous intent
#     resolved silently by precedence (case 3)
#   * falling back to the default guest when the flag names a missing file ->
#     the original incident, one layer down (case 5)
set -uo pipefail
cd "$(dirname "$0")/.."

HARNESS=scripts/codegen-eest-stateless-check.sh
PARITY=scripts/spike/parity-check.sh
rc=0

fail() { echo "FAIL: $*" >&2; rc=1; }
ok()   { echo "  ok: $*"; }

# Every case must exit non-zero AND name the flag, so the operator is told what
# to do rather than only what not to do. An exit code alone would pass even if
# the script died for an unrelated reason.
expect_rejected() {
  local what="$1"; shift
  local out status
  out="$("$@" 2>&1)"; status=$?
  if [[ "$status" -eq 0 ]]; then
    fail "$what was ACCEPTED (exit 0) -- a silent override is the incident this guard exists to prevent"
    return
  fi
  if ! grep -q -- '--guest-elf' <<<"$out"; then
    fail "$what was rejected but the message never names --guest-elf: $out"
    return
  fi
  ok "$what rejected, message names the flag"
}

echo "==> guest-ELF override guard ($HARNESS)"

# 1. PRESENCE, not a non-empty value. The likeliest source of an empty export is
#    a wrapper or profile that computed a path and got the empty string -- which
#    is exactly the case where a silent fallback misleads most.
expect_rejected "empty GUEST_ELF export" \
  env GUEST_ELF= "$HARNESS" --limit 1 --backend spike

# 2. The non-empty form of the same variable.
expect_rejected "GUEST_ELF=<path> export" \
  env GUEST_ELF=/nonexistent/guest.elf "$HARNESS" --limit 1 --backend spike

# 3. Presence is rejected even beside a CORRECT flag: a stale export next to a
#    correct flag is ambiguous about intent, and precedence rules are not.
expect_rejected "GUEST_ELF export alongside a correct --guest-elf" \
  env GUEST_ELF=/nonexistent/guest.elf "$HARNESS" --limit 1 --backend spike --guest-elf /bin/sh

# 4. The internal spelling -- the one actually exported in the incident.
expect_rejected "empty USER_GUEST_ELF export" \
  env USER_GUEST_ELF= "$HARNESS" --limit 1 --backend spike

# 5. A flag naming a path that does not exist must NOT fall back to the default
#    guest. That fallback is the incident itself, one layer down.
expect_rejected "--guest-elf pointing at a missing file" \
  "$HARNESS" --limit 1 --backend spike --guest-elf /nonexistent/guest.elf

echo "==> the rejected names and the used names are disjoint"
# The guard rejects GUEST_ELF / USER_GUEST_ELF. If the script also USES a variable
# of that name, an inherited child environment or a future export would make the
# harness trip its own guard. Disjointness makes that impossible by construction
# rather than by nobody happening to export it.
for f in "$HARNESS" "$PARITY"; do
  if grep -nE '^[[:space:]]*(GUEST_ELF|USER_GUEST_ELF)=' "$f"; then
    fail "$f assigns to a variable named GUEST_ELF/USER_GUEST_ELF (the names the guard rejects); rename the internal one"
  else
    ok "$f: no assignment to a rejected name"
  fi
done

echo "==> $PARITY rejects the same names"
expect_rejected "empty GUEST_ELF export (parity-check)" \
  env GUEST_ELF= "$PARITY"

if [[ "$rc" -eq 0 ]]; then
  echo "guest-ELF override guard: all cases rejected as required"
fi
exit "$rc"
