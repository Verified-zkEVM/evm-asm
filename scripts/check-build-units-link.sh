#!/usr/bin/env bash
# check-build-units-link.sh — link each named build unit and fail on any NEW
# link failure (GH #10619).
#
# WHY THIS EXISTS
# ---------------
# `lake build` compiles Lean. It does NOT assemble or link the emitted RISC-V, so a
# build unit can reference an undefined symbol and every existing gate stays green:
#
#   * `lake build`              — green; the fault is in emitted asm, not in Lean.
#   * `check-asm-to-program.sh` — green; it byte-ties converted `Program`s against
#                                 `GuestAddrs`, and says nothing about unit links.
#   * `check-region-map.sh`     — green; it pins `stateless_guest` only.
#
# That is exactly how `zisk_stateless_verdict_v2` stayed broken across three
# commits of GH #10619: it mirrors the guest's handlers, so it picked up calls to
# `storage_read_record`, `code_read_fetch`, `read_sets_incorporate_tx` and
# `account_at_header_state_root_tracked` without defining any of them. It surfaced
# only as a linker error buried inside an EEST A/B leg.
#
# The lesson from the earlier instance in that branch was "an emit is only verified
# once the .elf exists". This script is the stronger form: A UNIT CAN BE MISSING AN
# .ELF THAT NOTHING IN THE GATE SET EVER BUILDS, so "the guest links" does not mean
# "the units link". Link each unit.
#
# KNOWN-NONLINKABLE (allowlist, not failures)
# -------------------------------------------
# Some units are *structurally* non-linkable: they are spliced INTO the guest rather
# than linked alone, so they legitimately carry undefined cross-unit references.
# `scripts/gen-symbol-addresses.py` documents this for `runtime_dispatcher`. These
# are allowlisted below with the symbols that make them so — the point of the
# allowlist is that a NEW failure is a regression even though old ones are not.
#
# Allowlisted units ARE attempted, and the exemption EXPIRES: if one of them starts
# producing an `.elf`, the run fails with "stale allowlist" and names the entry to
# delete. Otherwise the allowlist would be documentation formatted as code — a branch
# that never executes, whose entries nobody can distinguish from ones that outlived
# their reason. An exemption that cannot expire is a promise rather than a mechanism,
# which is precisely the distinction this script exists to enforce.
#
# Usage:  scripts/check-build-units-link.sh [--units "a b c"]
# Exit:   0 expected-linkable units linked AND every exemption is still warranted;
#         1 a new link failure or a stale exemption; 0 with a skip message if the
#         RISC-V toolchain is absent (mirrors the other guards).
set -uo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO"

# Units that MUST link — the verdict-family probes that MIRROR guest handlers,
# which is exactly the property that makes them go stale when a handler gains a new
# callee.
#
# `stateless_guest` is deliberately NOT here: `codegen-stateless-link-check.sh`
# already links it in the same CI group, and it is the most expensive link of the
# set. Pass it via --units to include it. That existing gate is also the reason this
# one exists — linking only the guest is the wrong SHAPE, not merely incomplete,
# because its scope silently narrows every time someone adds a build unit, whereas a
# per-unit list grows with the units rather than with anyone's memory.
#
# The known-nonlinkable units below are INCLUDED in this sweep on purpose. Listing
# an exemption without ever attempting the unit would make the allowlist
# documentation formatted as code: the branch would never execute, and nobody could
# tell a year from now whether the entry still describes reality or outlived its
# reason.
UNITS_DEFAULT="zisk_stateless_verdict zisk_stateless_verdict_v2 zisk_step2_verdict \
runtime_dispatcher runtime_dispatcher_call_probe zisk_runtime_access_list_seeded_sload"

# Structurally non-linkable; NOT failures. Reason recorded so a reader can tell an
# expected gap from a regression.
#
# THE EXEMPTION EXPIRES. If one of these starts producing an `.elf`, the run FAILS
# with "stale allowlist" and names the entry to delete. An exemption that cannot
# expire is a promise rather than a mechanism — which is the distinction this whole
# script exists to enforce, so it has to hold for the script's own exemptions too.
declare -A KNOWN_NONLINKABLE=(
  [runtime_dispatcher]="spliced into the guest; references bsr_addr_4788, account_extract_nonce and other cross-unit symbols (documented in scripts/gen-symbol-addresses.py)"
  [runtime_dispatcher_call_probe]="same family as runtime_dispatcher"
  [zisk_runtime_access_list_seeded_sload]="references evm_access_account_table / evm_access_account_count / runtime_access_account_seed from the guest closure"
)

UNITS="$UNITS_DEFAULT"
while [ $# -gt 0 ]; do
  case "$1" in
    --units) UNITS="${2:?--units needs a value}"; shift 2 ;;
    -h|--help) sed -n '2,40p' "$0"; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

if ! command -v riscv64-unknown-elf-ld >/dev/null 2>&1 \
   && ! command -v riscv64-elf-ld >/dev/null 2>&1; then
  echo "check-build-units-link: SKIP — no riscv64-{unknown-,}elf-ld on PATH"
  exit 0
fi

OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT

fail=0
for u in $UNITS; do
  rm -f "$OUT/$u.elf"
  log="$OUT/$u.log"
  lake exe codegen --program "$u" --halt linux93 -o "$OUT/$u" >"$log" 2>&1

  # The ELF's EXISTENCE is the check. codegen can exit 0 having written only the
  # .s/.o, which is the whole failure mode this script exists to catch -- so do not
  # trust the exit status here.
  #
  # Branch on the ALLOWLIST first, not on the .elf: an allowlisted unit that now
  # links must be reported as a stale exemption rather than silently reported OK.
  if [ -n "${KNOWN_NONLINKABLE[$u]+x}" ]; then
    if [ -f "$OUT/$u.elf" ]; then
      echo "  STALE    $u — this unit now LINKS; its allowlist entry is obsolete."
      echo "             delete KNOWN_NONLINKABLE[$u] in $0"
      echo "             (recorded reason, no longer true: ${KNOWN_NONLINKABLE[$u]})"
      fail=1
    else
      echo "  KNOWN    $u — ${KNOWN_NONLINKABLE[$u]}"
    fi
  elif [ -f "$OUT/$u.elf" ]; then
    echo "  OK       $u"
  else
    echo "  FAIL     $u — no .elf produced"
    grep -oE "undefined reference to \`[A-Za-z0-9_]+'" "$log" | sort -u | sed 's/^/             /'
    fail=1
  fi
done

if [ "$fail" -ne 0 ]; then
  echo "check-build-units-link: FAILED."
  echo "  FAIL  — a unit that mirrors guest handlers must also define every routine"
  echo "          those handlers call, and repeat any data section it does not inherit."
  echo "  STALE — an allowlisted unit started linking; delete its entry so the"
  echo "          exemption does not outlive its reason."
  exit 1
fi

echo "check-build-units-link: OK — expected-linkable units produced an .elf, and every"
echo "  allowlisted unit is still genuinely non-linkable."
