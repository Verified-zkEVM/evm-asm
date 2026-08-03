#!/usr/bin/env bash
#
# check-layering.sh — enforce the repo's module-dependency boundaries as an
# architecture fitness function (report R-D1; Ford/Parsons).
#
# The kernel proves each theorem in isolation; it says nothing about the shape
# of the import graph. Architectural erosion (a high-trust layer reaching down
# into an unverified one, an acyclic boundary going circular) is exactly the
# kind of drift a fitness function should fence.
#
# INVARIANTS ENFORCED (hard fail):
#
#   L1. Codegen is a pure sink.
#       No verified-core module may `import EvmAsm.Codegen.*`. Codegen is the
#       RISC-V lowering + round-trip layer and is *unverified by design*
#       (docs/agent-progress-steering-review.md §6); the kernel-checked core
#       must never depend back on it, or the trust boundary leaks.
#       SCOPE IS CORE-BY-DEFAULT: EVERY file under EvmAsm/ is verified core
#       EXCEPT the explicitly non-core subtrees EvmAsm/{Codegen,Tests,Examples}
#       (Tests/Examples legitimately exercise Codegen). This deliberately
#       includes any NEW top-level EvmAsm/<X>/ dir, so a future module cannot
#       become an unscanned "laundering" hop that imports Codegen and is then
#       imported by core. (An allowlist of non-core dirs is safer than an
#       allowlist of core dirs: the default for the unknown is "is core".)
#       ONE EXEMPTION (GH #11042): the progress registry
#       (EvmAsm/Progress.lean, EvmAsm/Progress/**) MAY import Codegen, because
#       the guest routines it must witness for scripts/check-axioms.sh are
#       proved there. Sound only because L2 makes the registry a pure sink, so
#       there is no Codegen -> registry -> core path. Exempted edges are
#       printed on every run. See the block above L1 below.
#
#   L2. The progress registry is a pure sink.
#       Nothing under EvmAsm/** (outside EvmAsm/Progress*.lean itself) may
#       `import EvmAsm.Progress`. The registry observes the core; the core
#       must not observe the registry (else a tier edit could change what the
#       core elaborates).
#
#   L3. Core must not import the Tests/Examples escape hatches.
#       Tests/Examples are excluded from L1 (so they MAY import Codegen); to
#       stop them being a one-hop laundering path (core -> Tests -> Codegen),
#       no core file may import EvmAsm.Tests.* / EvmAsm.Examples.*.
#
# ADVISORY (reported, never fails): Rv64 should not import Evm64 — Rv64 is the
# lower RISC-V substrate beneath the Evm64 opcode layer. Exactly one bridge
# edge exists today (a tactic helper) and is allowlisted in RV64_EVM64_ALLOW.
#
# NOT ENFORCED — and deliberately so: there is NO clean EL/Rv64 layering. The
# RLP work spans both directions (EvmAsm/EL/RLP/{Program,ProgramSpec}.lean
# import Rv64, and EvmAsm/Rv64/RLP/Phase*.lean import EL). An "EL must not
# import Rv64" rule (floated in early planning) is therefore false against the
# tree and is intentionally absent.
#
# Usage:
#   scripts/check-layering.sh            # exit 1 on any L1/L2 violation
#   scripts/check-layering.sh --report   # always exit 0; print full state
#
# POSIX/bash; deps: grep. No build required (pure import scan).

set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

REPORT=0
[[ "${1:-}" == "--report" ]] && REPORT=1

# Allowlisted advisory bridge edges (Rv64 -> Evm64). One per line, repo-relative.
RV64_EVM64_ALLOW=(
  "EvmAsm/Rv64/Tactics/LiftSpec.lean"   # tactic helper; imports Evm64.Stack
)

fail=0

# Files making up the verified core: CORE-BY-DEFAULT — everything under
# EvmAsm/ EXCEPT the non-core subtrees (Codegen — unverified by design; Tests /
# Examples — may legitimately import Codegen). Their umbrella .lean files
# (EvmAsm/Codegen.lean etc.) are excluded too. Any other dir, including a
# future new one, is scanned. This closes the transitive-laundering hole: a new
# EvmAsm/<X>/ that imports Codegen is itself core, so its direct import fails.
core_files() {
  find EvmAsm \( \
       -path EvmAsm/Codegen  -o -path 'EvmAsm/Codegen/*'  -o -path EvmAsm/Codegen.lean  \
    -o -path EvmAsm/Tests    -o -path 'EvmAsm/Tests/*'    -o -path EvmAsm/Tests.lean    \
    -o -path EvmAsm/Examples -o -path 'EvmAsm/Examples/*' -o -path EvmAsm/Examples.lean \
    \) -prune -o -name '*.lean' -print
}

# ---- L1: Codegen is a pure sink ---------------------------------------
#
# EXEMPTION: the progress registry (EvmAsm/Progress.lean, EvmAsm/Progress/**)
# may import Codegen. This is narrow and it is sound ONLY because L2 holds
# (GH #11042).
#
# L1 exists so that a Codegen change cannot reach the kernel-checked core:
# the hazard is a module that imports Codegen AND is itself imported by core
# ("laundering"). The registry is the one place where the second half is
# impossible by construction — L2 below fails the build if anything under
# EvmAsm/** imports EvmAsm.Progress, so the registry is a pure sink and there
# is no path from Codegen through it into core.
#
# Why the edge is needed rather than merely convenient: the registry's job is
# to *witness* theorems so scripts/check-axioms.sh audits their trust base,
# and the verified guest routines are proved in Codegen
# (EvmAsm.Codegen.RlpEncodeUintBeSAsm.reub_spec_within is the whole-routine
# triple for rlp_encode_uint_be). Before #11042 no guest routine was in the
# registry at all, so this edge never had to exist — and the consequence was
# that a guest-routine spec could regress to sorryAx with the gate still
# green.
#
# ⚠️ If L2 is ever relaxed, this exemption must go with it: core -> Progress
# -> Codegen would then be exactly the laundering path L1 was written to stop.
# Exempted edges are PRINTED on every run, not silently skipped — an
# invisible exemption is how a fitness function erodes.
echo "== L1: Codegen is a pure sink (verified core must not import Codegen) =="
l1=0
l1_exempt=0
while IFS= read -r f; do
  hits="$(grep -nE '^import[[:space:]]+EvmAsm\.Codegen(\.|[[:space:]]|$)' "$f" 2>/dev/null || true)"
  [[ -z "$hits" ]] && continue
  case "$f" in
    EvmAsm/Progress.lean|EvmAsm/Progress/*)
      # Registry sink — allowed by the exemption above, but kept visible.
      echo "  EXEMPT (registry sink, sound via L2) $f imports Codegen:"
      echo "$hits" | sed -E 's/^/      /'
      l1_exempt=$((l1_exempt + 1))
      continue
      ;;
  esac
  echo "  VIOLATION $f imports Codegen:"
  echo "$hits" | sed -E 's/^/      /'
  l1=$((l1 + 1))
done < <(core_files)
(( l1 == 0 )) && echo "  (clean$( (( l1_exempt > 0 )) && printf ', %s exempt registry edge(s)' "$l1_exempt"))"
(( l1 > 0 )) && fail=$((fail + l1))

# ---- L2: Progress registry is a pure sink -----------------------------
echo "== L2: Progress registry is a pure sink (nothing imports EvmAsm.Progress) =="
l2=0
while IFS= read -r hit; do
  f="${hit%%:*}"
  case "$f" in
    EvmAsm/Progress.lean|EvmAsm/Progress/*) continue ;;  # the registry itself
  esac
  echo "  VIOLATION $f imports the progress registry:"
  echo "      ${hit#*:}"
  l2=$((l2 + 1))
done < <(grep -rnE '^import[[:space:]]+EvmAsm\.Progress(\.|[[:space:]]|$)' EvmAsm --include='*.lean' 2>/dev/null || true)
(( l2 == 0 )) && echo "  (clean)"
(( l2 > 0 )) && fail=$((fail + l2))

# ---- L3: core must not import the Tests/Examples escape hatches --------
# Tests/Examples are pruned from L1 so they MAY import Codegen. That makes them
# a one-hop laundering path: core -> Tests -> Codegen would leave core
# transitively depending on the unverified layer while L1's direct scan misses
# it. Forbidding core from importing Tests/Examples at all closes that hop.
echo "== L3: verified core must not import EvmAsm.Tests / EvmAsm.Examples =="
l3=0
while IFS= read -r f; do
  hits="$(grep -nE '^import[[:space:]]+EvmAsm\.(Tests|Examples)(\.|[[:space:]]|$)' "$f" 2>/dev/null || true)"
  if [[ -n "$hits" ]]; then
    echo "  VIOLATION $f imports a Tests/Examples escape hatch (which may import Codegen):"
    echo "$hits" | sed -E 's/^/      /'
    l3=$((l3 + 1))
  fi
done < <(core_files)
(( l3 == 0 )) && echo "  (clean)"
(( l3 > 0 )) && fail=$((fail + l3))

# ---- advisory: Rv64 -> Evm64 ------------------------------------------
echo "== advisory: Rv64 -> Evm64 (lower layer reaching up; allowlisted bridges OK) =="
is_allowed() { local x; for x in "${RV64_EVM64_ALLOW[@]}"; do [[ "$x" == "$1" ]] && return 0; done; return 1; }
adv=0
while IFS= read -r f; do
  if is_allowed "$f"; then
    (( REPORT )) && echo "  allowlisted $f"
  else
    echo "  ADVISORY    $f imports Evm64 and is not allowlisted (consider RV64_EVM64_ALLOW)"
    adv=$((adv + 1))
  fi
done < <(grep -rlE '^import[[:space:]]+EvmAsm\.Evm64(\.|[[:space:]]|$)' EvmAsm/Rv64 --include='*.lean' 2>/dev/null || true)
(( adv == 0 )) && echo "  (no un-allowlisted Rv64->Evm64 edges)"

echo
if (( REPORT )); then
  echo "check-layering: L1=$l1 L2=$l2 L3=$l3 advisory(Rv64->Evm64 un-allowlisted)=$adv (report mode, exit 0)"
  exit 0
fi
if (( fail > 0 )); then
  cat >&2 <<EOF
==================================================================
check-layering FAILED: $fail layering violation(s) above.
The verified core must not depend on the unverified Codegen layer
(L1), must not depend on the progress registry (L2), and must not
import the Tests/Examples escape hatches (L3). Move the shared
declaration down into a common dependency, or invert the edge.
==================================================================
EOF
  exit 1
fi
echo "check-layering: layering invariants hold. OK."
exit 0
