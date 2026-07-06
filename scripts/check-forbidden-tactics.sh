#!/usr/bin/env bash
#
# check-forbidden-tactics.sh — source-level gate forbidding proof tactics that
# expand the trusted computing base (TCB).
#
# Why this exists: the project's correctness guarantee is that every proof is
# *kernel-checkable* — the Lean kernel re-checks each proof term against only
# the three classical axioms (`propext`, `Classical.choice`, `Quot.sound`).
# A handful of tactics break that guarantee by sealing their result behind a
# trust axiom that rests on the native compiler path
# (`Lean.ofReduceBool` / `Lean.trustCompiler`) instead of a kernel-checked
# proof term:
#
#   * `native_decide` — trusts arbitrary compiled `Decidable` evaluation.
#   * `bv_decide`      — reflects an LRAT checker run via native evaluation.
#
# Both were fully eliminated from this repo (native_decide 206 -> 0,
# bv_decide 290 -> 0). This gate keeps them out: it FAILS the build if any
# `.lean` source under EvmAsm/ invokes a forbidden tactic.
#
# Relationship to scripts/check-axioms.sh: that script is the *kernel-truth*
# backstop — it runs `#print axioms` on the witnessed proofs and rejects any
# non-classical axiom (sorryAx, ofReduceBool, trustCompiler, native_decide /
# bv_decide trust axioms, or anything unknown). This script is the *source*
# pre-filter: it is fast, scans ALL of EvmAsm/ (not just the witnessed
# surface), and catches even a `bv_decide` call that the normalizer happens to
# close without emitting an axiom (axiom-neutral, but still policy-forbidden).
# The two gates are complementary; CI runs both.
#
# Policy (CLAUDE.md "No native_decide or bv_decide"):
#   FORBIDDEN as tactic invocations anywhere in EvmAsm/**.lean:
#     native_decide, bv_decide
#   To extend the list, add tokens to FORBIDDEN below (and document why).
#
# Doc mentions are allowed: a reference written inside backticks (e.g.
# "Replaces `bv_decide`") or in a `--` line comment is NOT flagged. A real
# tactic invocation is never backtick-wrapped, so this distinguishes prose
# from code. (If you must mention a forbidden tactic in prose, wrap it in
# backticks.)
#
# Usage:
#   scripts/check-forbidden-tactics.sh           # enforce; exit 1 on any hit
#   scripts/check-forbidden-tactics.sh --report  # list hits, exit 0
#
# POSIX/bash; deps: grep. No build required (pure source scan).

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

# Tactics that expand the TCB by sealing results behind a native-compiler
# trust axiom instead of a kernel-checked proof term.
FORBIDDEN=(native_decide bv_decide)

SCAN_DIR="EvmAsm"

mode="enforce"
case "${1:-}" in
  "")        mode="enforce" ;;
  --report)  mode="report" ;;
  *) echo "usage: $0 [--report]" >&2; exit 2 ;;
esac

# Build an alternation of the forbidden tokens.
alt="$(IFS='|'; echo "${FORBIDDEN[*]}")"

# A hit is the token bounded by non-identifier, non-backtick chars (so it is a
# real tactic token, not a substring and not a `backtick-quoted` doc mention),
# and the line is not a `--` line comment.
hits="$(
  grep -rnE "(^|[^\`A-Za-z_])(${alt})([^\`A-Za-z_]|\$)" --include="*.lean" "$SCAN_DIR" 2>/dev/null \
    | grep -vE "\`(${alt})\`" \
    | grep -vE '^[^:]*:[0-9]+:[[:space:]]*--' \
    || true
)"

if [[ "$mode" == "report" ]]; then
  echo "== Forbidden-tactic scan over ${SCAN_DIR}/**.lean =="
  echo "   forbidden: ${FORBIDDEN[*]}"
  echo
  if [[ -n "$hits" ]]; then echo "$hits"; else echo "  (none)"; fi
  echo
  echo "(report mode — exit 0)"
  exit 0
fi

if [[ -n "$hits" ]]; then
  echo "$hits" >&2
  n="$(printf '%s\n' "$hits" | grep -c . || true)"
  cat >&2 <<EOF

==================================================================
check-forbidden-tactics FAILED: $n invocation(s) of a TCB-expanding
tactic (${FORBIDDEN[*]}) found in ${SCAN_DIR}/.

These tactics seal their result behind a native-compiler trust axiom
(Lean.ofReduceBool / Lean.trustCompiler) instead of a kernel-checked
proof term, breaking the project's kernel-checkable guarantee.

Replace with a kernel-checkable proof (decide / omega / bv_omega /
simp / BitVec.eq_of_getLsbD_eq / etc.). See CLAUDE.md
("No native_decide or bv_decide") and scripts/check-axioms.sh.
If you only meant to MENTION the tactic in prose, wrap it in
\`backticks\`.
==================================================================
EOF
  exit 1
fi

echo "check-forbidden-tactics: OK — no ${FORBIDDEN[*]} invocations in ${SCAN_DIR}/."
