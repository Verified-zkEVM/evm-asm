#!/usr/bin/env bash
#
# port-check.sh — single-command acceptance gate for a routine-port file.
#
#   scripts/port-check.sh EvmAsm/Stateless/<Area>/<Routine>SAsm.lean
#
# Green means the file meets the delivery checklist of
# docs/agents/port-playbook.md (and sasm-howto §9) file-locally:
#
#   1. `lake build <module>` succeeds.
#   2. Re-elaboration is WARNING-FREE (zero-warning policy).
#   3. No forbidden tactics / TCB bumps in the source
#      (native_decide, bv_decide, maxHeartbeats/maxRecDepth raises, sorry).
#   4. Every theorem in the module kernel-depends only on the three
#      classical axioms (scripts/port_check_axioms.lean).
#   5. Advisory: #guard pins present (length / position-independence).
#
# It does NOT replace the EEST A/B run — required whenever emitted code
# changes (sasm-howto §7.6).
set -uo pipefail

FILE="${1:-}"
if [[ -z "$FILE" || ! -f "$FILE" ]]; then
  echo "usage: scripts/port-check.sh <path/to/File.lean>" >&2
  exit 2
fi
case "$FILE" in
  *.lean) ;;
  *) echo "port-check: not a .lean file: $FILE" >&2; exit 2 ;;
esac

MOD="${FILE%.lean}"
MOD="${MOD//\//.}"
FAIL=0

step() { printf '\n== %s\n' "$1"; }

# ---------------------------------------------------------------- 1. build
step "1/5 lake build $MOD"
if ! lake build "$MOD" >/tmp/port-check-build.$$ 2>&1; then
  cat /tmp/port-check-build.$$
  echo "port-check: BUILD FAILED"
  rm -f /tmp/port-check-build.$$
  exit 1
fi
tail -2 /tmp/port-check-build.$$
rm -f /tmp/port-check-build.$$

# ------------------------------------------------------- 2. zero warnings
step "2/5 warning-free re-elaboration"
ELAB_OUT="$(lake env lean "$FILE" 2>&1)"
# `#print axioms foo` emits informational lines. Those are part of the port
# checklist, so allow the classical-only forms and still fail on warnings/errors.
ELAB_BAD="$(printf '%s\n' "$ELAB_OUT" | grep -vE "^'[^']+' depends on axioms: \[(propext, )?(Classical\.choice, )?Quot\.sound\]$" || true)"
if [[ -n "$ELAB_BAD" ]]; then
  echo "$ELAB_OUT"
  echo "port-check: FAIL — output (warnings/errors) during elaboration"
  FAIL=1
elif [[ -n "$ELAB_OUT" ]]; then
  echo "OK (only classical #print axioms output)"
else
  echo "OK (no output)"
fi

# ------------------------------------------- 3. forbidden-source scan
step "3/5 forbidden tactics / TCB bumps / sorry"
BAD_LINES="$(grep -nE '(^|[^[:alnum:]_`])(native_decide|bv_decide)([^[:alnum:]_`]|$)|set_option[[:space:]]+(maxHeartbeats|maxRecDepth)[[:space:]]+[0-9]{6,}' "$FILE" \
  | grep -vE '^\s*[0-9]+:\s*(--|/-|\*|\s*-)' || true)"
SORRY_LINES="$(grep -nE '(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)' "$FILE" \
  | grep -vE '\-\-|/\-|^\s*[0-9]+:\s*\*' || true)"
if [[ -n "$BAD_LINES$SORRY_LINES" ]]; then
  [[ -n "$BAD_LINES" ]] && { echo "forbidden tactic / TCB bump:"; echo "$BAD_LINES"; }
  [[ -n "$SORRY_LINES" ]] && { echo "sorry:"; echo "$SORRY_LINES"; }
  echo "port-check: FAIL"
  FAIL=1
else
  echo "OK"
fi

# --------------------------------------------------- 4. kernel axiom audit
step "4/5 kernel axiom audit ($MOD)"
if ! lake env lean --run scripts/port_check_axioms.lean "$MOD"; then
  echo "port-check: FAIL — non-classical axioms"
  FAIL=1
fi

# --------------------------------------------------- 5. advisory guard pins
step "5/5 #guard pins (advisory)"
NGUARD="$(grep -c '^#guard' "$FILE" || true)"
if [[ "$NGUARD" -eq 0 ]]; then
  echo "WARNING: no #guard pins found — ports should pin emitted length and"
  echo "         position-independence (flatten 0 = flatten 0x80000000); see playbook Step 1."
else
  echo "OK ($NGUARD pins)"
fi

echo
if [[ "$FAIL" -ne 0 ]]; then
  echo "port-check: FAILED — fix the items above."
  exit 1
fi
echo "port-check: PASS ($FILE)"
echo "Reminder: if emitted code changed, run the EEST A/B (sasm-howto §7.6)."
