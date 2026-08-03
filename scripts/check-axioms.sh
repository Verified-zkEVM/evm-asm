#!/usr/bin/env bash
#
# check-axioms.sh — kernel-truth audit of the trust base behind every
# theorem the progress registries (EvmAsm/Progress.lean, EvmAsm/Progress/Routines.lean) classify as
# `.proven`, `.conditional`, or `.partly`.
#
# Why this exists: PROGRESS.md historically advertised "axiom count = 0",
# but that number was produced by grepping for the literal `axiom`
# *keyword* in source (zero), which CANNOT see the trust axioms that
# `bv_decide` and `native_decide` *synthesize* per call. `#print axioms`
# (the Lean kernel's own answer) tells the truth: a solver-invoking
# `bv_decide` seals its result as `<owner>._native.bv_decide.ax_*`, and
# `native_decide` seals its as `<owner>._native.native_decide.ax_*`.
# Both rest on the native compiler path (`Lean.ofReduceBool` /
# `Lean.trustCompiler`) — see CLAUDE.md "No native_decide or bv_decide".
#
# Policy enforced here (updated 2026-06-02 — bv_decide tightened from ALLOWED
# to FORBIDDEN after the 290->0 elimination; was set 2026-06-01, see
# docs/agent-progress-steering-review.md R-C1):
#   * ALLOWED with no allowlist entry:
#       - the three classical axioms: propext, Classical.choice, Quot.sound
#   * FORBIDDEN unless grandfathered in scripts/axiom-allow.txt:
#       - bv_decide AND native_decide trust axioms
#         (`*._native.{bv_decide,native_decide}.ax_*`): both seal their result
#         behind the native compiler path (Lean.ofReduceBool /
#         Lean.trustCompiler) instead of a kernel-checked proof term. Both are
#         fully eliminated; the allowlist is an EMPTY burndown — any NEW such
#         owner fails the build. (Source-level use is also blocked earlier by
#         scripts/check-forbidden-tactics.sh.)
#   * ALWAYS FORBIDDEN (never allowlistable):
#       - sorryAx, Lean.ofReduceBool, Lean.trustCompiler appearing bare,
#         and any other axiom not covered above.
#
# Allowlist keying: by the *owning declaration* (the text before
# `._native.<tactic>.ax_*`), e.g. `EvmAsm.Evm64.SDiv.Compose.sdivCode_*`,
# not the volatile `_N_M` counter — so the burndown list is legible and
# stable across rebuilds. Editing a grandfathered proof may change its
# owner set; rerun `--write-allow` (with review) if so.
#
# Scope: the witness theorems bound by `:= @EvmAsm.…` abbrevs in the two
# registries — EvmAsm/Progress.lean (OpcodeEntry: opcodes plus the
# state-assertion vocabulary) and EvmAsm/Progress/Routines.lean
# (RoutineEntry: verified guest routines, GH #11042). Witnesses are
# discovered by grepping those abbrev bindings, not by tier, so the
# conditional tier needs no logic change here.
#
# The name pattern is namespace-agnostic. It was `@EvmAsm.Evm64.…` /
# `@EvmAsm.Stateless.…`, which could not match the guest surface at all
# (`EvmAsm.Codegen.…`, `EvmAsm.Rv64.…`) — so before #11042 a guest-routine
# spec could regress to `sorryAx` and this gate would stay green, because it
# was not looking at that theorem. What is REGISTERED is audited; what is not
# registered is still outside the gate, and the guest-routine registry is a
# partial enumeration of the verified guest surface (a broader sweep of all
# of EvmAsm/ remains future work).
#
# Usage:
#   scripts/check-axioms.sh                # enforce; exit 1 on a new
#                                          #   forbidden (native_decide) axiom
#   scripts/check-axioms.sh --report       # print full inventory, exit 0
#   scripts/check-axioms.sh --write-allow  # regenerate scripts/axiom-allow.txt
#                                          #   from the current closure
#
# Requires a built library (oleans) so `lake env lean` imports are cheap;
# CI runs it after `lake build`.
#
# POSIX/bash; deps: lake, grep, awk, sort, comm, mktemp.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

PROGRESS_LEAN="EvmAsm/Progress.lean"
ROUTINES_LEAN="EvmAsm/Progress/Routines.lean"
CORRESPOND_LEAN="EvmAsm/Progress/Correspondence.lean"
ALLOW_FILE="scripts/axiom-allow.txt"

mode="enforce"
case "${1:-}" in
  "")            mode="enforce" ;;
  --report)     mode="report" ;;
  --write-allow) mode="write-allow" ;;
  *) echo "usage: $0 [--report | --write-allow]" >&2; exit 2 ;;
esac

# --------------------------------------------------------------------
# 1. Witness theorem names — the abbrev sections of the two registries:
#    EvmAsm/Progress.lean (OpcodeEntry, EVM opcodes) and
#    EvmAsm/Progress/Routines.lean (RoutineEntry, verified guest routines,
#    GH #11042) and EvmAsm/Progress/Correspondence.lean (spec-correspondence
#    verdicts — it carries 4 `EvmAsm.Rv64.RLP.*` witness abbrevs that NO
#    previous version of this gate audited, which is the same #11042 gap one
#    file over).
#
#    This grep is deliberately INDEPENDENT of gen-axiom-witnesses.py: the
#    completeness check below compares names derived here against reports
#    parsed from the build log, so re-deriving them is what makes a
#    generator bug visible rather than self-confirming.
#
#    Namespace-agnostic on purpose (#11042). It used to be
#    `@EvmAsm\.(Evm64|Stateless)…`, which cannot match the guest surface —
#    `reub_spec_within` is `EvmAsm.Codegen.RlpEncodeUintBeSAsm.…` and 289
#    modules live under `EvmAsm.Rv64.*`. A witness outside those two
#    namespaces was silently skipped, leaving the gate green while covering
#    nothing.
#
#    Anchored on the abbrev's `:=` so prose in these files (which now
#    discusses witness names) is not mistaken for a declaration. Names are
#    flattened across newlines first because the wide abbrevs wrap:
#      private noncomputable abbrev _sdiv_witness :=
#        @EvmAsm.Evm64.SDiv.Compose.…
# --------------------------------------------------------------------
mapfile -t NAMES < <(
  cat "$PROGRESS_LEAN" "$ROUTINES_LEAN" "$CORRESPOND_LEAN" \
    | tr '\n' ' ' \
    | grep -oE ':=[[:space:]]*@EvmAsm\.[A-Za-z0-9_.]+' \
    | sed -E 's/^:=[[:space:]]*@//; s/\.+$//' \
    | LC_ALL=C sort -u
)
if (( ${#NAMES[@]} == 0 )); then
  echo "check-axioms: no witness theorems found in $PROGRESS_LEAN / $ROUTINES_LEAN / $CORRESPOND_LEAN" >&2
  exit 1
fi

# --------------------------------------------------------------------
# 2. Ask the kernel: `#print axioms` for each witness.
# --------------------------------------------------------------------
RAWOUT="$(mktemp)"
REGEN="$(mktemp)"
cleanup() { rm -f "$RAWOUT" "$REGEN"; }
trap cleanup EXIT

WITNESS_MODULE="EvmAsm.Progress.AxiomWitnesses"
WITNESS_FILE="EvmAsm/Progress/AxiomWitnesses.lean"

# GH #10601: the axiom audit is a checked-in witness module built by
# `lake build`, so it works when LAKE_ARTIFACT_CACHE satisfies the graph
# without materializing oleans (where `lake env lean` cannot resolve
# cache-satisfied modules — issue #10537).  The module carries one
# `#print axioms` line per registry witness and is generated from
# EvmAsm/Progress.lean and EvmAsm/Progress/Routines.lean by
# scripts/gen-axiom-witnesses.py; the registries are the single source of
# truth, so the module must regenerate identically.
if ! python3 scripts/gen-axiom-witnesses.py > "$REGEN"; then
  echo "check-axioms: gen-axiom-witnesses.py failed — output follows:" >&2
  cat "$REGEN" >&2
  exit 1
fi
if ! diff -q "$REGEN" "$WITNESS_FILE" >/dev/null; then
  echo "check-axioms: FAIL: $WITNESS_FILE is stale vs $PROGRESS_LEAN / $ROUTINES_LEAN / $CORRESPOND_LEAN" >&2
  echo "check-axioms: regenerate with: python3 scripts/gen-axiom-witnesses.py --write" >&2
  exit 1
fi

# Capture both streams (do NOT suppress stderr — a real build failure
# must surface).  `#print axioms` reports ride lake's message channel;
# lake replays recorded messages even when the module is satisfied from
# the artifact cache (measured on this checkout), so the reports are
# present on cached rebuilds too.
if ! lake build "$WITNESS_MODULE" > "$RAWOUT" 2>&1; then
  echo "check-axioms: 'lake build $WITNESS_MODULE' failed — output follows:" >&2
  cat "$RAWOUT" >&2
  exit 1
fi

# `lake build` prints each report as `info: <file>:<line>:<col>: <text>`
# (the axiom list may wrap onto space-indented continuation lines that carry
# no prefix).  Strip the position prefix so records match the classic
# `#print axioms` shape the parser below consumes — but ONLY for reports
# originating in the witness module.
#
# Scoping to $WITNESS_FILE is load-bearing: `#print axioms` reports ride
# lake's message channel and are REPLAYED for every module in the build graph,
# not just the one asked for.  A witness whose module carries its own
# `#print axioms` lines (e.g. WithdrawalDecodeClose5's wd* intermediate
# lemmas, #11291) would otherwise leak dozens of foreign reports into the
# parse, breaking the exact count match below.  The witness module is the
# single source of the gate's reports; anything a witness transitively depends
# on already shows up inside that witness's own (transitive) report, so
# dropping the foreign lines loses no coverage.
STRIPPED="$(mktemp)"
awk -v wf="$WITNESS_FILE" '
  {
    if (match($0, /^info: [^:]+:[0-9]+:[0-9]+: /)) {
      f = substr($0, 7); f = substr(f, 1, index(f, ":") - 1)
      if (f == wf) { keep = 1; print substr($0, RLENGTH + 1) }
      else         { keep = 0 }
    } else if ($0 ~ /^info:/) {
      keep = 0            # non-report info line (build progress) ends a block
    } else if ($0 ~ /^[ \t]/) {
      if (keep) print     # space-indented continuation of a kept report
    } else {
      keep = 0            # any other non-indented line ends the block
    }
  }
' "$RAWOUT" > "$STRIPPED"
mv "$STRIPPED" "$RAWOUT"

# Completeness (GH #10601): a summary line quoting the number of NAMES is
# not evidence the names were checked.  A sed pattern that stops matching
# a future lake output format, a moved message channel, or a truncated log
# would all yield zero parsed reports — and the gate would still print a
# pass quoting the count of names it INTENDED to check.  Compare the
# PARSED report records against the registry: every witness must produce
# exactly one record, else fail naming the missing witnesses.
mapfile -t REPORTED < <(
  awk '/^\x27/ {
         line = $0
         q1 = index(line, "\x27"); rest = substr(line, q1 + 1)
         q2 = index(rest, "\x27")
         print substr(rest, 1, q2 - 1)
       }' "$RAWOUT" | LC_ALL=C sort -u
)
if (( ${#REPORTED[@]} != ${#NAMES[@]} )) \
  || ! diff -q <(printf '%s\n' "${NAMES[@]}") <(printf '%s\n' "${REPORTED[@]}") >/dev/null; then
  echo "check-axioms: FAIL: parsed ${#REPORTED[@]} axiom report(s) for ${#NAMES[@]} registry witness(es)" >&2
  MISSING="$(comm -23 <(printf '%s\n' "${NAMES[@]}") <(printf '%s\n' "${REPORTED[@]}"))"
  if [[ -n "$MISSING" ]]; then
    echo "check-axioms: witnesses with no parsed report:" >&2
    echo "$MISSING" >&2
  fi
  exit 1
fi

# --------------------------------------------------------------------
# 3. Parse into THEOREM<TAB>AXIOM rows.
#    `#print axioms` prints either
#       'Name' depends on axioms: [a, b, c]      (list may wrap onto
#                                                  space-indented lines)
#    or  'Name' does not depend on any axioms
#    Collapse each record (continuations start with a space) to one line.
# --------------------------------------------------------------------
PAIRS="$(mktemp)"; trap 'cleanup; rm -f "$PAIRS"' EXIT
awk '
  /^\x27/ { if (buf != "") print buf; buf = $0; next }
          { buf = buf " " $0 }
  END     { if (buf != "") print buf }
' "$RAWOUT" | awk '
  {
    # theorem name: between the first pair of single quotes
    line = $0
    q1 = index(line, "\x27"); rest = substr(line, q1 + 1)
    q2 = index(rest, "\x27"); name = substr(rest, 1, q2 - 1)
    if (line !~ /depends on axioms:/) next     # "does not depend": skip
    lb = index(line, "[")
    axlist = substr(line, lb + 1)
    sub(/\].*$/, "", axlist)
    n = split(axlist, parts, ",")
    for (i = 1; i <= n; i++) {
      ax = parts[i]
      gsub(/[[:space:]]/, "", ax)
      gsub(/\xe2\x9c\x9d/, "", ax)            # strip the ✝ hygiene mark
      if (ax != "") print name "\t" ax
    }
  }
' > "$PAIRS"

# --------------------------------------------------------------------
# 4. Classify. owner = text before `._native.<tactic>.ax`.
# --------------------------------------------------------------------
classify() {  # stdin: THEOREM<TAB>AXIOM ; stdout: CLASS<TAB>OWNER<TAB>THEOREM<TAB>AXIOM
  awk -F'\t' '
    {
      thm = $1; ax = $2; cls = ""; owner = ax
      if (ax == "propext" || ax == "Classical.choice" || ax == "Quot.sound") {
        cls = "classical"
      } else if (ax ~ /\._native\.bv_decide\.ax/) {
        cls = "bv_decide"; sub(/\._native\.bv_decide\.ax.*$/, "", owner)
      } else if (ax ~ /\._native\.native_decide\.ax/) {
        cls = "native_decide"; sub(/\._native\.native_decide\.ax.*$/, "", owner)
      } else if (ax == "sorryAx" || ax ~ /sorryAx/) {
        cls = "sorry"
      } else if (ax ~ /ofReduceBool|trustCompiler/) {
        cls = "native_trust"
      } else {
        cls = "unknown"
      }
      print cls "\t" owner "\t" thm "\t" ax
    }
  '
}

CLASSED="$(mktemp)"; trap 'cleanup; rm -f "$PAIRS" "$CLASSED"' EXIT
classify < "$PAIRS" > "$CLASSED"

# Owners that currently carry a TCB-trust axiom (native_decide OR bv_decide).
# Both rest on the native compiler path (Lean.ofReduceBool / Lean.trustCompiler)
# and are now FORBIDDEN (both fully eliminated: native_decide 206->0,
# bv_decide 290->0). The allowlist (scripts/axiom-allow.txt) is an empty
# burndown that the gate fails against — any new such owner fails the build.
current_nd_owners() {
  awk -F'\t' '$1=="native_decide" || $1=="bv_decide" {print $2}' "$CLASSED" \
    | LC_ALL=C sort -u
}

# --------------------------------------------------------------------
# Modes
# --------------------------------------------------------------------
if [[ "$mode" == "write-allow" ]]; then
  tmp="$(mktemp)"
  {
    echo "# axiom-allow.txt — burndown list of pre-existing native_decide"
    echo "# trust-axiom OWNERS reaching witnessed proofs (see check-axioms.sh)."
    echo "# Each line is the owning declaration of a *._native.native_decide.ax_*"
    echo "# axiom that the kernel found in the closure of a .proven/.partly"
    echo "# witness. GOAL: drive this list to zero (replace native_decide with"
    echo "# kernel-checkable proofs). The gate FAILS on any owner NOT listed here."
    echo "# Regenerate with: scripts/check-axioms.sh --write-allow"
    echo "#"
    echo "# Generated $(date -u +%Y-%m-%d) from $PROGRESS_LEAN + $ROUTINES_LEAN + $CORRESPOND_LEAN witnesses."
    current_nd_owners
  } > "$tmp"
  mv "$tmp" "$ALLOW_FILE"
  echo "check-axioms: wrote $(current_nd_owners | grep -c . || true) owner(s) to $ALLOW_FILE"
  exit 0
fi

# Load allowlist (strip comments/blanks).
declare -A ALLOWED_OWNER=()
if [[ -f "$ALLOW_FILE" ]]; then
  while IFS= read -r line; do
    line="${line%%#*}"; line="${line//[[:space:]]/}"
    [[ -n "$line" ]] && ALLOWED_OWNER["$line"]=1
  done < "$ALLOW_FILE"
fi

if [[ "$mode" == "report" ]]; then
  echo "== Axiom inventory across ${#NAMES[@]} witnessed proofs =="
  echo
  echo "-- non-classical axioms by witness --"
  awk -F'\t' '$1!="classical"{print "  " $3 "  <-  [" $1 "] " $4}' "$CLASSED" \
    | LC_ALL=C sort -u || echo "  (none — all witnesses depend only on classical axioms)"
  echo
  echo "-- TCB-trust owners (FORBIDDEN: native_decide / bv_decide; allowlist $ALLOW_FILE) --"
  current_nd_owners | sed 's/^/  /' || true
  echo
  echo "(report mode — exit 0)"
  exit 0
fi

# --------------------------------------------------------------------
# enforce
# --------------------------------------------------------------------
violations=0

# (a) sorry / bare native-trust / unknown axioms — never allowed.
while IFS=$'\t' read -r cls owner thm ax; do
  [[ -z "$cls" ]] && continue
  case "$cls" in
    sorry)
      echo "  FORBIDDEN (sorry):        $thm  depends on  $ax" >&2
      violations=$((violations + 1)) ;;
    native_trust|unknown)
      echo "  FORBIDDEN ($cls):  $thm  depends on  $ax" >&2
      violations=$((violations + 1)) ;;
  esac
done < "$CLASSED"

# (b) native_decide owners must be grandfathered.
while IFS= read -r owner; do
  [[ -z "$owner" ]] && continue
  if [[ -z "${ALLOWED_OWNER[$owner]:-}" ]]; then
    # which witness pulls it in (first one, for the message)
    thm="$(awk -F'\t' -v o="$owner" '$1=="native_decide"&&$2==o{print $3; exit}' "$CLASSED")"
    echo "  NEW native_decide owner not in $ALLOW_FILE:" >&2
    echo "      owner:   $owner" >&2
    echo "      reaches: $thm" >&2
    violations=$((violations + 1))
  fi
done < <(current_nd_owners)

if (( violations > 0 )); then
  cat >&2 <<EOF

==================================================================
check-axioms FAILED: $violations new/forbidden trust axiom(s).

Policy: only the three classical axioms (propext, Classical.choice,
Quot.sound) are allowed. bv_decide / native_decide trust axioms and
sorry are FORBIDDEN. The allowlist $ALLOW_FILE is an empty burndown.

If you ADDED a bv_decide / native_decide (or a sorry), replace it with
a kernel-checkable proof (decide / omega / bv_omega / simp /
BitVec.eq_of_getLsbD_eq). If you intentionally moved a grandfathered
proof, rerun: scripts/check-axioms.sh --write-allow  (and have the
delta reviewed — it changes the trusted base).
==================================================================
EOF
  exit 1
fi

# Note stale allowlist entries (owner listed but no longer present) so the
# burndown list stays honest. Advisory only.
stale=0
for owner in "${!ALLOWED_OWNER[@]}"; do
  if ! current_nd_owners | grep -qxF "$owner"; then
    [[ "$stale" == 0 ]] && echo "check-axioms: NOTE — stale allowlist entries (no longer needed; prune from $ALLOW_FILE):"
    echo "  - $owner"
    stale=$((stale + 1))
  fi
done

nd_count="$(current_nd_owners | grep -c . || true)"
echo "check-axioms: OK — ${#NAMES[@]} witnesses; only classical axioms (propext, Classical.choice, Quot.sound), plus $nd_count grandfathered bv_decide/native_decide owner(s) in $ALLOW_FILE."
