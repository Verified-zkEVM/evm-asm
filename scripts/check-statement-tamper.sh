#!/usr/bin/env bash
#
# check-statement-tamper.sh — surface the two highest-signal kinds of
# "make the build green by changing the goalposts" edit in a diff:
#
#   1. THEOREM-STATEMENT edits — a `theorem`/`lemma` *signature* removed or
#      changed (vs. only its proof body). The kernel happily re-proves a
#      *weakened* statement; only a human notices the spec got weaker.
#      This is the formal-methods analogue of editing the unit test to
#      match the bug. (Advisory: these are often legitimate; the point is
#      visibility for review — feeds the per-PR scorecard, R-B1.)
#
#   2. VERIFIER-CONFIG edits — changes to the things that DEFINE what
#      "passing" means: the gate scripts themselves, the axiom allowlist,
#      the conformance floor, the progress registry/tiers, the EEST
#      harness + pinned fixture tag, lakefile/toolchain, CI workflows.
#      A loosened verifier can hide a real regression. (Hard-failable
#      under --strict unless the HEAD commit says [allow-verifier-change].)
#
# This is a heuristic, not a proof; it reports, it does not block (by
# default). See docs/agent-progress-steering-review.md R-C2.
#
# Usage:
#   scripts/check-statement-tamper.sh                 # advisory; exit 0
#   scripts/check-statement-tamper.sh --base <ref>    # diff base (default:
#                                                     #   $GITHUB_BASE_REF or
#                                                     #   origin/main)
#   scripts/check-statement-tamper.sh --strict        # exit 1 on a
#                                                     #   verifier-config edit
#                                                     #   lacking the bypass token
#
# POSIX/bash; deps: git, grep, awk.

set -uo pipefail   # not -e: we tolerate git/grep non-matches

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

BASE=""
STRICT=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --base) BASE="$2"; shift 2 ;;
    --strict) STRICT=1; shift ;;
    *) echo "usage: $0 [--base <ref>] [--strict]" >&2; exit 2 ;;
  esac
done

# ---- resolve a base ref to diff against -------------------------------
if [[ -z "$BASE" ]]; then
  if [[ -n "${GITHUB_BASE_REF:-}" ]]; then
    BASE="origin/${GITHUB_BASE_REF}"
  else
    BASE="origin/main"
  fi
fi

resolve() {  # echo a usable commit-ish for $BASE, fetching best-effort if shallow
  if git rev-parse --verify --quiet "$BASE^{commit}" >/dev/null; then
    echo "$BASE"; return 0
  fi
  # Best-effort fetch for shallow CI checkouts; never fatal.
  local ref="${BASE#origin/}"
  git fetch --no-tags --depth=200 origin "$ref" >/dev/null 2>&1 || true
  if git rev-parse --verify --quiet "$BASE^{commit}" >/dev/null; then
    echo "$BASE"; return 0
  fi
  return 1
}

if ! BASE_OK="$(resolve)"; then
  echo "check-statement-tamper: base ref '$BASE' unavailable (shallow clone?); skipping. (advisory)"
  exit 0
fi
MERGE_BASE="$(git merge-base "$BASE_OK" HEAD 2>/dev/null || echo "$BASE_OK")"

mapfile -t CHANGED < <(git diff --name-only "$MERGE_BASE"...HEAD 2>/dev/null || true)
if (( ${#CHANGED[@]} == 0 )); then
  echo "check-statement-tamper: no changed files vs $BASE_OK. (advisory)"
  exit 0
fi

# ---- 1. theorem-statement edits --------------------------------------
HDR_RE='^[-+][[:space:]]*(private[[:space:]]+|protected[[:space:]]+|noncomputable[[:space:]]+|@\[[^]]*\][[:space:]]*)*(theorem|lemma)[[:space:]]'
stmt_hits=0
echo "== Theorem-statement edits (advisory — review for weakened specs) =="
for f in "${CHANGED[@]}"; do
  [[ "$f" == *.lean ]] || continue
  # Only signature lines that were REMOVED or MODIFIED (a '-' header line).
  removed="$(git diff "$MERGE_BASE"...HEAD -- "$f" 2>/dev/null \
    | grep -nE "$HDR_RE" | grep -E '^[0-9]+:-' || true)"
  if [[ -n "$removed" ]]; then
    echo "  $f:"
    echo "$removed" | sed -E 's/^[0-9]+:/    /'
    stmt_hits=$((stmt_hits + 1))
  fi
done
(( stmt_hits == 0 )) && echo "  (none)"

# ---- 2. verifier-config edits ----------------------------------------
is_verifier_config() {
  case "$1" in
    lakefile.toml|lean-toolchain) return 0 ;;
    scripts/check-*.sh) return 0 ;;
    scripts/axiom-allow.txt|scripts/conformance-baseline.txt) return 0 ;;
    scripts/approved-heartbeat-overrides.txt) return 0 ;;
    scripts/duplication-baseline.txt|scripts/jscpd.json) return 0 ;;
    scripts/churn-report.sh|scripts/cycles-append.sh) return 0 ;;
    scripts/eest-fixture-tag.txt) return 0 ;;
    scripts/codegen-eest-stateless-check.sh|scripts/eest-*.sh|scripts/eest-*.py) return 0 ;;
    scripts/progress-report.sh|scripts/check-progress.sh) return 0 ;;
    scripts/progress-snapshot.sh|scripts/progress-velocity.sh|scripts/progress-delta.sh) return 0 ;;
    EvmAsm/Progress.lean) return 0 ;;
    EvmAsm/EL/Conformance/*) return 0 ;;
    .github/workflows/*|.github/labeler.yml) return 0 ;;
    *) return 1 ;;
  esac
}

cfg_hits=()
for f in "${CHANGED[@]}"; do
  is_verifier_config "$f" && cfg_hits+=("$f")
done

echo
echo "== Verifier-config edits (these change what 'passing' means) =="
if (( ${#cfg_hits[@]} == 0 )); then
  echo "  (none)"
else
  printf '  %s\n' "${cfg_hits[@]}"
fi

# ---- verdict ----------------------------------------------------------
echo
if (( ${#cfg_hits[@]} > 0 )) && (( STRICT == 1 )); then
  if git log -1 --format='%B' HEAD 2>/dev/null | grep -qF '[allow-verifier-change]'; then
    echo "check-statement-tamper: verifier-config edits present, but HEAD carries [allow-verifier-change]. OK."
    exit 0
  fi
  cat >&2 <<EOF
==================================================================
check-statement-tamper (--strict) FAILED: this change edits
verifier configuration (listed above). A loosened verifier can hide
a real regression.

If intended, add the token [allow-verifier-change] to the HEAD commit
message (so the change is explicit and reviewable), or split the
config change into its own clearly-labelled PR.
==================================================================
EOF
  exit 1
fi

echo "check-statement-tamper: advisory scan complete (exit 0). Use --strict to gate verifier-config edits."
exit 0
