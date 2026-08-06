#!/usr/bin/env bash
# check-retired-predicates.sh — keep retired proof vocabulary out of EvmAsm.
#
# The persistent append-only storage-log assertion was retired in #11601.  A
# later reintroduction would compile cleanly but recreate the misleading
# container vocabulary that the retirement removed, so this is intentionally a
# source-level denylist rather than a registry or emitted-ELF check.
#
# Names may still be mentioned in documentation when wrapped in backticks;
# the gate is about declarations and uses, not the historical record of why the
# names were retired.  `--self-test` plants a declaration in a temporary Lean
# file and verifies that the scanner rejects it, so a green scan is not merely
# evidence that the name happens not to occur today.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

SCAN_DIR="EvmAsm"
FORBIDDEN=(
  storageLogIs
  storageLogIs_nil
  storageLogIs_cons
  storageLogIs_congr
  pcFree_storageLogIs
  storageLogLenIs
  PERSISTENT_STORAGE_LOG_BASE
)

mode="enforce"
case "${1:-}" in
  "")          mode="enforce" ;;
  --report)    mode="report" ;;
  --self-test) mode="self-test" ;;
  *)
    echo "usage: $0 [--report|--self-test]" >&2
    exit 2
    ;;
esac

alt="$(IFS='|'; echo "${FORBIDDEN[*]}")"

scan_dir() {
  local dir="$1"
  # Bound tokens by non-identifier/non-backtick characters.  Backtick-wrapped
  # prose is allowed, while line comments containing actual source tokens are
  # still rejected so comments cannot hide a copy-paste reintroduction.
  grep -rnE "(^|[^\`A-Za-z0-9_])(${alt})([^\`A-Za-z0-9_]|$)" \
      --include="*.lean" "$dir" 2>/dev/null \
    | grep -vE "\`(${alt})\`" \
    || true
}

if [[ "$mode" == "self-test" ]]; then
  tmp="$(mktemp -d)"
  trap 'rm -rf "$tmp"' EXIT
  mkdir -p "$tmp/planted" "$tmp/documented"
  printf 'def storageLogIs := True\n' > "$tmp/planted/RetiredPredicate.lean"
  planted="$(scan_dir "$tmp/planted")"
  if [[ -z "$planted" ]]; then
    echo "check-retired-predicates self-test FAILED: planted storageLogIs was not detected" >&2
    exit 1
  fi
  printf -- '-- `storageLogIs`\n' > "$tmp/documented/Documentation.lean"
  documented="$(scan_dir "$tmp/documented")"
  if [[ -n "$documented" ]]; then
    echo "check-retired-predicates self-test FAILED: backtick documentation was rejected" >&2
    exit 1
  fi
  echo "check-retired-predicates self-test: planted declaration rejected; backtick documentation allowed."
  exit 0
fi

hits="$(scan_dir "$SCAN_DIR")"

if [[ "$mode" == "report" ]]; then
  echo "== Retired-predicate scan over ${SCAN_DIR}/**.lean =="
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
check-retired-predicates FAILED: $n retired storage-log token(s) found in
${SCAN_DIR}/.

The persistent append-only storage-log proof vocabulary was retired in #11601.
Use the live map/transient vocabulary instead.  If this is historical prose,
wrap the retired name in backticks; otherwise remove the declaration or use.
==================================================================
EOF
  exit 1
fi

echo "check-retired-predicates: OK — no retired storage-log vocabulary in ${SCAN_DIR}/."
