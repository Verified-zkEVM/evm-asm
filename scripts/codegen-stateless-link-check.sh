#!/usr/bin/env bash
# codegen-stateless-link-check.sh -- link-only stateless_guest ELF gate.
#
# This is the CI-sized check for codegen closure drift: it emits, assembles,
# and links stateless_guest.elf, but does not run ziskemu or fetch EEST
# fixtures. It catches missing helper bodies that Lean can elaborate but the
# final RISC-V ELF linker cannot resolve.
set -euo pipefail

cd "$(dirname "$0")/.."

OUT_PREFIX="${CODEGEN_STATELESS_LINK_OUT:-gen-out/stateless-link-check/stateless_guest}"
NO_BUILD=0

usage() {
  cat <<'USAGE'
Usage:
  scripts/codegen-stateless-link-check.sh [options]

Options:
  --out PREFIX   output prefix for .s/.o/.elf files
  --no-build     skip `lake build codegen`
  -h, --help     show this help

Environment:
  CODEGEN_STATELESS_LINK_OUT  default output prefix
USAGE
}

require_arg() {
  local opt="$1"
  if [[ $# -lt 2 || -z "${2:-}" ]]; then
    echo "$opt requires an argument" >&2
    usage >&2
    exit 1
  fi
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) usage; exit 0 ;;
    --out) require_arg "$1" "${2:-}"; OUT_PREFIX="$2"; shift 2 ;;
    --no-build) NO_BUILD=1; shift ;;
    *) echo "unknown arg: $1" >&2; usage >&2; exit 1 ;;
  esac
done

mkdir -p "$(dirname "$OUT_PREFIX")"

if [[ "$NO_BUILD" -eq 0 ]]; then
  echo "==> lake build codegen"
  lake build codegen
fi

echo "==> emit and link stateless_guest ELF"
lake exe codegen --program stateless_guest --halt linux93 -o "$OUT_PREFIX"

if [[ ! -s "${OUT_PREFIX}.elf" ]]; then
  echo "missing linked ELF: ${OUT_PREFIX}.elf" >&2
  exit 1
fi

echo "==> PASS: linked ${OUT_PREFIX}.elf"
