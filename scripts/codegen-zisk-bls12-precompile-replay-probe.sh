#!/usr/bin/env bash
# codegen-zisk-bls12-precompile-replay-probe.sh
#
# Probe whether the installed ziskemu exposes the precompile-result replay
# surface needed before bare codegen ELFs can drive deterministic BLS12
# accelerator tests. By default this is informational and exits 0 even when the
# replay surface is absent; pass --require-ready to make absence a failure.
set -euo pipefail

cd "$(dirname "$0")/.."

require_ready=0
if [[ "${1:-}" == "--require-ready" ]]; then
  require_ready=1
elif [[ $# -ne 0 ]]; then
  echo "usage: $0 [--require-ready]" >&2
  exit 2
fi

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else
    echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2
    exit 1
  fi
fi

ZISK_SOURCE="${ZISK_SOURCE:-}"
if [[ -z "$ZISK_SOURCE" ]]; then
  if [[ -d "$HOME/.zisk/zisk" ]]; then
    ZISK_SOURCE="$HOME/.zisk/zisk"
  elif [[ -d "$HOME/zisk" ]]; then
    ZISK_SOURCE="$HOME/zisk"
  fi
fi

echo "==> ziskemu: $ZISKEMU"

help_text="$("$ZISKEMU" --help 2>&1 || true)"
has_result_file_flag=0
has_cache_load_flag=0
if grep -Eq '(^|[[:space:]])-r[[:space:]]+<precompile_results_file>' <<<"$help_text"; then
  has_result_file_flag=1
fi
if grep -q -- '--precompile-cache-load' <<<"$help_text"; then
  has_cache_load_flag=1
fi

echo "precompile result file flag (-r): $has_result_file_flag"
echo "precompile cache load flag:       $has_cache_load_flag"

source_has_gated_flag=0
source_has_hint_results=0
source_has_bls_impl=0
if [[ -n "$ZISK_SOURCE" && -d "$ZISK_SOURCE" ]]; then
  echo "==> zisk source: $ZISK_SOURCE"
  if grep -Rqs 'ASM_PRECOMPILE_CACHE' "$ZISK_SOURCE/emulator-asm/src"; then
    source_has_gated_flag=1
  fi
  if grep -Rqs 'HINTS_TYPE_RESULT' "$ZISK_SOURCE/emulator-asm/src"; then
    source_has_hint_results=1
  fi
  if find "$ZISK_SOURCE/lib-c/c/src/bls12_381" -type f \( -name '*.cpp' -o -name '*.hpp' -o -name '*.h' \) -print -quit >/dev/null 2>&1; then
    source_has_bls_impl=1
  fi
else
  echo "==> zisk source: not found (set ZISK_SOURCE=...)"
fi

echo "source mentions ASM_PRECOMPILE_CACHE: $source_has_gated_flag"
echo "source parses HINTS_TYPE_RESULT:      $source_has_hint_results"
echo "source has BLS12 field routines:      $source_has_bls_impl"

echo
if [[ "$has_result_file_flag" -eq 1 || "$has_cache_load_flag" -eq 1 ]]; then
  echo "READY: installed ziskemu exposes a precompile replay/cache CLI surface."
  echo "Next step: add a linkable BLS12 G1 ADD probe that consumes deterministic replay data."
  exit 0
fi

echo "NOT READY: installed ziskemu does not expose the replay/cache flags needed"
echo "for deterministic BLS12 precompile-result tests from bare codegen ELFs."

if [[ "$source_has_gated_flag" -eq 1 || "$source_has_hint_results" -eq 1 ]]; then
  echo "The checked zisk source contains gated precompile-result plumbing; this"
  echo "likely needs a ziskemu build exposing ASM_PRECOMPILE_CACHE/precompile"
  echo "results, or an equivalent guest-callable replay path, before BLS12 runtime"
  echo "bodies call zkvm_bls12_* wrappers."
fi

if [[ "$require_ready" -eq 1 ]]; then
  exit 1
fi
exit 0
