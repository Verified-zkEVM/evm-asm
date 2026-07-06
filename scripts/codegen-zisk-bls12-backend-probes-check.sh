#!/usr/bin/env bash
# Build and run all bare RV64 BLS12 backend wrapper probes.
#
# Default exit:
#   0 -- every wrapper links and each probe either completes with EOK/EFAIL or
#        is classified as not ready on the current ziskemu installation
#   1 -- build/link failed, or any backend returned an unexpected status
# With --require-ready:
#   0 -- every wrapper links and ziskemu completes with EOK or deterministic
#        EFAIL for every selector
#   1 -- any build/link/emulator/backend route is not ready, or unexpected status
set -euo pipefail

REQUIRE_READY=0
if [[ "${1:-}" == "--require-ready" ]]; then
  REQUIRE_READY=1
  shift
elif [[ $# -ne 0 ]]; then
  echo "usage: $0 [--require-ready]" >&2
  exit 1
fi

cd "$(dirname "$0")/.."

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

PROBES=(
  zisk_bls12_g1_add_backend_probe
  zisk_bls12_g1_msm_backend_probe
  zisk_bls12_g2_add_backend_probe
  zisk_bls12_g2_msm_backend_probe
  zisk_bls12_pairing_backend_probe
  zisk_bls12_map_fp_to_g1_backend_probe
  zisk_bls12_map_fp2_to_g2_backend_probe
)

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

not_ready=0
unexpected=0
ready=0

for probe in "${PROBES[@]}"; do
  echo
  echo "==> emit $probe ELF"
  lake exe codegen --program "$probe" --halt linux93 -o "gen-out/$probe"

  echo "==> ziskemu run $probe"
  set +e
  "$ZISKEMU" -e "gen-out/$probe.elf" \
    -o "gen-out/$probe.output" -n 200000 \
    >"gen-out/$probe.emu.log" 2>&1
  emu_status=$?
  set -e

  if [[ $emu_status -ne 0 ]]; then
    echo "  NOT READY: ziskemu did not complete ECALL route (exit $emu_status)"
    sed -n '1,12p' "gen-out/$probe.emu.log"
    not_ready=$((not_ready + 1))
    continue
  fi

  if [[ ! -f "gen-out/$probe.output" ]]; then
    echo "  NOT READY: ziskemu completed without writing probe output"
    not_ready=$((not_ready + 1))
    continue
  fi

  actual_hex="$(xxd -p -l 24 "gen-out/$probe.output" | tr -d '\n')"
  status_hex="${actual_hex:0:16}"
  result_prefix_hex="${actual_hex:16:32}"
  echo "  status:        $status_hex"
  echo "  result prefix: $result_prefix_hex"

  case "$status_hex" in
    0000000000000000|ffffffffffffffff)
      echo "  READY: wrapper linked and completed with EOK/EFAIL"
      ready=$((ready + 1))
      ;;
    *)
      echo "  FAIL: unexpected status word"
      echo "  emulator log: gen-out/$probe.emu.log"
      unexpected=$((unexpected + 1))
      ;;
  esac
done

echo
echo "==> BLS12 backend probe summary: ready=$ready not_ready=$not_ready unexpected=$unexpected total=${#PROBES[@]}"

if [[ "$unexpected" -ne 0 ]]; then
  exit 1
fi
if [[ "$REQUIRE_READY" -eq 1 && "$not_ready" -ne 0 ]]; then
  exit 1
fi
