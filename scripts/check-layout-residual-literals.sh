#!/usr/bin/env bash
# GH #11186: fail if retired layout literals reappear in production sources.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
cd "$root"
patterns='0xbdd80000|0xa2b20000|0xbe580000|0xbc377000|0xa1ba0000|0xa1ca0000|0xa1d20000|0xa1da0000|0xa1ea0000|0xa1f20000|0xa1fa0000|0xa27d0000'
fail=0
while IFS= read -r line; do
  case "$line" in
    *GuestAddrs.lean*|*RegionMapLinkPins.lean*|*symbol-addresses.tsv*) continue ;;
    *check-layout-residual*) continue ;;
    *BalAccountAccessDescriptors*|*Secp256k1Field*|*Bn254Fp2*|*BalStorageAccessDescriptors*) continue ;;
    *Placeholder*|*placeholder*) continue ;;
  esac
  echo "RESIDUAL: $line"
  fail=1
done < <(rg -n -g '!**/GuestAddrs.lean' -g '!**/RegionMapLinkPins.lean' -g '!**/symbol-addresses.tsv'   -e "$patterns" EvmAsm scripts 2>/dev/null || true)
while IFS= read -r line; do
  echo "RESIDUAL-SECTION: $line"
  fail=1
done < <(rg -n '0xa3000000|0xa3110000'   EvmAsm/Codegen/Driver.lean EvmAsm/Codegen/Cli.lean EvmAsm/Codegen/RegionMap.lean   EvmAsm/Codegen/CallFrameLayout.lean EvmAsm/Codegen/Programs/BlockVerdictParams.lean   EvmAsm/Codegen/Proofs/GuestImage.lean scripts/check-region-map.sh   scripts/gen-symbol-addresses.py 2>/dev/null || true)
if [[ $fail -ne 0 ]]; then
  echo "check-layout-residual-literals: FAIL"
  exit 1
fi
echo "check-layout-residual-literals: OK"
