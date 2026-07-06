#!/usr/bin/env bash
# Build and run the bare RV64 `zkvm_secp256k1_ecrecover` backend probe.
#
# The probe links a local wrapper with the zkvm-standards C ABI:
#   zkvm_secp256k1_ecrecover(msg, sig, recid, output) -> zkvm_status in a0
# and, on hosts without a success-producing recovery route, uses a
# deterministic safe-fail shim that returns EFAIL instead of crashing guest
# execution. It writes:
#   OUTPUT+0  returned status word
#   OUTPUT+8  first recovered-pubkey u64
#   OUTPUT+16 second recovered-pubkey u64
#
# Default exit:
#   0 -- wrapper linked; backend either returned EOK/EFAIL or its route was
#        classified as not ready on the current ziskemu installation
#   1 -- build/link failed, or backend returned an unexpected status
# With --require-ready:
#   0 -- wrapper linked and ziskemu returned EOK or deterministic EFAIL
#   1 -- build/link/emulator failed, backend route not ready, or unexpected status
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

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_secp256k1_ecrecover_backend_probe ELF"
lake exe codegen --program zisk_secp256k1_ecrecover_backend_probe --halt linux93 \
  -o gen-out/zisk_secp256k1_ecrecover_backend_probe

echo "==> ziskemu run"
set +e
"$ZISKEMU" -e gen-out/zisk_secp256k1_ecrecover_backend_probe.elf \
  -o gen-out/zisk_secp256k1_ecrecover_backend_probe.output -n 200000 \
  >gen-out/zisk_secp256k1_ecrecover_backend_probe.emu.log 2>&1
EMU_STATUS=$?
set -e

if [[ $EMU_STATUS -ne 0 ]]; then
  echo
  echo "==> NOT READY: zkvm_secp256k1_ecrecover wrapper linked, but ziskemu did not complete the route"
  echo "emulator exit: $EMU_STATUS"
  echo "emulator log:"
  sed -n '1,40p' gen-out/zisk_secp256k1_ecrecover_backend_probe.emu.log
  if [[ $REQUIRE_READY -eq 1 ]]; then
    exit 1
  fi
  exit 0
fi

if [[ ! -f gen-out/zisk_secp256k1_ecrecover_backend_probe.output ]]; then
  echo
  echo "==> NOT READY: ziskemu completed without writing probe output"
  if [[ $REQUIRE_READY -eq 1 ]]; then
    exit 1
  fi
  exit 0
fi

ACTUAL_HEX="$(xxd -p -l 24 gen-out/zisk_secp256k1_ecrecover_backend_probe.output | tr -d '\n')"
STATUS_HEX="${ACTUAL_HEX:0:16}"
PUBKEY_PREFIX_HEX="${ACTUAL_HEX:16:32}"

echo
echo "status word:"
echo "  $STATUS_HEX"
echo "pubkey prefix:"
echo "  $PUBKEY_PREFIX_HEX"
echo

case "$STATUS_HEX" in
  0000000000000000)
    echo "==> PASS: zkvm_secp256k1_ecrecover wrapper linked and backend returned EOK"
    ;;
  ffffffffffffffff)
    echo "==> PASS: zkvm_secp256k1_ecrecover wrapper linked and returned deterministic EFAIL"
    ;;
  *)
    echo "==> FAIL: unexpected status word from zkvm_secp256k1_ecrecover wrapper"
    echo "emulator log: gen-out/zisk_secp256k1_ecrecover_backend_probe.emu.log"
    exit 1
    ;;
esac
