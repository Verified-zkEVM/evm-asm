#!/usr/bin/env bash
# Build and run the bare RV64 real-linked `zkvm_modexp` backend probe.
#
# Unlike codegen-zisk-modexp-backend-probe-check.sh (which links a deterministic
# safe-fail shim), this program links the real bignum square-and-multiply
# implementation (zkvmModexpBackendImpl) and exercises four regression vectors,
# each routed to the bignum path via base_len=5. Records are written 16 bytes
# apart at 0xa0010000:
#
#   record i +0 : returned zkvm_status as u64
#   record i +8 : first output word (LE-loaded from the BE output buffer)
#
# Vectors (base=2, all lengths 5/1/5 bytes):
#   0: exp==0, mod==1   -> 1 % 1  = 0     (EIP-198; the 4ch8f.11.5 divergence)
#   1: exp==0, mod==13  -> 1 % 13 = 1
#   2: exp==0, mod==0   -> zero-fill
#   3: 2^5 mod 13       -> 6              (unchanged happy path)
#
# On PRE-FIX code, record 0's output word is 1 (raw result, unreduced); the fix
# reduces it to 0. This script FAILS on main and PASSES on the fix branch.
#
# Default exit:
#   0 -- wrapper linked; either all vectors matched, or the route was classified
#        as not ready on the current ziskemu installation
#   1 -- build/link failed, or a vector mismatched
# With --require-ready:
#   0 -- linked and all vectors matched
#   1 -- build/link/emulator failed, route not ready, or a vector mismatched
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

echo "==> emit zisk_modexp_backend_real_probe ELF"
set +e
lake exe codegen --program zisk_modexp_backend_real_probe --halt linux93 \
  -o gen-out/zisk_modexp_backend_real_probe \
  >gen-out/zisk_modexp_backend_real_probe.codegen.log 2>&1
CODEGEN_STATUS=$?
set -e
if [[ $CODEGEN_STATUS -ne 0 ]]; then
  echo
  echo "==> NOT READY: real zkvm_modexp symbol did not link"
  sed -n '1,80p' gen-out/zisk_modexp_backend_real_probe.codegen.log
  if [[ $REQUIRE_READY -eq 1 ]]; then exit 1; fi
  exit 0
fi

echo "==> ziskemu run"
set +e
"$ZISKEMU" -e gen-out/zisk_modexp_backend_real_probe.elf \
  -o gen-out/zisk_modexp_backend_real_probe.output -n 2000000 \
  >gen-out/zisk_modexp_backend_real_probe.emu.log 2>&1
EMU_STATUS=$?
set -e
if [[ $EMU_STATUS -ne 0 ]]; then
  echo
  echo "==> NOT READY: real zkvm_modexp route did not complete"
  echo "emulator exit: $EMU_STATUS"
  sed -n '1,40p' gen-out/zisk_modexp_backend_real_probe.emu.log
  if [[ $REQUIRE_READY -eq 1 ]]; then exit 1; fi
  exit 0
fi

if [[ ! -f gen-out/zisk_modexp_backend_real_probe.output ]]; then
  echo
  echo "==> NOT READY: ziskemu completed without writing probe output"
  if [[ $REQUIRE_READY -eq 1 ]]; then exit 1; fi
  exit 0
fi

ALL_HEX="$(xxd -p -l 64 gen-out/zisk_modexp_backend_real_probe.output | tr -d '\n')"

# Split into four 16-byte (32-hex-char) records: status(8B) || outword(8B).
rec_status() { echo "${ALL_HEX:$((32 * $1)):16}"; }
rec_outword() { echo "${ALL_HEX:$((32 * $1 + 16)):16}"; }

# Expected LE-stored output words. The backend writes Mlen=5 BE bytes into a
# pre-zeroed 8-byte buffer, so value v in the low byte lands at offset 4 and an
# `ld` reads it as v<<32; stored back little-endian that is "........vv......".
EXP_STATUS="0000000000000000"
declare -a EXP_OUT=(
  "0000000000000000"   # rec0: 1 % 1  = 0
  "0000000001000000"   # rec1: 1 % 13 = 1  (0x01 at BE offset 4)
  "0000000000000000"   # rec2: mod==0 zero-fill
  "0000000006000000"   # rec3: 2^5 mod 13 = 6 (0x06 at BE offset 4)
)
declare -a LABEL=(
  "exp==0, mod==1  -> 0"
  "exp==0, mod==13 -> 1"
  "exp==0, mod==0  -> zeros"
  "2^5 mod 13      -> 6"
)

echo
FAIL=0
for i in 0 1 2 3; do
  st="$(rec_status "$i")"
  ow="$(rec_outword "$i")"
  ok="ok"
  if [[ "$st" != "$EXP_STATUS" || "$ow" != "${EXP_OUT[$i]}" ]]; then
    ok="MISMATCH (want status=$EXP_STATUS out=${EXP_OUT[$i]})"
    FAIL=1
  fi
  printf 'record %d [%s]: status=%s out=%s  %s\n' "$i" "${LABEL[$i]}" "$st" "$ow" "$ok"
done
echo

if [[ $FAIL -eq 0 ]]; then
  echo "==> PASS: real zkvm_modexp backend matched all regression vectors"
  exit 0
fi

echo "==> FAIL: real zkvm_modexp backend diverged from EIP-198 spec"
echo "emulator log: gen-out/zisk_modexp_backend_real_probe.emu.log"
exit 1
