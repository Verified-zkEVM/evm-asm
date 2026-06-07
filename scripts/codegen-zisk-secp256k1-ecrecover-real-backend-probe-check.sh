#!/usr/bin/env bash
# Probe the real linked zkvm_secp256k1_ecrecover backend without the local
# deterministic safe-fail wrapper used by codegen-zisk-secp256k1-ecrecover-backend-probe-check.sh.
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
REPO_ROOT="$(pwd)"
IN_FILE="$REPO_ROOT/gen-out/zisk_secp256k1_ecrecover_real_backend_probe.input"
OUT_FILE="$REPO_ROOT/gen-out/zisk_secp256k1_ecrecover_real_backend_probe.output"
EXP_FILE="$REPO_ROOT/gen-out/zisk_secp256k1_ecrecover_real_backend_probe.expected"
EMU_LOG="$REPO_ROOT/gen-out/zisk_secp256k1_ecrecover_real_backend_probe.emu.log"
CODEGEN_LOG="$REPO_ROOT/gen-out/zisk_secp256k1_ecrecover_real_backend_probe.codegen.log"

uv run --directory execution-specs --quiet python3 - "$IN_FILE" "$EXP_FILE" <<'VECTOR_PY'
import hashlib
import struct
import sys

import coincurve

in_file, exp_file = sys.argv[1], sys.argv[2]
priv = bytes.fromhex("0000000000000000000000000000000000000000000000000000000000000001")
msg = hashlib.sha256(b"evm-asm real ecrecover backend probe").digest()
key = coincurve.PrivateKey(priv)
sig = key.sign_recoverable(msg, hasher=None)
assert len(sig) == 65
pub = key.public_key.format(compressed=False)[1:]
with open(in_file, "wb") as f:
    f.write(msg)
    f.write(sig[:64])
    f.write(struct.pack("<Q", sig[64]))
with open(exp_file, "wb") as f:
    f.write(pub)
VECTOR_PY

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_secp256k1_ecrecover_real_backend_probe ELF"
set +e
lake exe codegen --program zisk_secp256k1_ecrecover_real_backend_probe --halt linux93 \
  -o gen-out/zisk_secp256k1_ecrecover_real_backend_probe >"$CODEGEN_LOG" 2>&1
CODEGEN_STATUS=$?
set -e
if [[ $CODEGEN_STATUS -ne 0 ]]; then
  echo
  echo "==> NOT READY: real zkvm_secp256k1_ecrecover symbol did not link"
  sed -n '1,80p' "$CODEGEN_LOG"
  if [[ $REQUIRE_READY -eq 1 ]]; then
    exit 1
  fi
  exit 0
fi

echo "==> ziskemu run"
set +e
"$ZISKEMU" -e gen-out/zisk_secp256k1_ecrecover_real_backend_probe.elf \
  -i "$IN_FILE" -o "$OUT_FILE" -n 1000000 >"$EMU_LOG" 2>&1
EMU_STATUS=$?
set -e
if [[ $EMU_STATUS -ne 0 ]]; then
  echo
  echo "==> NOT READY: real zkvm_secp256k1_ecrecover route did not complete"
  echo "emulator exit: $EMU_STATUS"
  sed -n '1,80p' "$EMU_LOG"
  if [[ $REQUIRE_READY -eq 1 ]]; then
    exit 1
  fi
  exit 0
fi

if [[ ! -f "$OUT_FILE" ]]; then
  echo
  echo "==> NOT READY: ziskemu completed without writing probe output"
  if [[ $REQUIRE_READY -eq 1 ]]; then
    exit 1
  fi
  exit 0
fi

STATUS_HEX="$(xxd -p -l 8 "$OUT_FILE" | tr -d '\n')"
PUBKEY_HEX="$(dd if="$OUT_FILE" bs=1 skip=8 count=64 2>/dev/null | xxd -p | tr -d '\n')"
EXPECTED_HEX="$(xxd -p "$EXP_FILE" | tr -d '\n')"

echo
echo "status word:"
echo "  $STATUS_HEX"
echo "recovered pubkey:"
echo "  ${PUBKEY_HEX:0:32}..${PUBKEY_HEX: -32}"
echo "expected pubkey:"
echo "  ${EXPECTED_HEX:0:32}..${EXPECTED_HEX: -32}"
echo

if [[ "$STATUS_HEX" != "0000000000000000" ]]; then
  echo "==> NOT READY: real zkvm_secp256k1_ecrecover returned nonzero status"
  if [[ $REQUIRE_READY -eq 1 ]]; then
    exit 1
  fi
  exit 0
fi

if [[ "$PUBKEY_HEX" == "$EXPECTED_HEX" ]]; then
  echo "==> PASS: real zkvm_secp256k1_ecrecover recovered the expected public key"
  exit 0
fi

echo "==> FAIL: real zkvm_secp256k1_ecrecover returned status 0 with wrong pubkey"
echo "emulator log: $EMU_LOG"
exit 1
