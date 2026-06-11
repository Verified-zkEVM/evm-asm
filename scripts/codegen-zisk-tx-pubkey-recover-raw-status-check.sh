#!/usr/bin/env bash
# codegen-zisk-tx-pubkey-recover-raw-status-check.sh
#
# Drive tx_pubkey_recover_raw over one transaction. The software secp256k1
# recovery backend is now implemented: a valid tx whose signature material and
# ecrecover ABI staging both succeed runs full ECDSA recovery (e = hash mod n,
# r_inv = r^-1 mod n, u1 = -e*r_inv, u2 = s*r_inv, Q = u1*G + u2*R) and the
# helper returns status 0 with the recovered 64-byte public key (BE x||y). A
# malformed/high-s tx surfaces the material failure class (status 10) with the
# underlying material status preserved in the side slot. This deliberately does
# NOT compare stateless public_keys; that lands in later children.
#
# COST: the recovery composes the ziskemu-accelerator-backed Secp256k1Field/
# Curve primitives (Arith256Mod modular multiply; Secp256k1Add/Dbl affine point
# ops), so ONE recovery is ~2e6 ziskemu steps. The success case stays behind
# RECOVER_RAW_FULL=1 (it rebuilds the signed-tx vector via execution-specs/
# coincurve) and is gated at the stateless guest's 1e9 step budget, so a
# regression past the budget fails this script (EmulationNoCompleted).
set -euo pipefail

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

echo "==> emit zisk_tx_pubkey_recover_raw_status ELF"
lake exe codegen --program zisk_tx_pubkey_recover_raw_status --halt linux93 \
  -o gen-out/zisk_tx_pubkey_recover_raw_status

REPO_ROOT="$(pwd)"

# run_case <name> <kind> <expected_status> <expected_material> <max_steps> <check_pubkey>
run_case() {
  local name="$1" kind="$2" expected_status="$3" expected_material="$4"
  local max_steps="$5" check_pubkey="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_pubkey_recover_raw_status_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_pubkey_recover_raw_status_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_tx_pubkey_recover_raw_status_${name}.expected_pub"

  uv run --directory execution-specs --quiet python3 - "$kind" "$in_file" "$exp_file" <<'PYVEC'
import rlp
import struct
import sys

import coincurve
from ethereum.crypto.hash import keccak256

kind, in_path, exp_path = sys.argv[1:4]
chain_id = 1
alice = bytes.fromhex("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
# Deterministic signer: private key = 1, so the recovered public key is the
# secp256k1 generator point G (well-known coordinates) -- an independent oracle.
priv = coincurve.PrivateKey(secret=bytes([0] * 31 + [1]))
expected_pub = priv.public_key.format(compressed=False)[1:]  # 64 bytes BE x||y

def write_input(tx: bytes) -> None:
    with open(in_path, "wb") as f:
        f.write(struct.pack("<Q", len(tx)))
        f.write(struct.pack("<Q", chain_id))
        f.write(tx)
        pad = (-(16 + len(tx))) % 8
        if pad:
            f.write(b"\x00" * pad)

def write_expected(pub: bytes) -> None:
    with open(exp_path, "wb") as f:
        f.write(pub)

if kind == "legacy_eip155":
    nonce, gas_price, gas, value, data = 42, 10**9, 21000, 10**18, b""
    signing_list = [nonce, gas_price, gas, alice, value, data, chain_id, 0, 0]
    msg_hash = keccak256(rlp.encode(signing_list))
    sig = priv.sign_recoverable(msg_hash, hasher=None)  # 65 bytes r||s||recid
    r = int.from_bytes(sig[0:32], "big")
    s = int.from_bytes(sig[32:64], "big")
    recid = sig[64]
    v = recid + 2 * chain_id + 35  # EIP-155 v
    tx = rlp.encode([nonce, gas_price, gas, alice, value, data, v, r, s])
    write_input(tx)
    write_expected(expected_pub)
elif kind == "bad_s_high":
    high_s = int(
        "7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a1",
        16,
    )
    fields = [chain_id, 42, 10**9, 2 * 10**9, 21000, alice, 10**18,
              b"", [], 1, 1, high_s]
    tx = bytes([2]) + rlp.encode(fields)
    write_input(tx)
    write_expected(b"\x00" * 64)
else:
    raise SystemExit(f"unknown kind: {kind}")
PYVEC

  "$ZISKEMU" -e gen-out/zisk_tx_pubkey_recover_raw_status.elf \
    -i "$in_file" -o "$out_file" -n "$max_steps" \
    >"$REPO_ROOT/gen-out/zisk_tx_pubkey_recover_raw_status_${name}.emu.log" 2>&1 || true

  python3 - "$out_file" "$exp_file" "$name" "$expected_status" "$expected_material" "$check_pubkey" <<'PYCHECK'
import struct
import sys

out_path, exp_path, name, expected_status, expected_material, check_pubkey = sys.argv[1:7]
data = open(out_path, "rb").read()

def u64(off):
    return struct.unpack("<Q", data[off:off+8])[0]

status = u64(0)
material = u64(8)
pubkey = data[16:80]
expected_status = int(expected_status)
expected_material = int(expected_material)

if status != expected_status:
    print(f"  {name:<20} FAIL status={status} expected={expected_status}")
    raise SystemExit(1)

if status == 10 and material != expected_material:
    print(f"  {name:<20} FAIL material={material} expected={expected_material}")
    raise SystemExit(1)

if check_pubkey == "1":
    expected_pub = open(exp_path, "rb").read()
    if pubkey != expected_pub:
        print(f"  {name:<20} FAIL pubkey={pubkey.hex()} expected={expected_pub.hex()}")
        raise SystemExit(1)
    print(f"  {name:<20} OK   status={status} pubkey={pubkey.hex()}")
else:
    print(f"  {name:<20} OK   status={status} material={material}")
PYCHECK
}

FAILED=0
# Fast default cases: material/stage routing only (no recovery).
# High-s tx: material rejects with status 43, surfaced as helper status 10.
run_case "bad_s_high" "bad_s_high" 10 43 10000000 0 || FAILED=1

if [[ "${RECOVER_RAW_FULL:-0}" == "1" ]]; then
  echo "==> RECOVER_RAW_FULL=1: running full recovery (~2e6 steps, gated at 1e9)"
  # Valid legacy EIP-155 tx signed by private key 1: recovery must return
  # status 0 and the secp256k1 generator point G as the recovered public key.
  # The 1e9 cap is the stateless guest step budget (evm-asm-mcogi.5.5).
  run_case "legacy_eip155" "legacy_eip155" 0 0 1000000000 1 || FAILED=1
else
  echo "==> (skipping full recovery success case; set RECOVER_RAW_FULL=1 to run it)"
fi

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_pubkey_recover_raw routes material/stage and (in full mode) recovers the public key"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
