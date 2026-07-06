#!/usr/bin/env bash
# codegen-zisk-tx-pubkey-public-key-matches-check.sh
#
# Drive tx_pubkey_public_key_matches over one transaction and a supplied SEC1
# public key. This mirrors execution-specs Amsterdam
# transactions.recover_sender_from_public_key: the supplied public_key must
# equal recover_transaction_public_key(chain_id, tx).
#
# The helper checks the supplied 0x04 SEC1 prefix and the signature-material
# class BEFORE running the recovery, so the bad-prefix (status 2) and
# material-failure (status 10) cases are decided in a small step budget. The
# match (status 0) and mismatch (status 1) cases require a full recovery.
#
# COST: one full recovery composes the ziskemu-accelerator-backed
# Secp256k1Field/Curve primitives (Arith256Mod modular multiply;
# Secp256k1Add/Dbl affine point ops), so it is ~2e6 ziskemu steps. The
# match/mismatch cases stay behind RECOVER_RAW_FULL=1 (they rebuild signed-tx
# vectors via execution-specs/coincurve) and are gated at the stateless
# guest's 1e9 step budget, so a regression past the budget fails this script.
set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_tx_pubkey_public_key_matches_status ELF"
lake exe codegen --program zisk_tx_pubkey_public_key_matches_status --halt linux93 \
  -o gen-out/zisk_tx_pubkey_public_key_matches_status

# run_case <name> <kind> <expected_status> <max_steps> <check_pubkey>
run_case() {
  local name="$1" kind="$2" expected_status="$3" max_steps="$4" check_pubkey="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_pubkey_public_key_matches_status_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_pubkey_public_key_matches_status_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_tx_pubkey_public_key_matches_status_${name}.expected_pub"

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

def legacy_eip155_tx() -> bytes:
    nonce, gas_price, gas, value, data = 42, 10**9, 21000, 10**18, b""
    signing_list = [nonce, gas_price, gas, alice, value, data, chain_id, 0, 0]
    msg_hash = keccak256(rlp.encode(signing_list))
    sig = priv.sign_recoverable(msg_hash, hasher=None)  # 65 bytes r||s||recid
    r = int.from_bytes(sig[0:32], "big")
    s = int.from_bytes(sig[32:64], "big")
    recid = sig[64]
    v = recid + 2 * chain_id + 35  # EIP-155 v
    return rlp.encode([nonce, gas_price, gas, alice, value, data, v, r, s])

def high_s_tx() -> bytes:
    high_s = int(
        "7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a1",
        16,
    )
    fields = [chain_id, 42, 10**9, 2 * 10**9, 21000, alice, 10**18,
              b"", [], 1, 1, high_s]
    return bytes([2]) + rlp.encode(fields)

def write_input(tx: bytes, pubkey65: bytes) -> None:
    assert len(pubkey65) == 65
    with open(in_path, "wb") as f:
        f.write(struct.pack("<Q", len(tx)))      # +0  tx_len
        f.write(struct.pack("<Q", chain_id))     # +8  chain_id
        f.write(pubkey65)                        # +16 supplied public key (65)
        f.write(b"\x00" * (88 - 16 - 65))        # pad to +88 (8-byte aligned)
        f.write(tx)                              # +88 tx
        pad = (-(88 + len(tx))) % 8
        if pad:
            f.write(b"\x00" * pad)

def write_expected(pub: bytes) -> None:
    with open(exp_path, "wb") as f:
        f.write(pub)

if kind == "match":
    write_input(legacy_eip155_tx(), b"\x04" + expected_pub)
    write_expected(expected_pub)
elif kind == "mismatch":
    wrong = bytearray(expected_pub)
    wrong[0] ^= 0x01            # flip one coordinate byte
    write_input(legacy_eip155_tx(), b"\x04" + bytes(wrong))
    write_expected(b"\x00" * 64)
elif kind == "bad_prefix":
    # Valid tx, but the supplied key uses an unsupported (compressed) prefix.
    write_input(legacy_eip155_tx(), b"\x02" + expected_pub)
    write_expected(b"\x00" * 64)
elif kind == "material_fail":
    # High-s tx: signature material rejects before recovery; the supplied key
    # has a well-formed 0x04 prefix so the helper reaches recover_raw.
    write_input(high_s_tx(), b"\x04" + expected_pub)
    write_expected(b"\x00" * 64)
else:
    raise SystemExit(f"unknown kind: {kind}")
PYVEC

  "$ZISKEMU" -e gen-out/zisk_tx_pubkey_public_key_matches_status.elf \
    -i "$in_file" -o "$out_file" -n "$max_steps" \
    >"$REPO_ROOT/gen-out/zisk_tx_pubkey_public_key_matches_status_${name}.emu.log" 2>&1 || true

  python3 - "$out_file" "$exp_file" "$name" "$expected_status" "$check_pubkey" <<'PYCHECK'
import struct
import sys

out_path, exp_path, name, expected_status, check_pubkey = sys.argv[1:6]
data = open(out_path, "rb").read()

def u64(off):
    return struct.unpack("<Q", data[off:off+8])[0]

status = u64(0)
pubkey = data[16:80]
expected_status = int(expected_status)

if status != expected_status:
    print(f"  {name:<16} FAIL status={status} expected={expected_status}")
    raise SystemExit(1)

if check_pubkey == "1":
    expected_pub = open(exp_path, "rb").read()
    if pubkey != expected_pub:
        print(f"  {name:<16} FAIL pubkey={pubkey.hex()} expected={expected_pub.hex()}")
        raise SystemExit(1)
    print(f"  {name:<16} OK   status={status} pubkey={pubkey.hex()}")
else:
    print(f"  {name:<16} OK   status={status}")
PYCHECK
}

FAILED=0
# Fast default cases: prefix + material routing only (no recovery).
run_case "bad_prefix"    "bad_prefix"    2  10000000 0 || FAILED=1
run_case "material_fail" "material_fail" 10 10000000 0 || FAILED=1

if [[ "${RECOVER_RAW_FULL:-0}" == "1" ]]; then
  echo "==> RECOVER_RAW_FULL=1: running full recovery (~2e6 steps, gated at 1e9)"
  # Valid legacy EIP-155 tx signed by private key 1: the supplied G key matches
  # (status 0); a one-byte-flipped key mismatches (status 1).
  # The 1e9 cap is the stateless guest step budget (evm-asm-mcogi.5.5).
  run_case "match"    "match"    0 1000000000 1 || FAILED=1
  run_case "mismatch" "mismatch" 1 1000000000 0 || FAILED=1
else
  echo "==> (skipping full match/mismatch cases; set RECOVER_RAW_FULL=1 to run them)"
fi

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_pubkey_public_key_matches routes prefix/material and (in full mode) compares the recovered key"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
