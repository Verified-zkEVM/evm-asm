#!/usr/bin/env bash
# codegen-zisk-verify-public-keys-match-senders-check.sh
#
# Drive verify_public_keys_match_senders over a single-transaction SSZ
# `transactions` list and one supplied SEC1 public key. This mirrors
# execution-specs Amsterdam recover_sender_from_public_key applied to each
# transaction of a block: the supplied public_keys[i] must equal
# recover_transaction_public_key(chain_id, tx[i]).
#
# The helper walks the SSZ offset table to locate tx[0]=[offset[0],list_end)
# and delegates the per-transaction recover-and-compare to the already-verified
# tx_pubkey_public_key_matches. The prefix (status 2) and signature-material
# (status 10) classes are decided before the recovery, so they run in a small
# step budget; the match (0) and mismatch (1) cases require a full recovery.
#
# COST: one full recovery is ~2e6 ziskemu steps (accelerator-backed
# Secp256k1Field/Curve), so the match/mismatch cases stay behind
# RECOVER_RAW_FULL=1 and are gated at the stateless guest's 1e9 step budget.
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

echo "==> emit zisk_verify_public_keys_match_senders ELF"
lake exe codegen --program zisk_verify_public_keys_match_senders --halt linux93 \
  -o gen-out/zisk_verify_public_keys_match_senders

# run_case <name> <kind> <expected_status> <max_steps>
run_case() {
  local name="$1" kind="$2" expected_status="$3" max_steps="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_verify_public_keys_match_senders_${name}.input"

  uv run --directory execution-specs --quiet python3 - "$kind" "$in_file" <<'PYVEC'
import rlp
import struct
import sys

import coincurve
from ethereum.crypto.hash import keccak256

kind, in_path = sys.argv[1:3]
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

def legacy_create_eip155(nonce: int, data: bytes) -> bytes:
    # contract-creation (to == b"") with `data` bytes of init code; large data
    # pushes the EIP-155 signing payload past 55 bytes (the long-list RLP prefix
    # path that exercises tx_signing_hash_legacy_eip155's new_payload_len reuse).
    signing_list = [nonce, 10**9, 0x01000000, b"", 0, data, chain_id, 0, 0]
    msg_hash = keccak256(rlp.encode(signing_list))
    sig = priv.sign_recoverable(msg_hash, hasher=None)
    r = int.from_bytes(sig[0:32], "big")
    s = int.from_bytes(sig[32:64], "big")
    v = sig[64] + 2 * chain_id + 35
    return rlp.encode([nonce, 10**9, 0x01000000, b"", 0, data, v, r, s])

def ssz_tx_list(txs) -> bytes:
    # SSZ list of variable-length elements: a u32 LE offset table (one entry per
    # element, first = 4*count) followed by the concatenated element bytes.
    n = len(txs)
    offs, cur = [], 4 * n
    for t in txs:
        offs.append(cur)
        cur += len(t)
    return b"".join(struct.pack("<I", o) for o in offs) + b"".join(txs)

def write_input(txs, keys: bytes) -> None:
    # Layout: +0 tx_list_len, +8 chain_id, +16 tx_list_offset, +24 keys,
    # +tx_list_offset SSZ tx list. tx_list_offset is placed past the keys so an
    # N-key block does not collide with the list.
    tx_list = ssz_tx_list(txs)
    tlo = (24 + len(keys) + 7) & ~7
    with open(in_path, "wb") as f:
        f.write(struct.pack("<Q", len(tx_list)))  # +0  SSZ tx list byte length
        f.write(struct.pack("<Q", chain_id))      # +8  chain_id
        f.write(struct.pack("<Q", tlo))           # +16 tx-list offset
        f.write(keys)                             # +24 supplied public keys
        pad = tlo - (24 + len(keys))
        if pad:
            f.write(b"\x00" * pad)
        f.write(tx_list)                          # +tlo SSZ transactions list
        tail = (-(8 + tlo + len(tx_list))) % 8
        if tail:
            f.write(b"\x00" * tail)

if kind == "match":
    write_input([legacy_eip155_tx()], b"\x04" + expected_pub)
elif kind == "mismatch":
    wrong = bytearray(expected_pub)
    wrong[0] ^= 0x01            # flip one coordinate byte
    write_input([legacy_eip155_tx()], b"\x04" + bytes(wrong))
elif kind == "bad_prefix":
    write_input([legacy_eip155_tx()], b"\x02" + expected_pub)
elif kind == "material_fail":
    write_input([high_s_tx()], b"\x04" + expected_pub)
elif kind == "create_large_data":
    # EIP-155 contract-creation with 300 bytes of init code: the signing payload
    # crosses 55 bytes, exercising the long-list RLP prefix path. Regression for
    # the tx_signing_hash_legacy_eip155 new_payload_len clobber (bmvmx.3.2).
    write_input([legacy_create_eip155(0, bytes([0x33] * 300))], b"\x04" + expected_pub)
elif kind == "match2":
    # Two-tx block: exercises the offset-table walk for index > 0.
    write_input([legacy_eip155_tx(), legacy_create_eip155(1, bytes([0x33] * 300))],
                (b"\x04" + expected_pub) * 2)
else:
    raise SystemExit(f"unknown kind: {kind}")
PYVEC

  local out_file="$REPO_ROOT/gen-out/zisk_verify_public_keys_match_senders_${name}.output"
  "$ZISKEMU" -e gen-out/zisk_verify_public_keys_match_senders.elf \
    -i "$in_file" -o "$out_file" -n "$max_steps" \
    >"$REPO_ROOT/gen-out/zisk_verify_public_keys_match_senders_${name}.emu.log" 2>&1 || true

  python3 - "$out_file" "$name" "$expected_status" <<'PYCHECK'
import struct
import sys

out_path, name, expected_status = sys.argv[1:4]
data = open(out_path, "rb").read()
status = struct.unpack("<Q", data[0:8])[0]
expected_status = int(expected_status)
if status != expected_status:
    print(f"  {name:<16} FAIL status={status} expected={expected_status}")
    raise SystemExit(1)
print(f"  {name:<16} OK   status={status}")
PYCHECK
}

FAILED=0
# Fast default cases: offset-table walk + prefix/material routing (no recovery).
run_case "bad_prefix"    "bad_prefix"    2  10000000 || FAILED=1
run_case "material_fail" "material_fail" 10 10000000 || FAILED=1

if [[ "${RECOVER_RAW_FULL:-0}" == "1" ]]; then
  echo "==> RECOVER_RAW_FULL=1: running full recovery (~2e6 steps, gated at 1e9)"
  # Valid legacy EIP-155 tx signed by private key 1: the supplied G key matches
  # (status 0); a one-byte-flipped key mismatches (status 1).
  run_case "match"    "match"    0 1000000000 || FAILED=1
  run_case "mismatch" "mismatch" 1 1000000000 || FAILED=1
  # EIP-155 contract-creation with large init code (signing payload > 55 bytes):
  # before the tx_signing_hash_legacy_eip155 fix this ran past budget; now matches.
  run_case "create_large_data" "create_large_data" 0 1000000000 || FAILED=1
  # Two-tx block (offset-table walk for index > 0), second tx large-data creation.
  run_case "match2"   "match2"   0 1000000000 || FAILED=1
else
  echo "==> (skipping full match/mismatch cases; set RECOVER_RAW_FULL=1 to run them)"
fi

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: verify_public_keys_match_senders walks the tx list and (in full mode) recovers + compares each sender"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
