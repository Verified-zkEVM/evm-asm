#!/usr/bin/env bash
# codegen-zisk-tx-pubkey-ecrecover-stage-material-check.sh
#
# Build tx_pubkey_signature_material and stage it into the ABI byte layout for
# zkvm_secp256k1_ecrecover(msg, sig, recid, output). This deliberately stops
# before recovery/comparison; the real backend route is tracked separately.
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

echo "==> emit zisk_tx_pubkey_ecrecover_stage_material ELF"
lake exe codegen --program zisk_tx_pubkey_ecrecover_stage_material --halt linux93 \
  -o gen-out/zisk_tx_pubkey_ecrecover_stage_material

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" kind="$2" expected_material_status="$3" expected_stage_status="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_pubkey_ecrecover_stage_material_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_pubkey_ecrecover_stage_material_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_tx_pubkey_ecrecover_stage_material_${name}.expected"

  uv run --directory execution-specs --quiet python3 - "$kind" "$in_file" "$exp_file" <<'PYVEC'
import json
import rlp
import struct
import sys

try:
    from Crypto.Hash import keccak
    def keccak256(data: bytes) -> bytes:
        h = keccak.new(digest_bits=256)
        h.update(data)
        return h.digest()
except Exception:
    import sha3
    def keccak256(data: bytes) -> bytes:
        return sha3.keccak_256(data).digest()

kind, in_path, exp_path = sys.argv[1:4]
chain_id = 1
alice = bytes.fromhex("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
auth_addr = bytes.fromhex("dededededededededededededededededededede")
r = 1
s = 2

def be32(x: int) -> bytes:
    return int(x).to_bytes(32, "big")

def write_input(tx: bytes) -> None:
    with open(in_path, "wb") as f:
        f.write(struct.pack("<Q", len(tx)))
        f.write(struct.pack("<Q", chain_id))
        f.write(tx)
        pad = (-(16 + len(tx))) % 8
        if pad:
            f.write(b"\x00" * pad)

def write_expected(status, tx_type=0, recid=0, r_value=0, s_value=0,
                   signing_hash=b"\x00" * 32, inner_off=0, is_eip155=0):
    with open(exp_path, "w") as f:
        json.dump({
            "status": status,
            "type": tx_type,
            "recid": recid,
            "r": be32(r_value).hex(),
            "s": be32(s_value).hex(),
            "hash": signing_hash.hex(),
            "inner_off": inner_off,
            "is_eip155": is_eip155,
        }, f)

if kind == "legacy_eip155":
    fields = [42, 10**9, 21000, alice, 10**18, b"", 37, r, s]
    tx = rlp.encode(fields)
    signing_hash = keccak256(rlp.encode(fields[:6] + [chain_id, 0, 0]))
    write_input(tx)
    write_expected(0, 0, 0, r, s, signing_hash, 0, 1)
elif kind == "eip1559":
    fields = [chain_id, 42, 10**9, 2 * 10**9, 21000, alice, 10**18,
              b"", [], 1, r, s]
    inner = rlp.encode(fields)
    tx = bytes([2]) + inner
    signing_hash = keccak256(bytes([2]) + rlp.encode(fields[:9]))
    write_input(tx)
    write_expected(0, 2, 1, r, s, signing_hash, 1, 0)
elif kind == "eip7702":
    fields = [chain_id, 42, 10**9, 2 * 10**9, 21000, alice, 10**18,
              b"", [], [[chain_id, auth_addr, 0, 1, r, s]], 0, r, s]
    inner = rlp.encode(fields)
    tx = bytes([4]) + inner
    signing_hash = keccak256(bytes([4]) + rlp.encode(fields[:10]))
    write_input(tx)
    write_expected(0, 4, 0, r, s, signing_hash, 1, 0)
elif kind == "bad_s_high":
    high_s = int(
        "7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a1",
        16,
    )
    fields = [chain_id, 42, 10**9, 2 * 10**9, 21000, alice, 10**18,
              b"", [], 1, r, high_s]
    tx = bytes([2]) + rlp.encode(fields)
    write_input(tx)
    write_expected(43)
else:
    raise SystemExit(f"unknown kind: {kind}")
PYVEC

  "$ZISKEMU" -e gen-out/zisk_tx_pubkey_ecrecover_stage_material.elf \
    -i "$in_file" -o "$out_file" -n 10000000 \
    >"$REPO_ROOT/gen-out/zisk_tx_pubkey_ecrecover_stage_material_${name}.emu.log" 2>&1 || true

  python3 - "$out_file" "$exp_file" "$name" "$expected_material_status" "$expected_stage_status" <<'PYCHECK'
import json
import struct
import sys

out_path, exp_path, name, expected_material_status, expected_stage_status = sys.argv[1:6]
data = open(out_path, "rb").read()
exp = json.load(open(exp_path))

def u64(off):
    return struct.unpack("<Q", data[off:off+8])[0]

material_status = u64(0)
stage_status = u64(136)
expected_material_status = int(expected_material_status)
expected_stage_status = int(expected_stage_status)
if material_status != expected_material_status or material_status != exp["status"]:
    print(f"  {name:<28} FAIL material_status={material_status} expected={expected_material_status}")
    raise SystemExit(1)

if material_status != 0:
    print(f"  {name:<28} OK   material_status={material_status} stage skipped")
    raise SystemExit(0)

actual = {
    "type": u64(8),
    "recid": u64(16),
    "r": data[24:56].hex(),
    "s": data[56:88].hex(),
    "hash": data[88:120].hex(),
    "inner_off": u64(120),
    "is_eip155": u64(128),
    "stage_status": stage_status,
    "stage_hash": data[144:176].hex(),
    "stage_sig": data[176:240].hex(),
    "stage_recid": u64(240),
    # ziskemu emits a fixed 256-byte public output for this probe, so only
    # the first 8 bytes of the 64-byte recovered-pubkey staging buffer are
    # observable at OUTPUT+248. The guest helper still zeroes all 64 bytes.
    "stage_pubkey_zero_prefix": data[248:256].hex(),
}

if stage_status != expected_stage_status:
    print(f"  {name:<28} FAIL stage_status={stage_status} expected={expected_stage_status}")
    raise SystemExit(1)

checks = {
    "type": exp["type"],
    "recid": exp["recid"],
    "r": exp["r"],
    "s": exp["s"],
    "hash": exp["hash"],
    "inner_off": exp["inner_off"],
    "is_eip155": exp["is_eip155"],
    "stage_hash": exp["hash"],
    "stage_sig": exp["r"] + exp["s"],
    "stage_recid": exp["recid"],
    "stage_pubkey_zero_prefix": "00" * 8,
}
bad = [k for k, v in checks.items() if actual[k] != v]
if bad:
    print(f"  {name:<28} FAIL mismatched {bad}")
    print("      actual  ", actual)
    print("      expected", checks)
    raise SystemExit(1)

print(f"  {name:<28} OK   material=0 stage=0 type={actual['type']} recid={actual['recid']}")
PYCHECK
}

FAILED=0
run_case "legacy_eip155" "legacy_eip155" 0 0 || FAILED=1
run_case "eip1559" "eip1559" 0 0 || FAILED=1
run_case "eip7702" "eip7702" 0 0 || FAILED=1
run_case "bad_s_high" "bad_s_high" 43 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_pubkey ecrecover staging preserves hash/signature/recid ABI bytes"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
