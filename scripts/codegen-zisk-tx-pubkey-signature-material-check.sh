#!/usr/bin/env bash
# codegen-zisk-tx-pubkey-signature-material-check.sh
#
# Route one encoded transaction to its canonical public-key verification
# material: tx type, recovery id, r, s, and signing hash.
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

echo "==> emit zisk_tx_pubkey_signature_material ELF"
lake exe codegen --program zisk_tx_pubkey_signature_material --halt linux93 \
  -o gen-out/zisk_tx_pubkey_signature_material

REPO_ROOT="$(pwd)"

# run_case <name> <kind> <expected_status>
run_case() {
  local name="$1" kind="$2" expected_status="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_pubkey_signature_material_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_pubkey_signature_material_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_tx_pubkey_signature_material_${name}.expected"

  uv run --directory execution-specs --quiet python3 - "$kind" "$in_file" "$exp_file" <<'PY'
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
PY

  "$ZISKEMU" -e gen-out/zisk_tx_pubkey_signature_material.elf \
    -i "$in_file" -o "$out_file" -n 10000000 \
    >"$REPO_ROOT/gen-out/zisk_tx_pubkey_signature_material_${name}.emu.log" 2>&1 || true

  python3 - "$out_file" "$exp_file" "$name" "$expected_status" <<'PY'
import json
import struct
import sys

out_path, exp_path, name, expected_status = sys.argv[1:5]
data = open(out_path, "rb").read()
exp = json.load(open(exp_path))

def u64(off):
    return struct.unpack("<Q", data[off:off+8])[0]

actual = {
    "status": u64(0),
    "type": u64(8),
    "recid": u64(16),
    "r": data[24:56].hex(),
    "s": data[56:88].hex(),
    "hash": data[88:120].hex(),
    "inner_off": u64(120),
    "is_eip155": u64(128),
}

expected_status = int(expected_status)
if actual["status"] != expected_status or actual["status"] != exp["status"]:
    print(f"  {name:<28} FAIL status={actual['status']} expected={expected_status}")
    raise SystemExit(1)

if actual["status"] == 0:
    fields = ["type", "recid", "r", "s", "hash", "inner_off", "is_eip155"]
    bad = [k for k in fields if actual[k] != exp[k]]
    if bad:
        print(f"  {name:<28} FAIL mismatched {bad}")
        print("      actual  ", actual)
        print("      expected", exp)
        raise SystemExit(1)

print(f"  {name:<28} OK   status={actual['status']} type={actual['type']} recid={actual['recid']}")
PY
}

FAILED=0
run_case "legacy_eip155" "legacy_eip155" 0 || FAILED=1
run_case "eip1559" "eip1559" 0 || FAILED=1
run_case "eip7702" "eip7702" 0 || FAILED=1
run_case "bad_s_high" "bad_s_high" 43 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_pubkey_signature_material routes tx signature material"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
