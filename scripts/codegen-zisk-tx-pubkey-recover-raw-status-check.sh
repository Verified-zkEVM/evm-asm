#!/usr/bin/env bash
# codegen-zisk-tx-pubkey-recover-raw-status-check.sh
#
# Drive tx_pubkey_recover_raw over one transaction. The software secp256k1
# recovery backend is not implemented yet, so a valid tx whose signature
# material and ecrecover ABI staging both succeed must reach status 50
# (backend stub), and a malformed/high-s tx must surface the material failure
# class (status 10) with the underlying material status preserved in the side
# slot. This deliberately does NOT recover a key or compare stateless
# public_keys; those land in later children.
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

run_case() {
  local name="$1" kind="$2" expected_status="$3" expected_material="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_pubkey_recover_raw_status_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_pubkey_recover_raw_status_${name}.output"

  uv run --directory execution-specs --quiet python3 - "$kind" "$in_file" <<'PYVEC'
import rlp
import struct
import sys

kind, in_path = sys.argv[1:3]
chain_id = 1
alice = bytes.fromhex("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
auth_addr = bytes.fromhex("dededededededededededededededededededede")
r = 1
s = 2

def write_input(tx: bytes) -> None:
    with open(in_path, "wb") as f:
        f.write(struct.pack("<Q", len(tx)))
        f.write(struct.pack("<Q", chain_id))
        f.write(tx)
        pad = (-(16 + len(tx))) % 8
        if pad:
            f.write(b"\x00" * pad)

if kind == "legacy_eip155":
    fields = [42, 10**9, 21000, alice, 10**18, b"", 37, r, s]
    tx = rlp.encode(fields)
    write_input(tx)
elif kind == "eip1559":
    fields = [chain_id, 42, 10**9, 2 * 10**9, 21000, alice, 10**18,
              b"", [], 1, r, s]
    tx = bytes([2]) + rlp.encode(fields)
    write_input(tx)
elif kind == "bad_s_high":
    high_s = int(
        "7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a1",
        16,
    )
    fields = [chain_id, 42, 10**9, 2 * 10**9, 21000, alice, 10**18,
              b"", [], 1, r, high_s]
    tx = bytes([2]) + rlp.encode(fields)
    write_input(tx)
else:
    raise SystemExit(f"unknown kind: {kind}")
PYVEC

  "$ZISKEMU" -e gen-out/zisk_tx_pubkey_recover_raw_status.elf \
    -i "$in_file" -o "$out_file" -n 10000000 \
    >"$REPO_ROOT/gen-out/zisk_tx_pubkey_recover_raw_status_${name}.emu.log" 2>&1 || true

  python3 - "$out_file" "$name" "$expected_status" "$expected_material" <<'PYCHECK'
import struct
import sys

out_path, name, expected_status, expected_material = sys.argv[1:5]
data = open(out_path, "rb").read()

def u64(off):
    return struct.unpack("<Q", data[off:off+8])[0]

status = u64(0)
material = u64(8)
expected_status = int(expected_status)
expected_material = int(expected_material)

if status != expected_status:
    print(f"  {name:<20} FAIL status={status} expected={expected_status}")
    raise SystemExit(1)

if status == 10 and material != expected_material:
    print(f"  {name:<20} FAIL material={material} expected={expected_material}")
    raise SystemExit(1)

print(f"  {name:<20} OK   status={status} material={material}")
PYCHECK
}

FAILED=0
# Valid txs: material + staging succeed, recovery backend stub -> status 50.
run_case "legacy_eip155" "legacy_eip155" 50 0 || FAILED=1
run_case "eip1559" "eip1559" 50 0 || FAILED=1
# High-s tx: material rejects with status 43, surfaced as helper status 10.
run_case "bad_s_high" "bad_s_high" 10 43 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_pubkey_recover_raw routes material/stage and reports backend stub status 50"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
