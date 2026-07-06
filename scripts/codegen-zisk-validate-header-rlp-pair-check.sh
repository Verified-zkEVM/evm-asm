#!/usr/bin/env bash
# codegen-zisk-validate-header-rlp-pair-check.sh -- verify validate_header_rlp_pair
# (bead evm-asm-fhsxz.2.3): the guest-callable "is this header a valid child of
# its parent?" check (header_extended_decode x2 + validate_header_full +
# header_validate_parent_hash).
#
# Builds a valid Amsterdam-style (this, parent) header pair where parent
# gas_used == gas_limit/2 (so the EIP-1559 child base-fee is unchanged) and
# this.parent_hash == keccak256(parent_rlp). Expects status 0. Then three
# invalid tweaks: wrong number (rejected), wrong base-fee (rejected), and a
# broken parent_hash link (status 702 = K94 mismatch + the wrapper's +700),
# and wrong excess_blob_gas recurrence (status 602 from validate_header_full).
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

VDIR="$REPO_ROOT/gen-out/header-pair"
mkdir -p "$VDIR"

echo "==> generate header-pair vectors"
uv run --directory execution-specs --quiet python3 - "$VDIR" <<'PY'
import struct, sys, os
import rlp
from Crypto.Hash import keccak

VDIR = sys.argv[1]
EMPTY_OMMERS = bytes.fromhex(
    "1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347")

def k256(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

def header(parent_hash, number, gas_limit, gas_used, timestamp, base_fee,
           state_root=b"\x44" * 32, extra=b"", difficulty=0,
           nonce=b"\x00" * 8, blob_gas_used=0, excess_blob_gas=0):
    # Amsterdam-style header with blob-gas fields.
    return [
        parent_hash,            # 0
        EMPTY_OMMERS,           # 1
        b"\x33" * 20,           # 2 coinbase
        state_root,             # 3
        b"\x55" * 32,           # 4 tx_root
        b"\x66" * 32,           # 5 receipts_root
        b"\x00" * 256,          # 6 bloom
        difficulty,             # 7
        number,                 # 8
        gas_limit,              # 9
        gas_used,               # 10
        timestamp,              # 11
        extra,                  # 12 extra_data
        b"\x77" * 32,           # 13 prev_randao
        nonce,                  # 14
        base_fee,               # 15
        b"\x88" * 32,           # 16 withdrawals_root
        blob_gas_used,          # 17
        excess_blob_gas,        # 18
        b"\x99" * 32,           # 19 parent_beacon_block_root
    ]

GL, BF = 30_000_000, 1_000_000_000
# parent: gas_used == gas_limit/2 => EIP-1559 base-fee unchanged in the child.
parent = header(b"\x22" * 32, 100, GL, GL // 2, 1000, BF)
parent_rlp = rlp.encode(parent)
ph = k256(parent_rlp)

def emit(name, this_fields):
    this_rlp = rlp.encode(this_fields)
    body = bytearray(struct.pack("<Q", len(this_rlp)) +
                     struct.pack("<Q", len(parent_rlp)) + this_rlp + parent_rlp)
    while len(body) % 8 != 0:        # ziskemu requires an 8-aligned input size
        body.append(0)
    with open(os.path.join(VDIR, name + ".input"), "wb") as f:
        f.write(bytes(body))

# valid child: number+1, ts>parent, gl unchanged, gas_used<=gl, base_fee=BF,
# parent_hash = keccak(parent_rlp).
emit("valid",      header(ph, 101, GL, GL // 2, 1012, BF))
emit("bad_number", header(ph, 103, GL, GL // 2, 1012, BF))      # number != parent+1
emit("bad_basefee",header(ph, 101, GL, GL // 2, 1012, BF + 1))  # base-fee mismatch
emit("bad_phash",  header(b"\xde" * 32, 101, GL, GL // 2, 1012, BF))  # broken link
emit("bad_excess", header(ph, 101, GL, GL // 2, 1012, BF, excess_blob_gas=1))
print("wrote valid / bad_number / bad_basefee / bad_phash / bad_excess")
PY

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_validate_header_rlp_pair probe ELF"
lake exe codegen --program zisk_validate_header_rlp_pair --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_validate_header_rlp_pair"

read_status() { od -An -tu8 -j 0 -N 8 "$1" | tr -d ' \n'; }
run() {  # run <name> -> echoes status
  local out="$VDIR/$1.output"
  "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_validate_header_rlp_pair.elf" \
    -i "$VDIR/$1.input" -o "$out" -n 5000000 >/dev/null 2>&1 </dev/null || { echo "ERR"; return; }
  read_status "$out"
}

fail=0
check() {  # check <name> <predicate-desc> <test>
  local name="$1" desc="$2" st; st="$(run "$name")"
  if eval "$3"; then echo "  PASS   $name ($desc) status=$st"
  else echo "  FAIL   $name ($desc) status=$st"; fail=1; fi
}
check valid       "valid child => 0"      '[[ "$st" == "0" ]]'
check bad_number  "wrong number rejected" '[[ "$st" != "0" && "$st" != "ERR" ]]'
check bad_basefee "base-fee rejected"     '[[ "$st" != "0" && "$st" != "ERR" ]]'
check bad_phash   "broken link => 702"    '[[ "$st" == "702" ]]'
check bad_excess  "bad excess => 602"     '[[ "$st" == "602" ]]'

[[ "$fail" -eq 0 ]] && echo "==> PASS: validate_header_rlp_pair matches expectations" \
  || { echo "==> FAIL"; exit 1; }
