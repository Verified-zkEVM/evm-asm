#!/usr/bin/env bash
# codegen-zisk-block-header-ssz-to-rlp-check.sh -- verify block_header_ssz_to_rlp
# (bead evm-asm-fhsxz.2.4.1): re-encode an Amsterdam block header from its SSZ
# ExecutionPayload (+ 5 commitments not in the fixed payload) into the canonical
# RLP whose keccak256 is the block hash.
#
# Python builds a canonical SSZ ExecutionPayload blob + the 23-field Amsterdam
# header RLP from the same field values; the probe reads the blob + roots and
# emits the header RLP; we diff the RLP byte-for-byte AND check keccak(out)
# equals keccak(expected) (the block hash).
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

VDIR="$REPO_ROOT/gen-out/block-header"
mkdir -p "$VDIR"

echo "==> generate SSZ payload + expected header RLP"
uv run --directory execution-specs --quiet python3 - "$VDIR" <<'PY'
import struct, sys, os
import rlp
from Crypto.Hash import keccak

VDIR = sys.argv[1]
def k(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()
EMPTY_OMMER = bytes.fromhex("1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347")

# field values
parent_hash = b"\x11" * 32
coinbase    = b"\x33" * 20
state_root  = b"\x44" * 32
receipts    = b"\x66" * 32
bloom       = bytes(range(256))           # arbitrary 256-byte logs_bloom
prev_randao = b"\x77" * 32
number      = 100
gas_limit   = 30_000_000
gas_used    = 21_000
timestamp   = 1_700_000_000
extra_data  = b"test-extra-data"          # 15 bytes
base_fee    = 1_000_000_000
block_hash_f= b"\x99" * 32                 # in payload, unused by the encoder
blob_gas    = 0
excess_blob = 0
# the four roots NOT in the payload (encoder inputs)
tx_root        = b"\xaa" * 32
wd_root        = b"\xbb" * 32
parent_beacon  = b"\xcc" * 32
requests_hash  = b"\xdd" * 32
block_access_list = rlp.encode([])
block_access_list_hash = k(block_access_list)
slot_number = 12_345

# ---- canonical SSZ ExecutionPayload (fixed 540 B + variable tail) ----
fixed = bytearray(540)
fixed[0:32]    = parent_hash
fixed[32:52]   = coinbase
fixed[52:84]   = state_root
fixed[84:116]  = receipts
fixed[116:372] = bloom
fixed[372:404] = prev_randao
fixed[404:412] = number.to_bytes(8, "little")
fixed[412:420] = gas_limit.to_bytes(8, "little")
fixed[420:428] = gas_used.to_bytes(8, "little")
fixed[428:436] = timestamp.to_bytes(8, "little")
fixed[440:472] = base_fee.to_bytes(32, "little")
fixed[472:504] = block_hash_f
fixed[512:520] = blob_gas.to_bytes(8, "little")
fixed[520:528] = excess_blob.to_bytes(8, "little")
fixed[532:540] = slot_number.to_bytes(8, "little")
extra_off = 540
tx_off    = extra_off + len(extra_data)
wd_off    = tx_off                       # transactions empty
bal_off   = wd_off                       # withdrawals empty
fixed[436:440] = extra_off.to_bytes(4, "little")
fixed[504:508] = tx_off.to_bytes(4, "little")
fixed[508:512] = wd_off.to_bytes(4, "little")
fixed[528:532] = bal_off.to_bytes(4, "little")
payload = bytes(fixed) + extra_data + block_access_list

# ---- canonical Amsterdam header RLP (23 fields) ----
def ri(x):
    return b"" if x == 0 else x.to_bytes((x.bit_length() + 7) // 8, "big")
header = [parent_hash, EMPTY_OMMER, coinbase, state_root, tx_root, receipts,
         bloom, ri(0), ri(number), ri(gas_limit), ri(gas_used), ri(timestamp),
         extra_data, prev_randao, b"\x00" * 8, ri(base_fee), wd_root,
         ri(blob_gas), ri(excess_blob), parent_beacon, requests_hash,
         block_access_list_hash, ri(slot_number)]
expected = rlp.encode(header)

body = (struct.pack("<Q", len(payload)) + tx_root + wd_root + parent_beacon
        + requests_hash + block_access_list_hash + payload)
body += b"\x00" * ((-len(body)) % 8)
with open(os.path.join(VDIR, "hdr.input"), "wb") as f:
    f.write(body)
with open(os.path.join(VDIR, "hdr.expected"), "w") as f:
    f.write(expected.hex())
with open(os.path.join(VDIR, "hdr.blockhash"), "w") as f:
    f.write(k(expected).hex())
print(f"payload_len={len(payload)} header_rlp_len={len(expected)} block_hash={k(expected).hex()[:16]}..")
PY

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_block_header_ssz_to_rlp probe ELF"
lake exe codegen --program zisk_block_header_ssz_to_rlp --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_block_header_ssz_to_rlp"

out="$VDIR/hdr.output"
"$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_block_header_ssz_to_rlp.elf" -i "$VDIR/hdr.input" \
  -o "$out" -n 3000000 >/dev/null 2>&1 </dev/null || { echo "  ERROR (ziskemu)"; exit 1; }
# OUTPUT+0 = header RLP length; OUTPUT+8 = block hash = keccak256(header RLP).
act_len="$(od -An -tu8 -j 0 -N 8 "$out" | tr -d ' \n')"
act_bh="$(xxd -p -s 8 -l 32 "$out" | tr -d '\n')"
exp_len="$(( $(wc -c < "$VDIR/hdr.expected") / 2 ))"
exp_bh="$(cat "$VDIR/hdr.blockhash")"
if [[ "$act_bh" == "$exp_bh" && "$act_len" == "$exp_len" ]]; then
  echo "  PASS   rlp_len=$act_len  block_hash=$act_bh"
  echo "==> PASS: block_header_ssz_to_rlp matches reference (keccak of full header RLP)"
else
  echo "  FAIL"
  [[ "$act_len" != "$exp_len" ]] && echo "    rlp_len exp=$exp_len act=$act_len"
  [[ "$act_bh" != "$exp_bh" ]] && { echo "    block_hash exp: $exp_bh"; echo "    block_hash act: $act_bh"; }
  echo "==> FAIL"; exit 1
fi
