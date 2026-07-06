#!/usr/bin/env bash
# codegen-zisk-block-validate-receipts-consensus-list-check.sh
#
# Validate the combined receipts consensus surface: header.receipts_root and
# header.logs_bloom are checked from one RLP list of already-encoded receipts.
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

echo "==> emit zisk_block_validate_receipts_consensus_list ELF"
lake exe codegen --program zisk_block_validate_receipts_consensus_list --halt linux93 \
  -o gen-out/zisk_block_validate_receipts_consensus_list

read_u64() { od -An -tu8 -j "$2" -N 8 "$1" | tr -d ' \n'; }

run_case() {
  local name="$1"
  local receipts_py="$2"
  local root_override="$3"
  local bloom_override="$4"
  local exp_status="$5"
  local exp_root_valid="$6"
  local exp_bloom_valid="$7"
  local in_file="$REPO_ROOT/gen-out/zisk_block_validate_receipts_consensus_list_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_validate_receipts_consensus_list_${name}.output"

  RECEIPTS_PY="$receipts_py" ROOT_OVERRIDE="$root_override" BLOOM_OVERRIDE="$bloom_override" \
  uv run --directory execution-specs --quiet python3 - "$in_file" <<'PYGEN'
import ast, os, struct, sys
from ethereum.merkle_patricia_trie import Trie, trie_set, root
from ethereum_rlp import rlp
from ethereum_types.bytes import Bytes
from ethereum_types.numeric import Uint

raw = ast.literal_eval(os.environ["RECEIPTS_PY"])
root_override = os.environ["ROOT_OVERRIDE"]
bloom_override = os.environ["BLOOM_OVERRIDE"]

def rlp_list_prefix(payload_len: int) -> bytes:
    if payload_len <= 55:
        return bytes([0xC0 + payload_len])
    length_bytes = payload_len.to_bytes((payload_len.bit_length() + 7) // 8, "big")
    return bytes([0xF7 + len(length_bytes)]) + length_bytes

receipt_values = []
block_bloom = bytearray(256)
for item in raw:
    status = Uint(item.get("status", 1))
    gas = Uint(item.get("gas", 21000))
    bloom = bytes.fromhex(item.get("bloom", "00" * 256))
    logs = []
    inner = rlp.encode([status, gas, bloom, logs])
    tx_type = item.get("type", 0)
    if tx_type:
        receipt_values.append(bytes([tx_type]) + inner)
    else:
        receipt_values.append(inner)
    if len(bloom) == 256:
        for i, b in enumerate(bloom):
            block_bloom[i] |= b

receipts_payload = b"".join(receipt_values)
receipts_list_rlp = rlp_list_prefix(len(receipts_payload)) + receipts_payload
trie = Trie(secured=False, default=None)
for i, value in enumerate(receipt_values):
    trie_set(trie, Bytes(rlp.encode(Uint(i))), Bytes(value))
correct_root = bytes(root(trie))
correct_bloom = bytes(block_bloom)

if root_override == "":
    receipts_root = correct_root
elif root_override == "wrong":
    receipts_root = bytes.fromhex("ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100")
elif root_override == "short":
    receipts_root = b"\xaa" * 16
else:
    raise ValueError(root_override)

if bloom_override == "":
    logs_bloom = correct_bloom
elif bloom_override == "zero":
    logs_bloom = b"\x00" * 256
elif bloom_override == "extra":
    logs_bloom = bytearray(correct_bloom)
    logs_bloom[255] ^= 1
    logs_bloom = bytes(logs_bloom)
else:
    raise ValueError(bloom_override)

H32 = b"\x11" * 32
fields = [
    b"\x22"*32,
    bytes.fromhex("1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"),
    b"\x33"*20,
    b"\x44"*32,
    b"\x55"*32,
    receipts_root,
    logs_bloom,
    Uint(0), Uint(18000000), Uint(30000000), Uint(21000),
    Uint(1700000000), b"", H32, b"\x00"*8,
    Uint(7 * 10**9), H32,
]
header_rlp = rlp.encode(fields)

with open(sys.argv[1], "wb") as f:
    f.write(struct.pack("<Q", len(header_rlp)))
    f.write(struct.pack("<Q", len(receipts_list_rlp)))
    f.write(header_rlp + receipts_list_rlp)
    f.write(b"\x00" * ((-(16 + len(header_rlp) + len(receipts_list_rlp))) % 8))
PYGEN

  if ! "$ZISKEMU" -e gen-out/zisk_block_validate_receipts_consensus_list.elf \
        -i "$in_file" -o "$out_file" -n 50000000 >/dev/null 2>&1 </dev/null; then
    printf "  %-28s ERROR ziskemu\n" "$name"
    return 1
  fi

  local status root_valid bloom_valid
  status="$(read_u64 "$out_file" 0)"
  root_valid="$(read_u64 "$out_file" 8)"
  bloom_valid="$(read_u64 "$out_file" 16)"
  if [[ "$status" == "$exp_status" && "$root_valid" == "$exp_root_valid" && "$bloom_valid" == "$exp_bloom_valid" ]]; then
    printf "  %-28s OK   status=%s root=%s bloom=%s\n" "$name" "$status" "$root_valid" "$bloom_valid"
    return 0
  fi

  printf "  %-28s FAIL status=%s/%s root=%s/%s bloom=%s/%s\n" \
    "$name" "$status" "$exp_status" "$root_valid" "$exp_root_valid" "$bloom_valid" "$exp_bloom_valid"
  return 1
}

B0="$(python3 - <<'PY'
b=bytearray(256); b[0]=0x80; print(bytes(b).hex())
PY
)"
B1="$(python3 - <<'PY'
b=bytearray(256); b[1]=0x40; print(bytes(b).hex())
PY
)"
B2="$(python3 - <<'PY'
b=bytearray(256); b[31]=0x20; print(bytes(b).hex())
PY
)"
B3="$(python3 - <<'PY'
b=bytearray(256); b[255]=0x01; print(bytes(b).hex())
PY
)"
SHORT="$(python3 - <<'PY'
print('aa' * 16)
PY
)"
MANY129="$(python3 - <<'PY'
print('[' + ','.join("{'status':1,'gas':21000}" for _ in range(129)) + ']')
PY
)"

CASES=(
  "empty|[]|||0|1|1"
  "one|[{'status':1,'gas':21000,'bloom':'$B0'}]|||0|1|1"
  "two|[{'status':1,'gas':21000,'bloom':'$B0'},{'status':1,'gas':42000,'bloom':'$B1'}]|||0|1|1"
  "typed_one|[{'type':2,'status':1,'gas':21000,'bloom':'$B0'}]|||0|1|1"
  "five|[{'status':1,'gas':21000,'bloom':'$B0'},{'status':0,'gas':42000,'bloom':'$B1'},{'status':1,'gas':63000,'bloom':'$B2'},{'status':1,'gas':84000,'bloom':'$B3'},{'status':0,'gas':105000,'bloom':'$B0'}]|||0|1|1"
  "wrong_root|[{'status':1,'gas':21000,'bloom':'$B0'}]|wrong||2|0|0"
  "wrong_bloom_zero|[{'status':1,'gas':21000,'bloom':'$B0'}]||zero|4|1|0"
  "wrong_bloom_extra|[]||extra|4|1|0"
  "short_receipt_bloom|[{'status':1,'gas':21000,'bloom':'$SHORT'}]|||3|1|0"
  "short_header_root|[{'status':1,'gas':21000,'bloom':'$B0'}]|short||1|0|0"
  "129_receipts_capacity|$MANY129|||1|0|0"
)

FAILED=0
for row in "${CASES[@]}"; do
  IFS='|' read -r name receipts root_override bloom_override exp_status exp_root exp_bloom <<<"$row"
  run_case "$name" "$receipts" "$root_override" "$bloom_override" "$exp_status" "$exp_root" "$exp_bloom" || FAILED=1
done

[[ "$FAILED" -eq 0 ]] && echo "==> PASS: receipts consensus list validator checks root and bloom" \
  || { echo "==> FAIL"; exit 1; }
