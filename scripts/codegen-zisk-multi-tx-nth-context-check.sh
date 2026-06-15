#!/usr/bin/env bash
# codegen-zisk-multi-tx-nth-context-check.sh
#
# Boundary-check multi_tx_nth_context against generated SSZ transaction lists.
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
lake build codegen >/dev/null

echo "==> emit zisk_multi_tx_nth_context ELF"
lake exe codegen --program zisk_multi_tx_nth_context --halt linux93 \
  -o gen-out/zisk_multi_tx_nth_context

python3 - <<'MAKE_INPUTS_PY'
import struct
from pathlib import Path

TX = bytes.fromhex(
    "f8500184ee6b280082520894aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    "881bc16d674ec80000801ba01111111111111111111111111111111111111111111111111111111111111111"
    "a02222222222222222222222222222222222222222222222222222222222222222"
)

cases = [
    ("last1024", 1024, 1023),
    ("last1025", 1025, 1024),
    ("last9523", 9523, 9522),
    ("oob9523", 9523, 9523),
]

out_dir = Path("gen-out")
for name, tx_count, index in cases:
    offsets = bytearray()
    first = tx_count * 4
    for i in range(tx_count):
        offsets.extend(struct.pack("<I", first + i * len(TX)))
    tx_list = bytes(offsets) + TX * tx_count

    # ziskemu maps file byte 0 to guest INPUT+8. The probe reads tx_list_len
    # at guest +8, index at guest +16, and the SSZ list at guest +640.
    payload = bytearray(632)
    struct.pack_into("<Q", payload, 0, len(tx_list))
    struct.pack_into("<Q", payload, 8, index)
    payload.extend(tx_list)
    payload.extend(b"\x00" * ((-len(payload)) % 8))
    (out_dir / f"zisk_multi_tx_nth_context_{name}.input").write_bytes(payload)
MAKE_INPUTS_PY

run_case() {
  local name="$1"
  local steps="${2:-5000000}"
  "$ZISKEMU" -e gen-out/zisk_multi_tx_nth_context.elf \
    -i "gen-out/zisk_multi_tx_nth_context_${name}.input" \
    -o "gen-out/zisk_multi_tx_nth_context_${name}.output" -n "$steps" \
    >"gen-out/zisk_multi_tx_nth_context_${name}.emu.log" 2>&1 || true
}

run_case last1024
run_case last1025
run_case last9523 20000000
run_case oob9523 20000000

python3 - <<'CHECK_OUTPUTS_PY'
import struct
import sys
from pathlib import Path

# Keep the expected length tied to the generated transaction.
TX_LEN = len(bytes.fromhex(
    "f8500184ee6b280082520894aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    "881bc16d674ec80000801ba01111111111111111111111111111111111111111111111111111111111111111"
    "a02222222222222222222222222222222222222222222222222222222222222222"
))
RECIPIENT = bytes.fromhex("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")

checks = [
    ("last1024", 0, TX_LEN),
    ("last1025", 0, TX_LEN),
    ("last9523", 0, TX_LEN),
    ("oob9523", 5, 0),
]

failed = False

def u64(data, off):
    return struct.unpack("<Q", data[off:off + 8])[0] if len(data) >= off + 8 else None

for name, exp_status, exp_tx_len in checks:
    path = Path(f"gen-out/zisk_multi_tx_nth_context_{name}.output")
    data = path.read_bytes() if path.exists() else b""
    status = u64(data, 0)
    tx_len = u64(data, 16)
    gas_limit = u64(data, 40)
    creation = u64(data, 48)
    data_len = u64(data, 64)
    tx_type = u64(data, 160)
    inner_off = u64(data, 168)
    inner_len = u64(data, 184)
    recipient = data[72:92]

    case_failed = status != exp_status
    if exp_status == 0:
        case_failed = case_failed or tx_len != exp_tx_len
        case_failed = case_failed or gas_limit != 21000
        case_failed = case_failed or creation != 0
        case_failed = case_failed or data_len != 0
        case_failed = case_failed or tx_type != 0
        case_failed = case_failed or inner_off != 0
        case_failed = case_failed or inner_len != exp_tx_len
        case_failed = case_failed or recipient != RECIPIENT
    else:
        case_failed = case_failed or tx_len not in (0, None)

    failed = failed or case_failed
    print(
        f"  {'FAIL' if case_failed else 'OK  '} {name:10s} "
        f"status={status!r} tx_len={tx_len!r} gas={gas_limit!r} "
        f"type={tx_type!r} inner_off={inner_off!r} inner_len={inner_len!r}"
    )
    if case_failed:
        print(f"       log=gen-out/zisk_multi_tx_nth_context_{name}.emu.log")

sys.exit(1 if failed else 0)
CHECK_OUTPUTS_PY

echo
echo "==> PASS: multi_tx_nth_context handles 1024/1025/9523 SSZ list boundaries"
