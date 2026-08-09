#!/usr/bin/env bash
# codegen-bmvmx-full-capacity-probes.sh -- regression probes for bmvmx.5.5.7.6.
set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

RUN_DIR="${RUN_DIR:-gen-out/bmvmx-full-capacity-probes}"
EEST_FIXTURES_DIR="${EEST_FIXTURES_DIR:-gen-out/eest-fixtures}"
EXPECTED_EEST_TX_COUNT="${EXPECTED_EEST_TX_COUNT:-1021}"
SYNTHETIC_TX_COUNTS="${SYNTHETIC_TX_COUNTS:-1021 1024 1025 16666}"
# A 1025-transaction body is the regression boundary for the former
# fixture-era active-loop cap.  It is below the protocol-derived full cap, so
# it must classify as active-loop admissible, not merely as decodable.
REQUIRED_ACTIVE_TX_COUNT="${REQUIRED_ACTIVE_TX_COUNT:-1025}"
REQUIRE_EEST="${REQUIRE_EEST:-0}"
RUN_SYNTHETIC="${RUN_SYNTHETIC:-1}"
ZISKEMU="${ZISKEMU:-}"

mkdir -p "$RUN_DIR"
RUN_DIR="$(cd "$RUN_DIR" && pwd)"

mtx_caps() {
  python3 - <<'PY'
import re
from pathlib import Path

text = Path("EvmAsm/Codegen/Programs/BlockVerdictParams.lean").read_text()
raw = dict(re.findall(r"def\s+(\w+)\s*:\s*Nat\s*:=\s*([^\n]+)", text))

visiting = set()
resolved = {}
def resolve(name):
    if name in resolved:
        return resolved[name]
    if name in visiting:
        raise SystemExit(f"cycle while resolving {name}")
    visiting.add(name)
    value = raw.get(name)
    if value is None:
        raise SystemExit(f"missing {name} in BlockVerdictParams.lean")
    value = value.strip()
    if value.isdigit():
        result = int(value)
    elif value in raw:
        result = resolve(value)
    else:
        quotient = re.fullmatch(r"(\w+)\s*/\s*(\w+)", value)
        if not quotient:
            raise SystemExit(f"unsupported {name} definition: {value}")
        numerator, denominator = map(resolve, quotient.groups())
        if denominator == 0:
            raise SystemExit(f"zero denominator in {name}: {value}")
        result = numerator // denominator
    visiting.remove(name)
    resolved[name] = result
    return result

print(resolve("bvMtxActiveTxCap"), resolve("bvMtxFullTxCap"))
PY
}

classify_tx_count() {
  local tx_count="$1" active_cap="$2" full_cap="$3"
  if (( tx_count > full_cap )); then
    printf "above-full-cap"
  elif (( tx_count > active_cap )); then
    printf "above-active-within-full"
  else
    printf "within-active"
  fi
}

resolve_ziskemu() {
  if [[ -n "$ZISKEMU" ]]; then
    return 0
  fi
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else
    echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2
    return 1
  fi
}

scan_eest_fixtures() {
  local active_cap="$1" full_cap="$2"
  local fixtures_dir="$EEST_FIXTURES_DIR"
  [[ "$fixtures_dir" = /* ]] || fixtures_dir="$REPO_ROOT/$fixtures_dir"
  if [[ ! -d "$fixtures_dir" ]]; then
    echo "eest_status=missing fixtures_dir=$fixtures_dir"
    [[ "$REQUIRE_EEST" -eq 0 ]] || return 1
    return 0
  fi

  local report="$RUN_DIR/eest-max-tx.tsv"
  local scan_out scan_rc
  set +e
  scan_out="$(uv run --directory execution-specs --quiet python3 - "$fixtures_dir" "$report" <<'PY'
import json
import sys
from pathlib import Path

try:
    from ethereum.forks.amsterdam.stateless_guest import deserialize_stateless_input
    from ethereum_types.bytes import Bytes
except ImportError as exc:
    print(f"IMPORT_ERROR\t{type(exc).__name__}:{exc}", file=sys.stderr)
    raise SystemExit(2)

fixtures_dir = Path(sys.argv[1])
report = Path(sys.argv[2])
total = 0
max_count = -1
max_rows = []

for path in sorted(fixtures_dir.rglob("*.json")):
    try:
        doc = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError):
        continue
    for test_name, tc in doc.items():
        blocks = tc.get("blocks") if isinstance(tc, dict) else None
        if not isinstance(blocks, list):
            continue
        for block_index, block in enumerate(blocks):
            if not isinstance(block, dict) or not block.get("statelessInputBytes"):
                continue
            raw = block["statelessInputBytes"]
            blob = bytes.fromhex(raw[2:] if raw.startswith("0x") else raw)
            try:
                payload = deserialize_stateless_input(Bytes(blob)).new_payload_request.execution_payload
            except Exception as exc:
                print(f"DECODE_ERROR\t{path}\t{test_name}\t{block_index}\t{type(exc).__name__}:{exc}", file=sys.stderr)
                continue
            total += 1
            tx_count = len(payload.transactions)
            rel = path.relative_to(fixtures_dir)
            row = (tx_count, str(rel), test_name, block_index)
            if tx_count > max_count:
                max_count = tx_count
                max_rows = [row]
            elif tx_count == max_count:
                max_rows.append(row)

with report.open("w") as f:
    f.write("tx_count\tfixture\ttest\tblock_index\n")
    for row in max_rows:
        f.write("\t".join(map(str, row)) + "\n")

if total == 0:
    print("NO_STATELESS_FIXTURES")
    raise SystemExit(3)

tx_count, rel, test_name, block_index = max_rows[0]
print(f"OK\t{total}\t{tx_count}\t{rel}\t{block_index}\t{test_name}")
PY
)"
  scan_rc="$?"
  set -e
  if [[ "$scan_rc" -ne 0 ]]; then
    if [[ "$scan_rc" -eq 2 ]]; then
      echo "eest_status=missing-execution-specs fixtures_dir=$fixtures_dir"
    else
      echo "eest_status=scan-failed rc=$scan_rc fixtures_dir=$fixtures_dir"
    fi
    [[ "$REQUIRE_EEST" -eq 0 ]] || return 1
    return 0
  fi

  local status total max_count fixture block_index test_name
  IFS=$'\t' read -r status total max_count fixture block_index test_name <<< "$scan_out"
  local class
  class="$(classify_tx_count "$max_count" "$active_cap" "$full_cap")"
  echo "eest_status=ok max_tx_count=$max_count expected_floor=$EXPECTED_EEST_TX_COUNT capacity_class=$class active_cap=$active_cap full_cap=$full_cap fixture=$fixture report=$report"
  if (( max_count < EXPECTED_EEST_TX_COUNT )); then
    echo "eest_status=below-expected max_tx_count=$max_count expected_floor=$EXPECTED_EEST_TX_COUNT" >&2
    [[ "$REQUIRE_EEST" -eq 0 ]] || return 1
  fi
}

emit_block_body_input() {
  local tx_count="$1" in_file="$2"
  uv run --directory execution-specs --quiet python3 - "$tx_count" "$in_file" <<'PY'
import struct
import sys

tx_count = int(sys.argv[1])
out = sys.argv[2]
tx = bytes.fromhex(
    "f8500184ee6b280082520894aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    "881bc16d674ec80000801ba01111111111111111111111111111111111111111111111111111111111111111"
    "a02222222222222222222222222222222222222222222222222222222222222222"
)
def rlp_list(payload: bytes) -> bytes:
    """Encode an RLP list whose already-encoded items form payload."""
    length = len(payload)
    if length < 56:
        return bytes([0xC0 + length]) + payload
    length_bytes = length.to_bytes((length.bit_length() + 7) // 8, "big")
    return bytes([0xF7 + len(length_bytes)]) + length_bytes + payload

def rlp_bytes(value: bytes) -> bytes:
    if len(value) == 1 and value[0] < 0x80:
        return value
    if len(value) < 56:
        return bytes([0x80 + len(value)]) + value
    length_bytes = len(value).to_bytes((len(value).bit_length() + 7) // 8, "big")
    return bytes([0xB7 + len(length_bytes)]) + length_bytes + value

# Keep the historical probe construction byte-identical to rlp.encode([txs,
# [], []]): each fixture transaction is a byte string, hence one RLP string
# item inside the transactions list.  This is intentionally only a body-count
# capacity probe; it does not claim to construct a signed execution payload.
transactions = rlp_list(rlp_bytes(tx) * tx_count)
body_rlp = rlp_list(transactions + b"\xc0\xc0")
record = struct.pack("<Q", len(body_rlp)) + body_rlp
with open(out, "wb") as f:
    f.write(record)
    f.write(b"\x00" * ((-len(record)) % 8))
PY
}

run_synthetic_probe() {
  local active_cap="$1" full_cap="$2"
  [[ "$RUN_SYNTHETIC" -eq 1 ]] || return 0
  resolve_ziskemu

  echo "==> lake build codegen"
  lake build codegen

  echo "==> emit zisk_block_body_extract_tx_count ELF"
  lake exe codegen --program zisk_block_body_extract_tx_count --halt linux93 \
    -o "$RUN_DIR/zisk_block_body_extract_tx_count"

  local failed=0
  if (( active_cap < REQUIRED_ACTIVE_TX_COUNT )); then
    echo "active-cap regression: active_cap=$active_cap must admit tx_count=$REQUIRED_ACTIVE_TX_COUNT" >&2
    return 1
  fi
  local tx_count name in_file out_file log_file status_le count_le status count class
  for tx_count in $SYNTHETIC_TX_COUNTS; do
    name="tx${tx_count}"
    in_file="$RUN_DIR/${name}.input"
    out_file="$RUN_DIR/${name}.output"
    log_file="$RUN_DIR/${name}.emu.log"
    emit_block_body_input "$tx_count" "$in_file"
    "$ZISKEMU" -e "$RUN_DIR/zisk_block_body_extract_tx_count.elf" \
      -i "$in_file" -o "$out_file" -n "${ZISKEMU_STEPS:-20000000}" \
      >"$log_file" 2>&1 || true

    status_le="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
    count_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
    status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('${status_le:-0000000000000000}'))[0])")"
    count="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('${count_le:-0000000000000000}'))[0])")"
    class="$(classify_tx_count "$tx_count" "$active_cap" "$full_cap")"
    if [[ "$status" == "0" && "$count" == "$tx_count" ]]; then
      echo "synthetic_status=ok tx_count=$tx_count decoded_count=$count capacity_class=$class active_cap=$active_cap full_cap=$full_cap resource_status=block-body-count-only"
    else
      echo "synthetic_status=fail tx_count=$tx_count status=$status decoded_count=$count capacity_class=$class active_cap=$active_cap full_cap=$full_cap log=$log_file" >&2
      failed=1
    fi
  done
  return "$failed"
}

read -r active_cap full_cap < <(mtx_caps)
echo "active_mtx_cap=$active_cap full_mtx_cap=$full_cap"
scan_eest_fixtures "$active_cap" "$full_cap"
run_synthetic_probe "$active_cap" "$full_cap"
