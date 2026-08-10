#!/usr/bin/env bash
# codegen-bmvmx-full-capacity-probes.sh -- regression probes for bmvmx.5.5.7.6.
set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

RUN_DIR="${RUN_DIR:-gen-out/bmvmx-full-capacity-probes}"
EEST_FIXTURES_DIR="${EEST_FIXTURES_DIR:-gen-out/eest-fixtures}"
EXPECTED_EEST_TX_COUNT="${EXPECTED_EEST_TX_COUNT:-1021}"
REQUIRE_EEST="${REQUIRE_EEST:-0}"

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

read -r active_cap full_cap < <(mtx_caps)
echo "active_mtx_cap=$active_cap full_mtx_cap=$full_cap"
scan_eest_fixtures "$active_cap" "$full_cap"
