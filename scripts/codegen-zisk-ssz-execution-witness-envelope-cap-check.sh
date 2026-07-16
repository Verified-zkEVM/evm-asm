#!/usr/bin/env bash
# Verify ExecutionWitness ByteList envelopes in the live stateless_verdict_v2 path.
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-$HOME/.zisk/bin/ziskemu}"
[[ -x "$ZISKEMU" ]] || { echo "ziskemu not found: $ZISKEMU" >&2; exit 1; }
PYTHON="${PYTHON:-python3}"
FIXTURES="${EEST_FIXTURES_DIR:-gen-out/eest-fixtures/tests-zkevm@v0.6.2/fixtures/fixtures}"
[[ -d "$FIXTURES" ]] || { echo "EEST fixtures not found: $FIXTURES" >&2; exit 1; }

RUN_DIR="gen-out/ssz-execution-witness-envelope-cap"
rm -rf "$RUN_DIR"
mkdir -p "$RUN_DIR"

echo "==> build and emit stateless_verdict_v2"
lake build codegen >/dev/null
lake exe codegen --program zisk_stateless_verdict_v2 --halt linux93 \
  -o "$RUN_DIR/zisk_stateless_verdict_v2" >/dev/null

echo "==> construct protocol-boundary inputs"
"$PYTHON" - "$FIXTURES" "$RUN_DIR" <<'PY'
import json
import struct
import sys
from dataclasses import replace
from pathlib import Path

from ethereum.forks.amsterdam.stateless_guest import deserialize_stateless_input
from ethereum.forks.amsterdam.stateless_host import serialize_stateless_input
from ethereum_types.bytes import Bytes

fixtures, out = map(Path, sys.argv[1:])

for path in fixtures.rglob("*.json"):
    doc = json.loads(path.read_text())
    found = None
    for test in doc.values():
        if not isinstance(test, dict):
            continue
        for block in test.get("blocks", []):
            if isinstance(block, dict) and block.get("statelessInputBytes"):
                candidate = deserialize_stateless_input(
                    Bytes.fromhex(block["statelessInputBytes"][2:])
                )
                if candidate.witness.codes and candidate.witness.headers:
                    found = candidate
                    break
        if found is not None:
            break
    if found is not None:
        break
else:
    raise SystemExit("no EEST input with witness code and header entries")

def u32(data, offset):
    return int.from_bytes(data[offset : offset + 4], "little")

def p32(data, offset, value):
    data[offset : offset + 4] = value.to_bytes(4, "little")

def extend_last_code(blob):
    data = bytearray(blob)
    top = 2  # two-byte StatelessInput schema id
    witness = top + u32(data, top + 4)
    header_start = witness + u32(data, witness + 8)
    data.insert(header_start, ord("!"))
    p32(data, witness + 8, u32(data, witness + 8) + 1)
    p32(data, top + 8, u32(data, top + 8) + 1)
    p32(data, top + 12, u32(data, top + 12) + 1)
    return bytes(data)

def extend_last_header(blob):
    data = bytearray(blob)
    top = 2
    chain_config = top + u32(data, top + 8)
    data.insert(chain_config, ord("!"))
    p32(data, top + 8, u32(data, top + 8) + 1)
    p32(data, top + 12, u32(data, top + 12) + 1)
    return bytes(data)

code_ok = bytes(serialize_stateless_input(replace(
    found, witness=replace(found.witness,
        codes=found.witness.codes + (Bytes(b"c" * 65536),)),
)))
header_ok = bytes(serialize_stateless_input(replace(
    found, witness=replace(found.witness,
        headers=found.witness.headers + (Bytes(b"h" * 1024),)),
)))
cases = [
    ("code-65536", code_ok, False),
    ("code-65537", extend_last_code(code_ok), True),
    ("header-1024", header_ok, False),
    ("header-1025", extend_last_header(header_ok), True),
]
for name, blob, should_reject in cases:
    try:
        deserialize_stateless_input(Bytes(blob))
    except Exception:
        if not should_reject:
            raise
    else:
        if should_reject:
            raise SystemExit(f"execution-specs unexpectedly accepted {name}")
    packed = struct.pack("<Q", len(blob)) + blob
    (out / f"{name}.input").write_bytes(
        packed + b"\0" * ((-len(packed)) % 8)
    )
PY

run_case() {
  local name="$1" expected_verdict="$2" expected_fail="$3"
  "$ZISKEMU" -e "$RUN_DIR/zisk_stateless_verdict_v2.elf" \
    -i "$RUN_DIR/$name.input" -o "$RUN_DIR/$name.output" -n 500000000 \
    >"$RUN_DIR/$name.log" 2>&1
  local actual
  actual="$(od -An -tu8 -N16 "$RUN_DIR/$name.output" | xargs)"
  local expected="$expected_verdict $expected_fail"
  [[ "$actual" == "$expected" ]] || {
    echo "$name: expected '$expected', got '$actual'" >&2
    exit 1
  }
  echo "  $name: $actual"
}

echo "==> run live envelope boundaries"
run_case code-65536 1 0
run_case code-65537 0 33
# The exact-cap header is SSZ-valid and gets past the envelope check; its
# deliberately non-RLP payload subsequently fails normal header validation.
run_case header-1024 0 10
run_case header-1025 0 34

echo "==> PASS: live ExecutionWitness code/header ByteList caps"
