#!/usr/bin/env bash
# Verify the standalone ExecutionWitness SSZ-root probe against the Amsterdam
# execution-specs/remerkleable implementation.  The empty case is important:
# it makes each field's schema capacity part of the root, so it detects stale
# ByteList and List limits even without production-sized witness sections.
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

EXECUTION_SPECS_DIR="${EXECUTION_SPECS_DIR:-execution-specs}"
if [[ ! -f "$EXECUTION_SPECS_DIR/pyproject.toml" ]]; then
  echo "execution-specs source not found at $EXECUTION_SPECS_DIR; set EXECUTION_SPECS_DIR" >&2
  exit 1
fi

VDIR="$PWD/gen-out/ssz-execution-witness-root"
mkdir -p "$VDIR"

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_ssz_hash_tree_root_execution_witness ELF"
lake exe codegen --program zisk_ssz_hash_tree_root_execution_witness --halt linux93 \
  -o gen-out/zisk_ssz_hash_tree_root_execution_witness >/dev/null

uv run --directory "$EXECUTION_SPECS_DIR" --quiet python3 - "$VDIR" <<'PY'
import struct
import sys
from pathlib import Path

from ethereum.forks.amsterdam.stateless_ssz import (
    MAX_BYTES_PER_CODE,
    MAX_BYTES_PER_HEADER,
    MAX_BYTES_PER_WITNESS_NODE,
    MAX_WITNESS_CODES,
    MAX_WITNESS_HEADERS,
    MAX_WITNESS_NODES,
    SszExecutionWitness,
)
from remerkleable.byte_arrays import ByteList
from remerkleable.complex import List as SszList

out = Path(sys.argv[1])
StateByteList = ByteList[MAX_BYTES_PER_WITNESS_NODE]
CodeByteList = ByteList[MAX_BYTES_PER_CODE]
HeaderByteList = ByteList[MAX_BYTES_PER_HEADER]
StateList = SszList[StateByteList, MAX_WITNESS_NODES]
CodeList = SszList[CodeByteList, MAX_WITNESS_CODES]
HeaderList = SszList[HeaderByteList, MAX_WITNESS_HEADERS]

cases = {
    "empty": ([], [], []),
    "mixed": ([b"state"], [b"code", bytes(range(33))], [b"header"]),
}
for name, (state, codes, headers) in cases.items():
    witness = SszExecutionWitness(
        state=StateList(*(StateByteList(value) for value in state)),
        codes=CodeList(*(CodeByteList(value) for value in codes)),
        headers=HeaderList(*(HeaderByteList(value) for value in headers)),
    )
    section = witness.encode_bytes()
    root = bytes(witness.hash_tree_root())
    payload = struct.pack("<Q", len(section)) + section
    payload += b"\x00" * ((-len(payload)) % 8)
    (out / f"{name}.input").write_bytes(payload)
    (out / f"{name}.expected").write_text(root.hex() + " 0\n")
PY

run_case() {
  local name="$1" out="$VDIR/$1.output"
  "$ZISKEMU" -e gen-out/zisk_ssz_hash_tree_root_execution_witness.elf \
    -i "$VDIR/$name.input" -o "$out" -n 5000000 \
    >"$VDIR/$name.emu.log" 2>&1
  local actual_root actual_status expected_root expected_status
  actual_root="$(xxd -p -l 32 "$out" | tr -d '\n')"
  actual_status="$(od -An -tu8 -j 32 -N 8 "$out" | tr -d ' \n')"
  read -r expected_root expected_status < "$VDIR/$name.expected"
  if [[ "$actual_root" != "$expected_root" || "$actual_status" != "$expected_status" ]]; then
    echo "  $name FAIL: expected $expected_root status=$expected_status; got $actual_root status=$actual_status" >&2
    return 1
  fi
  echo "  $name OK"
}

run_case empty
run_case mixed
echo "==> PASS: ExecutionWitness root matches Amsterdam execution-specs"
