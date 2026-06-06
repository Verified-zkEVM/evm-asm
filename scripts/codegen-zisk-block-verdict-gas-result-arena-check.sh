#!/usr/bin/env bash
# codegen-zisk-block-verdict-gas-result-arena-check.sh -- block verdict runtime gas-result arena probe.
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

echo "==> emit zisk_block_verdict_gas_result_arena ELF"
lake exe codegen --program zisk_block_verdict_gas_result_arena --halt linux93 \
  -o gen-out/zisk_block_verdict_gas_result_arena

REPO_ROOT="$(pwd)"

# run_case <name> <mode> <expected_csv>
run_case() {
  local name="$1" mode="$2" expected_csv="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_block_verdict_gas_result_arena_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_verdict_gas_result_arena_${name}.output"
  local expected_file="$REPO_ROOT/gen-out/zisk_block_verdict_gas_result_arena_${name}.expected"

  python3 - "$in_file" "$expected_file" "$mode" "$expected_csv" <<'PY'
import struct
import sys

in_path, expected_path, mode, expected_csv = sys.argv[1:]

def be(n: int) -> bytes:
    if n == 0:
        return b""
    out = bytearray()
    while n:
        out.append(n & 0xff)
        n >>= 8
    return bytes(reversed(out))

def rlp_bytes(data: bytes) -> bytes:
    if len(data) == 1 and data[0] < 0x80:
        return data
    if len(data) <= 55:
        return bytes([0x80 + len(data)]) + data
    lb = be(len(data))
    return bytes([0xb7 + len(lb)]) + lb + data

def rlp_uint(n: int) -> bytes:
    return rlp_bytes(be(n))

def rlp_list(items: list[bytes]) -> bytes:
    payload = b"".join(items)
    if len(payload) <= 55:
        return bytes([0xc0 + len(payload)]) + payload
    lb = be(len(payload))
    return bytes([0xf7 + len(lb)]) + lb + payload

def legacy_tx(nonce: int, gas: int) -> bytes:
    return rlp_list([
        rlp_uint(nonce),
        rlp_uint(1),
        rlp_uint(gas),
        rlp_bytes(bytes.fromhex("1111111111111111111111111111111111111111")),
        rlp_uint(0),
        rlp_bytes(b""),
        rlp_uint(27),
        rlp_uint(1),
        rlp_uint(1),
    ])

def typed_2930_tx(nonce: int, gas: int) -> bytes:
    return b"\x01" + rlp_list([
        rlp_uint(1),
        rlp_uint(nonce),
        rlp_uint(1),
        rlp_uint(gas),
        rlp_bytes(bytes.fromhex("2222222222222222222222222222222222222222")),
        rlp_uint(0),
        rlp_bytes(b""),
        rlp_list([]),
        rlp_uint(1),
        rlp_uint(1),
        rlp_uint(1),
    ])

def tx_list(txs: list[bytes]) -> bytes:
    if not txs:
        return b""
    first = 4 * len(txs)
    offsets = []
    cur = first
    for tx in txs:
        offsets.append(cur)
        cur += len(tx)
    return b"".join(struct.pack("<I", x) for x in offsets) + b"".join(txs)

payload = bytearray(640)
tx_off = 600
count = 0
gas_left = [0] * 16
refunds = [0] * 16
floors = [0] * 16
block_gas_limit = 0

if mode == "empty":
    txs = b""
    count = 0
    block_gas_limit = 100000
elif mode == "one_legacy":
    txs = tx_list([legacy_tx(0, 21000)])
    count = 1
    gas_left[0] = 0
    floors[0] = 21000
    block_gas_limit = 30000
elif mode == "two_overflow":
    txs = tx_list([legacy_tx(0, 21000), legacy_tx(1, 50000)])
    count = 2
    gas_left[0] = 0
    gas_left[1] = 0
    floors[0] = 21000
    floors[1] = 21000
    block_gas_limit = 70000
elif mode == "bad_remaining":
    txs = tx_list([legacy_tx(0, 21000)])
    count = 1
    gas_left[0] = 22000
    floors[0] = 21000
    block_gas_limit = 30000
elif mode == "count_mismatch":
    txs = tx_list([legacy_tx(0, 21000), legacy_tx(1, 50000)])
    count = 1
    gas_left[0] = 0
    floors[0] = 21000
    block_gas_limit = 100000
elif mode == "typed_2930":
    txs = tx_list([typed_2930_tx(0, 62000)])
    count = 1
    gas_left[0] = 1000
    floors[0] = 21000
    block_gas_limit = 100000
else:
    raise SystemExit(f"unknown mode: {mode}")

wd_off = tx_off + len(txs)
payload[504:508] = struct.pack("<I", tx_off)
payload[508:512] = struct.pack("<I", wd_off)
payload[tx_off:tx_off + len(txs)] = txs

image = bytearray(0x1400)
image[:len(payload)] = payload
base = 0x1000
struct.pack_into("<Q", image, base, count)
for i, value in enumerate(gas_left):
    struct.pack_into("<Q", image, base + 8 + 8 * i, value)
for i, value in enumerate(refunds):
    struct.pack_into("<Q", image, base + 136 + 8 * i, value)
for i, value in enumerate(floors):
    struct.pack_into("<Q", image, base + 264 + 8 * i, value)
struct.pack_into("<Q", image, base + 392, block_gas_limit)

with open(in_path, "wb") as f:
    f.write(image)

expected = [int(x, 0) for x in expected_csv.split(",")]
with open(expected_path, "wb") as f:
    for value in expected:
        f.write(struct.pack("<Q", value))
PY

  "$ZISKEMU" -e gen-out/zisk_block_verdict_gas_result_arena.elf \
    -i "$in_file" -o "$out_file" \
    >"$REPO_ROOT/gen-out/zisk_block_verdict_gas_result_arena_${name}.emu.log" 2>&1 || true

  if ! cmp -n "$(wc -c <"$expected_file")" -s "$expected_file" "$out_file"; then
    echo "FAIL $name" >&2
    echo "expected:" >&2
    od -An -tu8 "$expected_file" >&2
    echo "actual:" >&2
    od -An -tu8 -N "$(wc -c <"$expected_file")" "$out_file" >&2 || true
    echo "emu log:" >&2
    tail -80 "$REPO_ROOT/gen-out/zisk_block_verdict_gas_result_arena_${name}.emu.log" >&2
    return 1
  fi
}

FAILED=0
run_case "empty"         "empty"         "0,0,0,0,0,0,0,0,0,0,0,0,0" || FAILED=1
run_case "one_legacy"    "one_legacy"    "0,1,1,0,0,21000,21000,21000,0,0,21000,0,1" || FAILED=1
run_case "two_overflow"  "two_overflow"  "0,2,2,0,0,21000,21000,21000,1,2,21000,0,2" || FAILED=1
run_case "bad_remaining" "bad_remaining" "4,1,1,1,1,21000,0,0,255,0,0,255,0" || FAILED=1
run_case "count_mismatch" "count_mismatch" "2,2,1,0,1,21000,0,0,255,0,0,255,0" || FAILED=1
run_case "typed_2930"    "typed_2930"    "0,1,1,0,0,62000,61000,61000,0,0,61000,1,0" || FAILED=1

if [[ "$FAILED" -ne 0 ]]; then
  exit 1
fi

echo "==> PASS: block_verdict_gas_result_arena prepares runtime gas-result arrays"
