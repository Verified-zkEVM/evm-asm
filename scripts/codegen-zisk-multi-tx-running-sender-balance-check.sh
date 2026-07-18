#!/usr/bin/env bash
# codegen-zisk-multi-tx-running-sender-balance-check.sh -- B2.2 running balance probe.
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

echo "==> emit zisk_multi_tx_running_sender_balance ELF"
lake exe codegen --program zisk_multi_tx_running_sender_balance --halt linux93 \
  -o gen-out/zisk_multi_tx_running_sender_balance

grep -q "li a2, 9523" gen-out/zisk_multi_tx_running_sender_balance.s
grep -q "\.zero 609472" gen-out/zisk_multi_tx_running_sender_balance.s

REPO_ROOT="$(pwd)"

distinct_spec() {
  local n="$1"
  python3 - "$n" <<'PY'
import sys
n = int(sys.argv[1])
print(','.join(f'{i + 1}:100:1:1' for i in range(n)))
PY
}

run_case() {
  local name="$1" spec="$2" expected_status="$3" expected_count="$4" expected_table="$5"
  local in_file="$REPO_ROOT/gen-out/zisk_multi_tx_running_sender_balance_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_multi_tx_running_sender_balance_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_multi_tx_running_sender_balance_${name}.expected"

  python3 - "$spec" "$expected_status" "$expected_count" "$expected_table" "$in_file" "$exp_file" <<'PY'
import struct
import sys

spec, expected_status, expected_count, expected_table, in_path, exp_path = sys.argv[1:]

def u256(n: int) -> bytes:
    return n.to_bytes(32, "big")

def sender(seed: int) -> bytes:
    return seed.to_bytes(20, "big") + bytes(12)

rows = []
for raw in filter(None, spec.split(",")):
    seed_s, pre_s, upfront_s, debit_s = raw.split(":")
    rows.append(sender(int(seed_s)) + u256(int(pre_s)) + u256(int(upfront_s)) + u256(int(debit_s)))

payload = struct.pack("<Q", len(rows)) + b"".join(rows)
with open(in_path, "wb") as f:
    f.write(payload)

expected = bytearray(256)
struct.pack_into("<Q", expected, 0, int(expected_status))
struct.pack_into("<Q", expected, 8, int(expected_count))
off = 16
if expected_table and expected_table != "COUNT_ONLY":
    for item in expected_table.split(","):
        seed_s, balance_s = item.split(":")
        expected[off : off + 32] = sender(int(seed_s))
        expected[off + 32 : off + 64] = u256(int(balance_s))
        off += 64
with open(exp_path, "wb") as f:
    f.write(expected)
PY

  local steps=2000000
  if [[ "$name" == "distinct1024" || "$name" == "distinct1025" ]]; then
    steps=200000000
  fi

  "$ZISKEMU" -e gen-out/zisk_multi_tx_running_sender_balance.elf \
    -i "$in_file" -o "$out_file" -n "$steps" \
    >"$REPO_ROOT/gen-out/zisk_multi_tx_running_sender_balance_${name}.emu.log" 2>&1 || true

    local cmp_len=256
  if [[ "$expected_status" != "0" || "$expected_table" == "COUNT_ONLY" ]]; then
    cmp_len=16
  fi
  if cmp -n "$cmp_len" -s "$out_file" "$exp_file"; then
    printf "  %-28s OK\n" "$name"
  else
    printf "  %-28s FAIL\n" "$name"
    printf "    expected: %s\n" "$(xxd -p -l 160 "$exp_file" | tr -d '\n')"
    printf "    actual:   %s\n" "$(xxd -p -l 160 "$out_file" | tr -d '\n')"
    printf "    emulator log: %s\n" "$REPO_ROOT/gen-out/zisk_multi_tx_running_sender_balance_${name}.emu.log"
    return 1
  fi
}

FAILED=0
run_case "same_sender_valid" "1:100:50:30,1:999:50:40" 0 1 "1:30" || FAILED=1
run_case "distinct_senders" "1:100:50:30,2:80:40:10" 0 2 "1:70,2:70" || FAILED=1
run_case "distinct_17" "1:100:1:1,2:100:1:1,3:100:1:1,4:100:1:1,5:100:1:1,6:100:1:1,7:100:1:1,8:100:1:1,9:100:1:1,10:100:1:1,11:100:1:1,12:100:1:1,13:100:1:1,14:100:1:1,15:100:1:1,16:100:1:1,17:100:1:1" 0 17 "COUNT_ONLY" || FAILED=1
run_case "distinct1024" "$(distinct_spec 1024)" 0 1024 "COUNT_ONLY" || FAILED=1
run_case "distinct1025" "$(distinct_spec 1025)" 0 1025 "COUNT_ONLY" || FAILED=1
run_case "same_sender_upfront" "1:50:30:30,1:999:25:25" 1 1 "1:20" || FAILED=1
run_case "first_sender_upfront" "3:10:11:1" 1 0 "" || FAILED=1
run_case "settled_debit_underflow" "4:10:5:11" 2 0 "" || FAILED=1

echo
if [[ "$FAILED" -eq 0 ]]; then
  echo "==> PASS: multi_tx_running_sender_balance maintains ordered per-sender balances"
else
  echo "==> FAIL"
  exit 1
fi
