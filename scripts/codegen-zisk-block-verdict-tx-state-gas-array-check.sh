#!/usr/bin/env bash
# codegen-zisk-block-verdict-tx-state-gas-array-check.sh -- g8zeq.1.4.3.
#
# Fill a per-tx EIP-8037 state-gas array from an SSZ transactions section.
# Each entry: (is_creation ? 183600 : 0) + auth_count * 218790.
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

echo "==> emit zisk_block_verdict_tx_state_gas_array ELF"
lake exe codegen --program zisk_block_verdict_tx_state_gas_array --halt linux93 \
  -o gen-out/zisk_block_verdict_tx_state_gas_array

REPO_ROOT="$(pwd)"

# run_case <name> <spec> <expected_csv>
#   spec : ';'-separated tx descriptors "type:to:nauth" (to = 'A' addr or '' create)
run_case() {
  local name="$1" spec="$2" expected="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_bvtsg_array_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_bvtsg_array_${name}.output"

  SPEC="$spec" uv run --directory execution-specs --quiet python3 -c "
import struct, sys, os, rlp
ALICE = bytes.fromhex('aa'*20)
R = int.from_bytes(bytes([0x11]*32), 'big')
S = int.from_bytes(bytes([0x22]*32), 'big')

def build(t, to, nauth):
    to_b = ALICE if to == 'A' else b''
    if t == 'legacy':
        return rlp.encode([1, 10**9, 21000, to_b, 10**18, b'', 27, R, S])
    if t == 'eip1559':
        inner = [1, 7, 10**9, 2*10**9, 21000, to_b, 10**18, b'', [], 1, R, S]
        return b'\x02' + rlp.encode(inner)
    if t == 'eip7702':
        al = [[1, bytes([0xcc]*20), 0, 27, R, S] for _ in range(nauth)]
        inner = [1, 7, 10**9, 2*10**9, 21000, to_b, 10**18, b'', [], al, 1, R, S]
        return b'\x04' + rlp.encode(inner)
    raise ValueError(t)

txs = []
for d in os.environ['SPEC'].split(';'):
    t, to, na = d.split(':')
    txs.append(build(t, to, int(na)))

n = len(txs)
offs, cur = [], 4*n
for tx in txs:
    offs.append(cur); cur += len(tx)
section = b''.join(struct.pack('<I', o) for o in offs) + b''.join(txs)

with open(sys.argv[1], 'wb') as f:
    # ziskemu maps the input file to 0x40000000+8, so the probe reads section_len
    # at +8 (= file[0:8]), expected count at +16 (= file[8:16]), section at +24.
    f.write(struct.pack('<Q', len(section))) # file[0:8]  -> +8  section len
    f.write(struct.pack('<Q', n))            # file[8:16] -> +16 expected count
    f.write(section)                         # file[16:]  -> +24 section
    pad = (-(16 + len(section))) % 8
    if pad: f.write(b'\x00'*pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_verdict_tx_state_gas_array.elf \
    -i "$in_file" -o "$out_file" -n 2000000 \
    >"$REPO_ROOT/gen-out/zisk_bvtsg_array_${name}.emu.log" 2>&1 || true

  local status; status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  if [[ "$status" != "0000000000000000" ]]; then
    printf "  %-22s FAIL status=0x%s\n" "$name" "$status"
    return 1
  fi
  local i=0 got=()
  IFS=',' read -ra exp <<< "$expected"
  for _ in "${exp[@]}"; do
    local off=$((8 + i*8))
    local hx; hx="$(dd if="$out_file" bs=1 skip=$off count=8 2>/dev/null | xxd -p | tr -d '\n')"
    got+=("$(python3 -c "print(int.from_bytes(bytes.fromhex('$hx'),'little'))")")
    i=$((i+1))
  done
  local got_csv; got_csv="$(IFS=','; echo "${got[*]}")"
  if [[ "$got_csv" != "$expected" ]]; then
    printf "  %-22s FAIL array=[%s] expected=[%s]\n" "$name" "$got_csv" "$expected"
    return 1
  fi
  printf "  %-22s OK   array=[%s]\n" "$name" "$got_csv"
  return 0
}

FAILED=0
run_case "one_call"      "legacy:A:0"                          "0"                || FAILED=1
run_case "call_create"   "legacy:A:0;legacy::0"                "0,183600"         || FAILED=1
run_case "mixed_three"   "eip1559:A:0;eip7702:A:1;legacy::0"   "0,218790,183600"  || FAILED=1
run_case "two_creates"   "legacy::0;eip1559::0"                "183600,183600"    || FAILED=1
run_case "auth_heavy"    "eip7702:A:2;eip7702::1"              "437580,402390"    || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_verdict_tx_state_gas_array fills the per-tx state-gas array"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
