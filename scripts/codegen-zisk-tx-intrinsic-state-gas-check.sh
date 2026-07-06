#!/usr/bin/env bash
# codegen-zisk-tx-intrinsic-state-gas-check.sh -- g8zeq.1.4.3.1.
#
# Per-tx EIP-8037 intrinsic state-gas: in the BAL-replay path
#   tx_state_gas = (is_creation ? 183600 : 0) + auth_count * 218790
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

echo "==> emit zisk_tx_intrinsic_state_gas ELF"
lake exe codegen --program zisk_tx_intrinsic_state_gas --halt linux93 \
  -o gen-out/zisk_tx_intrinsic_state_gas

REPO_ROOT="$(pwd)"

# run_case <name> <tx_type> <to_hex> <num_auths> <expected_status> <expected_state_gas>
run_case() {
  local name="$1" t="$2" to="$3" nauth="$4" exp_status="$5" exp_gas="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_intrinsic_state_gas_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_intrinsic_state_gas_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
tx_type = '$t'
to_bytes = bytes.fromhex('$to')
nauth = int('$nauth')
R = int.from_bytes(bytes([0x11]*32), 'big')
S = int.from_bytes(bytes([0x22]*32), 'big')

if tx_type == 'legacy':
    tx = [1, 10**9, 21000, to_bytes, 10**18, b'', 27, R, S]
    tx_bytes = rlp.encode(tx)
elif tx_type == 'eip1559':
    inner = [1, 7, 10**9, 2*10**9, 21000, to_bytes, 10**18, b'', [], 1, R, S]
    tx_bytes = b'\x02' + rlp.encode(inner)
elif tx_type == 'eip7702':
    auth_list = [[1, bytes([0xcc]*20), 0, 27, R, S] for _ in range(nauth)]
    inner = [1, 7, 10**9, 2*10**9, 21000, to_bytes, 10**18, b'', [], auth_list, 1, R, S]
    tx_bytes = b'\x04' + rlp.encode(inner)
else:
    raise ValueError(tx_type)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(tx_bytes)))
    f.write(tx_bytes)
    pad = (-(8 + len(tx_bytes))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_tx_intrinsic_state_gas.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_tx_intrinsic_state_gas_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_gas_hex; actual_gas_hex="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$exp_status').to_bytes(8, 'little').hex())")"
  local exp_gas_le; exp_gas_le="$(python3 -c "print(int('$exp_gas').to_bytes(8, 'little').hex())")"
  local actual_gas; actual_gas="$(python3 -c "print(int.from_bytes(bytes.fromhex('$actual_gas_hex'), 'little'))")"

  if [[ "$actual_status" != "$exp_status_le" ]]; then
    printf "  %-28s FAIL status=0x%s expected=%d\n" "$name" "$actual_status" "$exp_status"
    return 1
  fi
  if [[ "$actual_gas_hex" != "$exp_gas_le" ]]; then
    printf "  %-28s FAIL state_gas=%s expected=%d\n" "$name" "$actual_gas" "$exp_gas"
    return 1
  fi
  printf "  %-28s OK   state_gas=%d\n" "$name" "$actual_gas"
  return 0
}

ALICE="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
EMPTY=""

FAILED=0
run_case "legacy_call"        legacy   "$ALICE" 0 0 0        || FAILED=1
run_case "legacy_create"      legacy   "$EMPTY"  0 0 183600   || FAILED=1
run_case "eip1559_call"       eip1559  "$ALICE" 0 0 0        || FAILED=1
run_case "eip1559_create"     eip1559  "$EMPTY"  0 0 183600   || FAILED=1
run_case "eip7702_1auth"      eip7702  "$ALICE" 1 0 218790   || FAILED=1
run_case "eip7702_2auth"      eip7702  "$ALICE" 2 0 437580   || FAILED=1
run_case "eip7702_create_1auth" eip7702 "$EMPTY" 1 0 402390  || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_intrinsic_state_gas computes per-tx EIP-8037 intrinsic state gas"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
