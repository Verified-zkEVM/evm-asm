#!/usr/bin/env bash
# codegen-zisk-eip8037-tx-state-gas-check.sh
#
# Focused EIP-8037 Amsterdam per-tx state-gas settlement probe. Mirrors
# execution-specs fork.py process_transaction (v0.6, fork.py:1174):
#   tx_state_gas = intrinsic_state_gas + tx_output.state_gas_used
#
# No v0.5.0 creation-revert refund subtraction: failed/colliding creation
# charges are credited back inside execution (credit_state_gas_refund), so the
# executed state gas the dispatcher captures is already net.
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

echo "==> emit zisk_eip8037_tx_state_gas ELF"
lake exe codegen --program zisk_eip8037_tx_state_gas --halt linux93 \
  -o gen-out/zisk_eip8037_tx_state_gas

REPO_ROOT="$(pwd)"

# run_case <name> <intrinsic_state_gas> <state_gas_used>
run_case() {
  local name="$1" isg="$2" sgu="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_eip8037_tx_state_gas_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_eip8037_tx_state_gas_${name}.output"

  python3 -c "
import struct, sys
with open(sys.argv[1], 'wb') as f:
    for x in ($isg, $sgu):
        f.write(struct.pack('<Q', x))
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_eip8037_tx_state_gas.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_eip8037_tx_state_gas_${name}.emu.log" 2>&1 || true

  if [[ ! -s "$out_file" ]]; then
    printf "  %-36s FAIL missing output\n" "$name"
    return 1
  fi

  local actual
  actual="$(python3 -c "
import struct, sys
with open(sys.argv[1], 'rb') as f:
    data = f.read(16)
if len(data) < 16:
    raise SystemExit('short output')
print(*struct.unpack('<QQ', data))
" "$out_file")"

  local expected_tsg=$(( isg + sgu ))
  local actual_status actual_tsg
  read -r actual_status actual_tsg <<<"$actual"

  if [[ "$actual_status" == "0" && "$actual_tsg" == "$expected_tsg" ]]; then
    printf "  %-36s OK   status=%s tx_state_gas=%s\n" "$name" "$actual_status" "$actual_tsg"
    return 0
  else
    printf "  %-36s FAIL status=%s/0 tx_state_gas=%s/%s\n" \
      "$name" "$actual_status" "$actual_tsg" "$expected_tsg"
    return 1
  fi
}

FAILED=0
# v0.6 identity: tx_state_gas = intrinsic_state_gas + state_gas_used
run_case "intrinsic_only"        183600 0 || FAILED=1
run_case "zero_all"              0 0 || FAILED=1
run_case "with_runtime_used"     183600 97920 || FAILED=1
run_case "executed_only"         0 97920 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: EIP-8037 tx state-gas settlement matches execution-spec arithmetic"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
