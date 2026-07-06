#!/usr/bin/env bash
# codegen-zisk-sstore-gas-refund-outcome-check.sh -- verify the Amsterdam
# SSTORE gas/refund outcome helper against execution-specs branch cases.
set -euo pipefail
cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_sstore_gas_refund_outcome ELF"
lake exe codegen --program zisk_sstore_gas_refund_outcome --halt linux93 \
  -o gen-out/zisk_sstore_gas_refund_outcome >/dev/null

word32() {
  local value="$1"
  python3 - "$value" <<'PY'
import sys
value = int(sys.argv[1], 0)
sys.stdout.buffer.write(value.to_bytes(32, "big"))
PY
}

make_input() {
  local path="$1" warm="$2" original="$3" current="$4" new="$5"
  python3 - "$path" "$warm" "$original" "$current" "$new" <<'PY'
import struct, sys
path, warm, original, current, new = sys.argv[1:]
body = struct.pack("<Q", int(warm, 0))
for value in (original, current, new):
    body += int(value, 0).to_bytes(32, "big")
with open(path, "wb") as f:
    f.write(body)
PY
}

run_case() {
  local name="$1" warm="$2" original="$3" current="$4" new="$5"
  local exp_gas="$6" exp_refund="$7" exp_changed="$8" exp_credit="$9"
  local in_file="gen-out/sstore_gas_${name}.input"
  local out_file="gen-out/sstore_gas_${name}.output"
  make_input "$in_file" "$warm" "$original" "$current" "$new"
  "$ZISKEMU" -e gen-out/zisk_sstore_gas_refund_outcome.elf \
    -i "$in_file" -o "$out_file" -n 2000000 >/dev/null 2>&1 </dev/null \
    || { echo "  ERROR  $name"; return 1; }
  local status gas refund_raw changed accessed credit
  status="$(od -An -tu8 -j 0 -N 8 "$out_file" | tr -d ' \n')"
  gas="$(od -An -tu8 -j 8 -N 8 "$out_file" | tr -d ' \n')"
  refund_raw="$(od -An -tu8 -j 16 -N 8 "$out_file" | tr -d ' \n')"
  changed="$(od -An -tu8 -j 24 -N 8 "$out_file" | tr -d ' \n')"
  accessed="$(od -An -tu8 -j 32 -N 8 "$out_file" | tr -d ' \n')"
  credit="$(od -An -tu8 -j 40 -N 8 "$out_file" | tr -d ' \n')"
  local refund
  refund="$(python3 - "$refund_raw" <<'PY'
import sys
u = int(sys.argv[1])
if u >= 1 << 63:
    u -= 1 << 64
print(u)
PY
)"
  if [[ "$status" == "0" && "$gas" == "$exp_gas" && "$refund" == "$exp_refund" &&
        "$changed" == "$exp_changed" && "$accessed" == "1" && "$credit" == "$exp_credit" ]]; then
    echo "  PASS   $name gas=$gas refund=$refund changed=$changed credit=$credit"
  else
    echo "  FAIL   $name"
    echo "    expected status=0 gas=$exp_gas refund=$exp_refund changed=$exp_changed accessed=1 credit=$exp_credit"
    echo "    actual   status=$status gas=$gas refund=$refund changed=$changed accessed=$accessed credit=$credit"
    return 1
  fi
}

fail=0
# Amsterdam schedule: the regular gas has NO EIP-2200 SET split (a zero-origin
# creation charges 2900 like any clean-changing write; the 97,920 EIP-8037 state
# gas is the CALLER's charge, surfaced only via the credit flag on zero-restore),
# and the restore refund is uniformly 2800.
# warm original/current/new -> gas, refund_delta, changed, state_credit
run_case warm_set_zero_to_nonzero 1 0 0 1 2900 0 1 0 || fail=1
run_case cold_set_zero_to_nonzero 0 0 0 1 5000 0 1 0 || fail=1
run_case warm_reset_nonzero       1 5 5 7 2900 0 1 0 || fail=1
run_case warm_noop                1 5 5 5 100 0 0 0 || fail=1
run_case warm_clear_refund        1 5 5 0 2900 4800 1 0 || fail=1
run_case warm_reverse_clear       1 5 0 7 100 -4800 1 0 || fail=1
run_case warm_restore_zero        1 0 7 0 100 2800 1 1 || fail=1
run_case warm_restore_nonzero     1 5 7 5 100 2800 1 0 || fail=1

[[ "$fail" -eq 0 ]] && echo "==> PASS: SSTORE gas/refund outcome matches reference cases" \
  || { echo "==> FAIL"; exit 1; }
