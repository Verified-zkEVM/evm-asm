#!/usr/bin/env bash
# codegen-zisk-validate-header-full-check.sh -- PR-K75.
#
# Run header validation checks (post_merge, extra_data,
# basic, gas_limit, base_fee, excess_blob_gas) in sequence and verify the
# composite return code.
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

echo "==> emit zisk_validate_header_full ELF"
lake exe codegen --program zisk_validate_header_full --halt linux93 \
  -o gen-out/zisk_validate_header_full

REPO_ROOT="$(pwd)"

EMPTY_OMMERS_HASH="1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"

# build_test <name> <expected_status>
#   <this_ommers> <this_diff> <this_nonce_hex>
#   <this_extra_data_hex>
#   <this_number> <this_timestamp> <this_gas_limit> <this_gas_used> <this_base_fee>
#   <parent_number> <parent_timestamp> <parent_gas_limit> <parent_gas_used> <parent_base_fee>
#   [this_blob_gas_used] [this_excess_blob_gas] [parent_blob_gas_used] [parent_excess_blob_gas]
build_test() {
  local name="$1" expected_status="$2"
  local this_ommers="$3" this_diff="$4" this_nonce="$5"
  local this_extra="$6"
  local this_number="$7" this_ts="$8" this_gas_limit="$9" this_gas_used="${10}" this_bf="${11}"
  local p_number="${12}" p_ts="${13}" p_gas_limit="${14}" p_gas_used="${15}" p_bf="${16}"
  local this_blob_gas_used="${17:-0}" this_excess_blob_gas="${18:-0}"
  local parent_blob_gas_used="${19:-0}" parent_excess_blob_gas="${20:-0}"

  local in_file="$REPO_ROOT/gen-out/zisk_validate_header_full_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_validate_header_full_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp

# Build this-header RLP (15 fields)
this_fields = [
    b'\x11' * 32,                              # 0: parent_hash
    bytes.fromhex('$this_ommers'),             # 1: ommers_hash
    b'\x33' * 20,                              # 2: coinbase
    b'\x44' * 32,                              # 3: state_root
    b'\x55' * 32,                              # 4: transactions_root
    b'\x66' * 32,                              # 5: receipts_root
    b'\x00' * 256,                             # 6: bloom
    $this_diff,                                # 7: difficulty
    $this_number,                              # 8: number
    $this_gas_limit,                           # 9: gas_limit
    $this_gas_used,                            # 10: gas_used
    $this_ts,                                  # 11: timestamp
    bytes.fromhex('$this_extra'),              # 12: extra_data
    b'\x77' * 32,                              # 13: prev_randao
    bytes.fromhex('$this_nonce'),              # 14: nonce
]
rlp_bytes = rlp.encode(this_fields)
if len(rlp_bytes) > 1024:
    raise RuntimeError(f'rlp too long for fixture: {len(rlp_bytes)}')

# Build extended-decode structs (144 B each)
def build_struct(parent_hash, state_root, number, ts, gl, gu, bf, blob_gas_used=0, excess_blob_gas=0):
    out  = parent_hash
    out += state_root
    out += struct.pack('<Q', number)
    out += struct.pack('<Q', ts)
    out += struct.pack('<Q', gl)
    out += struct.pack('<Q', gu)
    out += bf.to_bytes(32, 'big')
    out += struct.pack('<Q', blob_gas_used)
    out += struct.pack('<Q', excess_blob_gas)
    assert len(out) == 144
    return out

this_struct   = build_struct(b'\x11' * 32, b'\x44' * 32,
                              $this_number, $this_ts,
                              $this_gas_limit, $this_gas_used, $this_bf,
                              $this_blob_gas_used, $this_excess_blob_gas)
parent_struct = build_struct(b'\x22' * 32, b'\x55' * 32,
                              $p_number, $p_ts,
                              $p_gas_limit, $p_gas_used, $p_bf,
                              $parent_blob_gas_used, $parent_excess_blob_gas)

# Assemble input file
out  = struct.pack('<Q', len(rlp_bytes))   # bytes 0..8: rlp_len
out += rlp_bytes
out += b'\x00' * (1024 - len(rlp_bytes))   # pad rlp area to 1024 B
out += this_struct                          # 144 B
out += parent_struct                        # 144 B
assert len(out) == 8 + 1024 + 288

with open(sys.argv[1], 'wb') as f:
    f.write(out)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_validate_header_full.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_validate_header_full_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local exp_le; exp_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"

  if [[ "$actual" == "$exp_le" ]]; then
    printf "  %-30s OK   status=%d\n" "$name" "$expected_status"
    return 0
  else
    printf "  %-30s FAIL  expected status=%d got 0x%s\n" "$name" "$expected_status" "$actual"
    return 1
  fi
}

ZERO_NONCE="0000000000000000"

FAILED=0
# All pass: gas_used == parent_gas_target → base_fee unchanged
# parent_gas_limit=30000000, parent_gas_used=15000000 (= target), parent.bf=50 gwei
# this matches struct: gas_limit=30000000, gas_used=15000000, base_fee=50 gwei (unchanged)
# this RLP has same fields; nonce=0; difficulty=0; ommers=EMPTY; extra_data <= 32B
GWEI=$(python3 -c "print(10**9)")
BF_50=$(python3 -c "print(50 * $GWEI)")

build_test "all_pass_at_target" 0 \
  "$EMPTY_OMMERS_HASH" 0 "$ZERO_NONCE" \
  "74657374" \
  101 1700000100 30000000 15000000 "$BF_50" \
  100 1700000000 30000000 15000000 "$BF_50" || FAILED=1

# Step 1 fail: ommers_hash mismatch → status = 100 + 1 = 101
build_test "step1_ommers_fail" 101 \
  "0000000000000000000000000000000000000000000000000000000000000000" 0 "$ZERO_NONCE" \
  "74657374" \
  101 1700000100 30000000 15000000 "$BF_50" \
  100 1700000000 30000000 15000000 "$BF_50" || FAILED=1

# Step 1 fail: difficulty != 0 → status = 102
build_test "step1_diff_nonzero" 102 \
  "$EMPTY_OMMERS_HASH" 1 "$ZERO_NONCE" \
  "74657374" \
  101 1700000100 30000000 15000000 "$BF_50" \
  100 1700000000 30000000 15000000 "$BF_50" || FAILED=1

# Step 2 fail: extra_data > 32 bytes → status = 200 + 1 = 201
build_test "step2_extra_too_long" 201 \
  "$EMPTY_OMMERS_HASH" 0 "$ZERO_NONCE" \
  "$(printf 'aa%.0s' $(seq 1 40))" \
  101 1700000100 30000000 15000000 "$BF_50" \
  100 1700000000 30000000 15000000 "$BF_50" || FAILED=1

# Step 3 fail: gas_used > gas_limit → 301
# struct has this.gas_used=31M, this.gas_limit=30M
# (RLP and struct must agree for base_fee step; we use struct values)
build_test "step3_gas_used_overshoot" 301 \
  "$EMPTY_OMMERS_HASH" 0 "$ZERO_NONCE" \
  "74657374" \
  101 1700000100 30000000 31000000 "$BF_50" \
  100 1700000000 30000000 15000000 "$BF_50" || FAILED=1

# Step 3 fail: number not parent+1 → 302
build_test "step3_number_skip" 302 \
  "$EMPTY_OMMERS_HASH" 0 "$ZERO_NONCE" \
  "74657374" \
  102 1700000100 30000000 15000000 "$BF_50" \
  100 1700000000 30000000 15000000 "$BF_50" || FAILED=1

# Step 3 fail: timestamp not strictly greater → 303
build_test "step3_timestamp_eq" 303 \
  "$EMPTY_OMMERS_HASH" 0 "$ZERO_NONCE" \
  "74657374" \
  101 1700000000 30000000 15000000 "$BF_50" \
  100 1700000000 30000000 15000000 "$BF_50" || FAILED=1

# Step 4 fail: gas_limit jumped too far → 402
# this.gas_limit = parent.gas_limit + parent.gas_limit/1024 (= 30029296)
# But we also need this.gas_used <= this.gas_limit. Let this.gas_used = 1 to pass step 3.
build_test "step4_gas_limit_jump" 402 \
  "$EMPTY_OMMERS_HASH" 0 "$ZERO_NONCE" \
  "74657374" \
  101 1700000100 30029296 1 "$BF_50" \
  100 1700000000 30000000 15000000 "$BF_50" || FAILED=1

# Step 5 fail: base_fee != calculated → 501
# parent.gas_used == target → expected = parent.base_fee = BF_50.
# So this.base_fee = BF_50 + 1 should fail step 5.
WRONG_BF=$((BF_50 + 1))
build_test "step5_base_fee_wrong" 501 \
  "$EMPTY_OMMERS_HASH" 0 "$ZERO_NONCE" \
  "74657374" \
  101 1700000100 30000000 15000000 "$WRONG_BF" \
  100 1700000000 30000000 15000000 "$BF_50" || FAILED=1


# Step 6 fail: this.excess_blob_gas must follow the Amsterdam recurrence.
build_test "step6_excess_blob_wrong" 602 \
  "$EMPTY_OMMERS_HASH" 0 "$ZERO_NONCE" \
  "74657374" \
  101 1700000100 30000000 15000000 "$BF_50" \
  100 1700000000 30000000 15000000 "$BF_50" \
  0 1 0 0 || FAILED=1

# All pass: Amsterdam high-base-fee schedule branch.
# parent_blob_gas >= target and parent.base_fee > 16 * blob_price(0), so
# expected excess = parent_excess + parent_blob_gas_used // 3.
build_test "all_pass_excess_schedule" 0 \
  "$EMPTY_OMMERS_HASH" 0 "$ZERO_NONCE" \
  "" \
  101 1700000100 30000000 15000000 "$BF_50" \
  100 1700000000 30000000 15000000 "$BF_50" \
  0 917504 2752512 0 || FAILED=1

# Step 6 fail in the schedule branch.
build_test "step6_excess_schedule_wrong" 602 \
  "$EMPTY_OMMERS_HASH" 0 "$ZERO_NONCE" \
  "" \
  101 1700000100 30000000 15000000 "$BF_50" \
  100 1700000000 30000000 15000000 "$BF_50" \
  0 917505 2752512 0 || FAILED=1

# Step 6 fail: schedule branch where the spec's U64 `blob_gas_used * 7`
# overflows ((2^64-1)//7 + 1 = 2635249153387078803) → OverflowError in the
# spec, status 601 here. this.excess matches the unguarded `used // 3` value
# so a guest missing the overflow guard would wrongly return 0.
MUL_OVERFLOW_USED=2635249153387078803
MUL_OVERFLOW_EXCESS=$(python3 -c "print($MUL_OVERFLOW_USED // 3)")
build_test "step6_blob_mul_overflow" 601 \
  "$EMPTY_OMMERS_HASH" 0 "$ZERO_NONCE" \
  "" \
  101 1700000100 30000000 15000000 "$BF_50" \
  100 1700000000 30000000 15000000 "$BF_50" \
  0 "$MUL_OVERFLOW_EXCESS" "$MUL_OVERFLOW_USED" 0 || FAILED=1

# All pass: schedule branch at the largest non-overflowing blob_gas_used
# ((2^64-1)//7, where used * 7 = 2^64-2 still fits in U64).
MUL_BOUND_USED=2635249153387078802
MUL_BOUND_EXCESS=$(python3 -c "print($MUL_BOUND_USED // 3)")
build_test "all_pass_blob_mul_at_bound" 0 \
  "$EMPTY_OMMERS_HASH" 0 "$ZERO_NONCE" \
  "" \
  101 1700000100 30000000 15000000 "$BF_50" \
  100 1700000000 30000000 15000000 "$BF_50" \
  0 "$MUL_BOUND_EXCESS" "$MUL_BOUND_USED" 0 || FAILED=1

# All pass: realistic Holesky 60% used scenario
# parent.gas_used=18000000, target=15000000 (above), bf grows
# expected = bf + delta where delta = max((bf*3M/15M)/8, 1) = (bf*0.2)/8 = bf*0.025
BF_8=$(python3 -c "print(8 * $GWEI)")
EXP_HOLESKY=$(python3 -c "
pbf, pgl, pgu = $BF_8, 30000000, 18000000
target = pgl // 2
delta = pgu - target
pfgd = pbf * delta
tfgd = pfgd // target
bfd = max(tfgd // 8, 1)
print(pbf + bfd)
")
build_test "all_pass_holesky_60" 0 \
  "$EMPTY_OMMERS_HASH" 0 "$ZERO_NONCE" \
  "" \
  101 1700000100 30000000 18000000 "$EXP_HOLESKY" \
  100 1700000000 30000000 18000000 "$BF_8" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: validate_header_full runs all 6 checks and routes via composite codes"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
