#!/usr/bin/env bash
# codegen-zisk-mpt-indexed-trie-root-small-check.sh
#
# Verify mpt_indexed_trie_root_small against execution-specs'
# ethereum.merkle_patricia_trie root implementation for keys rlp(0..N-1).
set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_mpt_indexed_trie_root_small ELF"
lake exe codegen --program zisk_mpt_indexed_trie_root_small --halt linux93 \
  -o gen-out/zisk_mpt_indexed_trie_root_small

read_u64() { od -An -tu8 -j "$2" -N 8 "$1" | tr -d ' \n'; }

run_case() {
  local name="$1"
  local values_py="$2"
  local exp_status="$3"
  local in_file="$REPO_ROOT/gen-out/zisk_mpt_indexed_trie_root_small_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_indexed_trie_root_small_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_mpt_indexed_trie_root_small_${name}.expected"

  uv run --directory execution-specs --quiet python3 - "$in_file" "$exp_file" <<PY
import sys, struct
from ethereum.merkle_patricia_trie import Trie, trie_set, root
from ethereum_rlp import rlp
from ethereum_types.bytes import Bytes
from ethereum_types.numeric import Uint

values = $values_py
vals = [bytes.fromhex(v) for v in values]
trie = Trie(secured=False, default=None)
for i, value in enumerate(vals):
    trie_set(trie, Bytes(rlp.encode(Uint(i))), Bytes(value))
expected = bytes(root(trie))

with open(sys.argv[1], "wb") as f:
    f.write(struct.pack("<Q", len(vals)))
    for value in vals:
        f.write(struct.pack("<Q", len(value)))
    for value in vals:
        f.write(value)
        f.write(b"\\x00" * ((-len(value)) % 8))
with open(sys.argv[2], "w") as f:
    f.write(expected.hex())
PY

  if ! "$ZISKEMU" -e gen-out/zisk_mpt_indexed_trie_root_small.elf \
        -i "$in_file" -o "$out_file" -n 20000000 >/dev/null 2>&1 </dev/null; then
    printf "  %-24s ERROR ziskemu\n" "$name"
    return 1
  fi

  local st actual expected
  st="$(read_u64 "$out_file" 32)"
  actual="$(od -An -tx1 -j 0 -N 32 "$out_file" | tr -d ' \n')"
  expected="$(cat "$exp_file")"
  if [[ "$st" == "$exp_status" ]]; then
    if [[ "$exp_status" != "0" || "$actual" == "$expected" ]]; then
      printf "  %-24s OK   status=%s root=%s..\n" "$name" "$st" "${actual:0:16}"
      return 0
    fi
  fi

  printf "  %-24s FAIL status=%s/%s\n" "$name" "$st" "$exp_status"
  printf "      expected %s\n" "$expected"
  printf "      got      %s\n" "$actual"
  return 1
}

LONG0="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
LONG1="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
LARGE0="$(printf 'cc%.0s' {1..64})"
LARGE1="$(printf 'dd%.0s' {1..64})"

FAILED=0
run_case "empty" "[]" 0 || FAILED=1
run_case "one_short" "['01']" 0 || FAILED=1
run_case "one_large" "[('ab' * 200000)]" 0 || FAILED=1
run_case "two_short" "['01','02']" 0 || FAILED=1
run_case "three_mixed" "['01','$LONG0','03']" 0 || FAILED=1
run_case "four_long" "['$LONG0','$LONG1','$LONG0','$LONG1']" 0 || FAILED=1

GROUPED_LARGE="$(python3 - <<PYGROUP
vals = [('$LARGE0' if i % 2 == 0 else '$LARGE1') for i in range(18)]
print("[" + ",".join(repr(v) for v in vals) + "]")
PYGROUP
)"
run_case "two_large_same_first" "$GROUPED_LARGE" 0 || FAILED=1

ONE_GROUP_16_LARGE="$(python3 - <<PYGROUP16
vals = [('$LARGE0' if i % 2 == 0 else '$LARGE1') for i in range(32)]
print("[" + ",".join(repr(v) for v in vals) + "]")
PYGROUP16
)"
run_case "one_group_16_large" "$ONE_GROUP_16_LARGE" 0 || FAILED=1

SPREAD_FIRST_NIBBLES="$(python3 - <<PYSPREAD
vals = [('$LARGE0' if i % 3 == 0 else '$LARGE1') for i in range(33)]
print("[" + ",".join(repr(v) for v in vals) + "]")
PYSPREAD
)"
run_case "spread_0_1_2_8" "$SPREAD_FIRST_NIBBLES" 0 || FAILED=1

# Row-12970-shaped: 34 large indexed values, scaled down to keep the probe
# fast while still exceeding the 128 KiB mpt leaf payload buffer class.
ROW_12970_SCALED="[(f'{i % 256:02x}' * 4096) for i in range(34)]"
run_case "row12970_scaled_34" "$ROW_12970_SCALED" 0 || FAILED=1

MANY_VALUES="$(python3 - <<'PY'
vals = [f"{i % 256:02x}" for i in range(128)]
print("[" + ",".join(repr(v) for v in vals) + "]")
PY
)"
run_case "max_old_128" "$MANY_VALUES" 0 || FAILED=1

OVER_128_VALUES="$(python3 - <<'PY'
vals = [(f"{i % 256:02x}" * 64) for i in range(129)]
print("[" + ",".join(repr(v) for v in vals) + "]")
PY
)"
run_case "over_128_keys" "$OVER_128_VALUES" 0 || FAILED=1

# 257 entries: index 256 needs a 3-byte RLP index key (rlp(256)=0x82 0x01 0x00 ->
# nibbles [8,2,0,1,0,0]). Now supported (was rejected under the old 256 cap).
KEYS_257="$(python3 - <<'PY'
vals = [f"{i % 256:02x}" for i in range(257)]
print("[" + ",".join(repr(v) for v in vals) + "]")
PY
)"
run_case "keys_257_three_byte" "$KEYS_257" 0 || FAILED=1

# 300 entries: more 3-byte index keys (256..299).
KEYS_300="$(python3 - <<'PY'
vals = [f"{i % 256:02x}" for i in range(300)]
print("[" + ",".join(repr(v) for v in vals) + "]")
PY
)"
run_case "keys_300_three_byte" "$KEYS_300" 0 || FAILED=1

# New cap: >=2049 entries is rejected (status 1) by mpt_indexed_trie_root_small.
OVER_CAP="$(python3 - <<'PY'
vals = [f"{i % 256:02x}" for i in range(2049)]
print("[" + ",".join(repr(v) for v in vals) + "]")
PY
)"
run_case "over_cap_2049" "$OVER_CAP" 1 || FAILED=1

[[ "$FAILED" -eq 0 ]] && echo "==> PASS: indexed trie root builder matches execution-specs" \
  || { echo "==> FAIL"; exit 1; }
