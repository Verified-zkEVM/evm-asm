#!/usr/bin/env bash
# codegen-zisk-running-bloom-log-commit-revert-check.sh
#
# Probe the hot running block bloom path with LOG-shaped updates. Mode 0
# commits a parent LOG update. Mode 1 snapshots that bloom, applies a child
# LOG update, returns the child with success=0, and expects rollback to the
# parent-only bloom.
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

echo "==> emit zisk_running_bloom_log_commit_revert ELF"
lake exe codegen --program zisk_running_bloom_log_commit_revert --halt linux93 \
  -o gen-out/zisk_running_bloom_log_commit_revert

REPO_ROOT="$(pwd)"

# run_case <name> <mode>
run_case() {
  local name="$1" mode="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_running_bloom_log_commit_revert_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_running_bloom_log_commit_revert_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_running_bloom_log_commit_revert_${name}.expected.hex"

  MODE="$mode" OUT_FILE="$in_file" EXPECTED_FILE="$exp_hex_file" \
    uv run --directory execution-specs --quiet python3 - <<'PYCASE'
import os, struct, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

mode = int(os.environ["MODE"])
out_file = os.environ["OUT_FILE"]
expected_file = os.environ["EXPECTED_FILE"]

parent_addr = bytes.fromhex("1111111111111111111111111111111111111111")
parent_topics = [bytes.fromhex("22" * 32)]
child_addr = bytes.fromhex("3333333333333333333333333333333333333333")
child_topics = [bytes.fromhex("44" * 32), bytes.fromhex("55" * 32)]

parent_log = rlp.encode([parent_addr, parent_topics, b"parent"])
child_log = rlp.encode([child_addr, child_topics, b"child payload ignored by bloom"])
assert len(parent_log) <= 256, len(parent_log)

bloom = bytearray(256)
def add_value(value):
    h = keccak256(value)
    for idx in (0, 2, 4):
        raw = int.from_bytes(h[idx:idx+2], "big") & 0x07FF
        bit = 0x07FF - raw
        bloom[bit // 8] |= 1 << (7 - (bit % 8))
def add_log(addr, topics):
    add_value(addr)
    for topic in topics:
        add_value(topic)

# Expected hot bloom after both modes is parent-only. Mode 1 deliberately
# applies child_log in the guest before a failed frame_return rollback.
add_log(parent_addr, parent_topics)

with open(out_file, "wb") as f:
    f.write(struct.pack("<Q", 0))
    f.write(struct.pack("<Q", mode))
    f.write(struct.pack("<Q", len(parent_log)))
    f.write(struct.pack("<Q", len(child_log)))
    f.write(parent_log)
    f.write(b"\x00" * (256 - len(parent_log)))
    f.write(child_log)
    pad = (-f.tell()) % 8
    if pad:
        f.write(b"\x00" * pad)
with open(expected_file, "w") as f:
    f.write(bytes(bloom).hex())
PYCASE

  "$ZISKEMU" -e gen-out/zisk_running_bloom_log_commit_revert.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_running_bloom_log_commit_revert_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -c 256 "$out_file" | tr -d '\n')"
  local expected; expected="$(cat "$exp_hex_file")"

  if [[ "$actual" == "$expected" ]]; then
    local nbits; nbits="$(python3 -c "print(bin(int('$actual', 16)).count('1'))")"
    printf "  %-30s OK   mode=%s bits_set=%d\n" "$name" "$mode" "$nbits"
    return 0
  else
    printf "  %-30s FAIL mode=%s\n" "$name" "$mode"
    printf "      actual:   %s...\n" "${actual:0:80}"
    printf "      expected: %s...\n" "${expected:0:80}"
    return 1
  fi
}

FAILED=0
run_case "committed_parent_log" 0 || FAILED=1
run_case "reverted_child_log" 1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: hot running bloom commits parent LOG and rolls back reverted child LOG"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
