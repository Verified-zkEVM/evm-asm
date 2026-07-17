#!/usr/bin/env bash
# codegen-zisk-stateless-adversarial-mpt-check.sh -- full-guest 0-FA guards
#
# Start from one canonical expected-valid tests-zkevm@v0.6.2 stateless input,
# then forge trust-bearing state-root inputs without changing their framing:
#   * a witness.state node byte (the header still commits to the old hash),
#   * a malformed RLP node,
#   * a ByteList[1025] state node with every enclosing SSZ offset repaired,
#   * a BAL account post-balance, and
#   * a BAL storage post-value.
#
# Every forged input is protocol-invalid: execution-specs and the linked guest
# must both emit successful_validation = 0.  This is deliberately a full-guest
# guard rather than a leaf-probe, so it exercises the actual stateless verdict
# route and its bounded state-root builder.
set -euo pipefail

cd "$(dirname "$0")/.."
repo_root="$(pwd)"
tag="${EEST_FIXTURE_TAG:-$(cat scripts/eest-fixture-tag.txt)}"
fixtures="${EEST_FIXTURES_DIR:-$repo_root/gen-out/eest-fixtures/$tag/fixtures/fixtures}"
spike_run="${SPIKE_RUN:-$repo_root/scripts/spike/spike_run}"
guest_elf="${GUEST_ELF:-$repo_root/gen-out/stateless_guest.elf}"
fixture_rel="blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/authorization_charges/account_write_authority_is_recipient.json"

[[ -d "$fixtures" ]] || { echo "fixtures not found: $fixtures" >&2; exit 1; }
[[ -x "$spike_run" ]] || { echo "spike_run not found: $spike_run" >&2; exit 1; }

if [[ ! -f "$guest_elf" ]]; then
  echo "==> build and emit stateless_guest"
  lake build codegen
  lake exe codegen --program stateless_guest --halt linux93 -o gen-out/stateless_guest
  guest_elf="$repo_root/gen-out/stateless_guest.elf"
fi

tmp="$(mktemp -d "${TMPDIR:-/tmp}/stateless-adversarial-mpt.XXXXXX")"
trap 'rm -rf "$tmp"' EXIT

echo "==> construct v0.6.2 canonical input and five structural forgeries"
uv run --directory execution-specs --quiet python3 - "$fixtures/$fixture_rel" "$tmp" <<'PY'
import json
import struct
import sys
from pathlib import Path

import rlp
from ethereum.forks.amsterdam.stateless_guest import (
    deserialize_stateless_input,
    run_stateless_guest,
)
from ethereum_types.bytes import Bytes

fixture_path, out_dir = map(Path, sys.argv[1:])
doc = json.loads(fixture_path.read_text())
selected = None
for tc in doc.values():
    for block in tc.get("blocks", []):
        raw = block.get("statelessInputBytes")
        if not raw:
            continue
        blob = bytes.fromhex(raw.removeprefix("0x"))
        spec_out = bytes(run_stateless_guest(Bytes(blob)))
        if spec_out[32] == 1:
            selected = blob
            break
    if selected is not None:
        break
assert selected is not None, "fixture no longer contains an expected-valid stateless block"

def pack(blob: bytes) -> bytearray:
    framed = bytearray(struct.pack("<Q", len(blob)) + blob)
    framed.extend(b"\0" * ((-len(framed)) % 8))
    return framed

def blob_of(framed: bytes) -> bytes:
    n = struct.unpack_from("<Q", framed)[0]
    return framed[8 : 8 + n]

base = pack(selected)
assert bytes(run_stateless_guest(Bytes(blob_of(base))))[32] == 1
(out_dir / "baseline.input").write_bytes(base)

# File offset 8 is the schema prefix; stateless_verdict_v2 starts its SSZ
# navigation at schema+2, i.e. file offset 10.
s0 = 10
u32 = lambda b, p: struct.unpack_from("<I", b, p)[0]
witness = s0 + u32(base, s0 + 4)
state = witness + u32(base, witness)
first = u32(base, state)
count = first // 4
assert count >= 2 and first == 4 * count
node = state + first
node_end = state + u32(base, state + 4)
node_len = node_end - node
assert base[node : node + 2] == b"\xf8\x51", "canonical fixture layout changed"

def save(name: str, framed: bytearray) -> None:
    blob = blob_of(framed)
    spec_out = bytes(run_stateless_guest(Bytes(blob)))
    assert spec_out[32] == 0, f"execution-specs accepted forged {name}"
    (out_dir / f"{name}.input").write_bytes(framed)

# 1. Preserve every SSZ offset and RLP envelope; only forge a child-hash byte.
forged_node = bytearray(base)
forged_node[node + 13] ^= 1
save("forged_witness_node", forged_node)

# 2. The node remains the same ByteList length but its RLP list envelope lies.
malformed_node = bytearray(base)
malformed_node[node + 1] = 0x52
save("malformed_witness_node", malformed_node)

# 3. Expand exactly one ByteList to 1025 bytes while repairing its state-list,
# witness, StatelessInput and host framing offsets.  This must be rejected by
# the SSZ ByteList[1024] envelope, not accepted as a different MPT preimage.
overlong = bytearray(base)
delta = 1025 - node_len
assert delta > 0
overlong[node_end:node_end] = b"\0" * delta
for i in range(1, count):
    struct.pack_into("<I", overlong, state + 4 * i, u32(base, state + 4 * i) + delta)
for p in (witness + 4, witness + 8):
    struct.pack_into("<I", overlong, p, u32(base, p) + delta)
for p in (s0, s0 + 4, s0 + 8, s0 + 12):
    old = u32(base, p)
    if old > u32(base, s0 + 4):
        struct.pack_into("<I", overlong, p, old + delta)
payload_len = struct.unpack_from("<Q", overlong)[0] + delta
struct.pack_into("<Q", overlong, 0, payload_len)
del overlong[8 + payload_len:]
overlong.extend(b"\0" * ((-len(overlong)) % 8))
save("overlong_witness_node", overlong)

decoded = deserialize_stateless_input(Bytes(selected))
bal = bytes(decoded.new_payload_request.execution_payload.block_access_list)
bal_start = selected.find(bal)
assert bal_start >= 0 and selected.find(bal, bal_start + 1) < 0

def forge_bal(name: str, needle: bytes, before: int, after: int) -> None:
    framed = bytearray(base)
    pos = bal.find(needle)
    assert pos >= 0 and bal.find(needle, pos + 1) < 0, f"{name} layout changed"
    at = 8 + bal_start + pos + len(needle) - 1
    assert framed[at] == before
    framed[at] = after
    save(name, framed)

# 4. Account[9]'s balance change [1, 0x65] -> [1, 0x64].
forge_bal("forged_bal_post_balance", bytes.fromhex("c3c20165"), 0x65, 0x64)
# 5. Account[5]'s storage post-value 0x03e8 -> 0x03e9.
forge_bal("forged_bal_storage_value", bytes.fromhex("c5c4808203e8"), 0xE8, 0xE9)

print(f"baseline node={node_len} bytes, state entries={count}, forged inputs written to {out_dir}")
PY

run_case() {
  local name="$1" input="$tmp/$1.input" output="$tmp/$1.output"
  "$spike_run" "$guest_elf" "$input" "$output" >"$tmp/$1.log" 2>&1
  python3 - "$name" "$output" <<'PY'
import sys
name, path = sys.argv[1:]
out = open(path, "rb").read()
if len(out) < 33:
    raise SystemExit(f"{name}: guest output too short ({len(out)} bytes)")
if out[32] != 0:
    raise SystemExit(f"{name}: FALSE ACCEPT (succ={out[32]})")
print(f"  {name:28} OK   guest rejects")
PY
}

echo "==> baseline"
"$spike_run" "$guest_elf" "$tmp/baseline.input" "$tmp/baseline.output" >"$tmp/baseline.log" 2>&1
python3 - "$tmp/baseline.output" <<'PY'
import sys
out = open(sys.argv[1], "rb").read()
if len(out) < 33 or out[32] != 1:
    raise SystemExit(f"baseline no longer accepts (succ={out[32] if len(out) > 32 else 'short'})")
print("  canonical baseline            OK   guest accepts")
PY

echo "==> adversarial trust-boundary forgeries"
run_case forged_witness_node
run_case malformed_witness_node
run_case overlong_witness_node
run_case forged_bal_post_balance
run_case forged_bal_storage_value
echo "==> PASS: full guest rejects all forged witness/BAL state-root inputs"
