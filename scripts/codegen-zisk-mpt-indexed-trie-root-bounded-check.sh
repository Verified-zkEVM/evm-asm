#!/usr/bin/env bash
# Oracle KATs for the bounded empty indexed transaction/receipt trie builder.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"
ZISKEMU="${ZISKEMU:-$(command -v ziskemu || true)}"
[[ -n "$ZISKEMU" ]] || { echo "ziskemu not found" >&2; exit 1; }
mkdir -p gen-out
lake build codegen >/dev/null
lake exe codegen --program zisk_mpt_indexed_trie_root_bounded --halt linux93 \
  -o gen-out/zisk_mpt_indexed_trie_root_bounded >/dev/null

run_case() {
  local name="$1" indices_py="$2"
  uv run --directory execution-specs --quiet python3 - "$REPO_ROOT" "$name" "$indices_py" <<'PY'
import struct, sys
from ethereum.merkle_patricia_trie import Trie, root, trie_set
from ethereum_rlp import rlp
from ethereum_types.bytes import Bytes
from ethereum_types.numeric import Uint

repo_root, name, indices = sys.argv[1], sys.argv[2], eval(sys.argv[3])
def path(i):
    key = bytes(rlp.encode(Uint(i)))
    return bytes(x for b in key for x in (b >> 4, b & 15))
if name == 'long_one':
    values = [b'\xab' * 20000]
elif name == 'long_extension':
    values = [b'\xcd' * 20000, b'\x80']
else:
    values = [bytes([i & 255]) for i in indices]
with open(f'{repo_root}/gen-out/zisk_mpt_indexed_trie_root_bounded_{name}.input', 'wb') as f:
    f.write(struct.pack('<Q', len(indices)))
    for p, v in zip(map(path, indices), values):
        f.write(struct.pack('<Q', len(p)) + p + b'\0' * (8 - len(p)))
        f.write(struct.pack('<Q', len(v)) + v + b'\0' * (-len(v) % 8))
t = Trie(secured=False, default=None)
for i, value in zip(indices, values):
    trie_set(t, Bytes(rlp.encode(Uint(i))), Bytes(value))
open(f'{repo_root}/gen-out/zisk_mpt_indexed_trie_root_bounded_{name}.expected', 'wb').write(bytes(root(t)))
PY
  "$ZISKEMU" -e gen-out/zisk_mpt_indexed_trie_root_bounded.elf \
    -i "gen-out/zisk_mpt_indexed_trie_root_bounded_${name}.input" \
    -o "gen-out/zisk_mpt_indexed_trie_root_bounded_${name}.output" -n 3000000 >/dev/null </dev/null
  python3 - "$name" <<'PY'
import struct, sys
name = sys.argv[1]
out = open(f'gen-out/zisk_mpt_indexed_trie_root_bounded_{name}.output', 'rb').read()
assert struct.unpack_from('<Q', out, 32)[0] == 0
assert out[:32] == open(f'gen-out/zisk_mpt_indexed_trie_root_bounded_{name}.expected', 'rb').read()
print(f'OK {name}')
PY
}

run_case empty '[]'
run_case one '[0]'
run_case two '[0, 1]'
run_case rlp_order_boundary '[0, 127, 128, 256]'
run_case long_one '[0]'
run_case long_extension '[0, 128]'

# The indexed transaction/receipt capacity is a block-gas upper bound, not an
# arbitrary implementation limit: every transaction consumes at least the
# protocol's 21,000 intrinsic gas, so a 200M-gas block cannot carry C+1
# descriptors.  The builder must reject that spec-invalid input before it
# dereferences the descriptor array.
uv run --directory execution-specs --quiet python3 - "$REPO_ROOT" <<'PY'
import struct, sys

repo_root = sys.argv[1]
block_gas_limit = 200_000_000
intrinsic_gas_floor = 21_000
cap = block_gas_limit // intrinsic_gas_floor
assert cap == 9523
with open(f'{repo_root}/gen-out/zisk_mpt_indexed_trie_root_bounded_over_cap.input', 'wb') as f:
    f.write(struct.pack('<Q', cap + 1))
PY
"$ZISKEMU" -e gen-out/zisk_mpt_indexed_trie_root_bounded.elf \
  -i gen-out/zisk_mpt_indexed_trie_root_bounded_over_cap.input \
  -o gen-out/zisk_mpt_indexed_trie_root_bounded_over_cap.output -n 3000000 >/dev/null </dev/null
python3 - <<'PY'
import struct

out = open('gen-out/zisk_mpt_indexed_trie_root_bounded_over_cap.output', 'rb').read()
assert struct.unpack_from('<Q', out, 32)[0] == 1
print('OK over_cap_9524 rejects (spec-invalid: 200M // 21000 = 9523)')
PY
echo 'PASS: bounded indexed trie root matches execution-specs'
