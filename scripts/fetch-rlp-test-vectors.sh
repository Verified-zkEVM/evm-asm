#!/usr/bin/env bash
# fetch-rlp-test-vectors.sh
#
# Vendor the official Ethereum RLP test vectors (ethereum/tests) for the
# `rlp-diff-check` correctness suite. Downloads the upstream JSON and flattens
# it to dead-simple `name <space> outHex` lines that the Lean vector runner
# (EvmAsm/Tests/RlpDiffCheck.lean) reads with no JSON/Python dependency at test
# time. Re-run to refresh; commit the regenerated files.
#
#   rlptest.json        -> tests/rlp-vectors/valid.txt    (must decode + re-encode canonically)
#   invalidRLPTest.json -> tests/rlp-vectors/invalid.txt  (must be rejected by decode)
#
# Source: https://github.com/ethereum/tests/tree/develop/RLPTests (MIT/CC0).
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_DIR="$REPO_ROOT/tests/rlp-vectors"
RAW_DIR="$OUT_DIR/upstream"
BASE_URL="https://raw.githubusercontent.com/ethereum/tests/develop/RLPTests"

mkdir -p "$RAW_DIR"

echo "Fetching official RLP test vectors from ethereum/tests ..."
curl -sS --fail --max-time 30 -o "$RAW_DIR/rlptest.json"        "$BASE_URL/rlptest.json"
curl -sS --fail --max-time 30 -o "$RAW_DIR/invalidRLPTest.json" "$BASE_URL/invalidRLPTest.json"

flatten() {  # $1 = json file, $2 = out file
  uv run python3 - "$1" "$2" <<'PY'
import json, sys
src, dst = sys.argv[1], sys.argv[2]
d = json.load(open(src))
with open(dst, "w") as f:
    for name, v in d.items():
        out = v["out"]
        hx = out[2:] if out.startswith("0x") else out      # strip optional 0x
        hx = hx.strip()
        # sanity: even-length hex (empty allowed)
        assert all(c in "0123456789abcdefABCDEF" for c in hx), (name, out)
        assert len(hx) % 2 == 0, (name, out)
        f.write(f"{name} {hx}\n")
print(f"  {dst}: {len(d)} entries")
PY
}

echo "Flattening to $OUT_DIR ..."
flatten "$RAW_DIR/rlptest.json"        "$OUT_DIR/valid.txt"
flatten "$RAW_DIR/invalidRLPTest.json" "$OUT_DIR/invalid.txt"
echo "Done. Commit tests/rlp-vectors/ (upstream JSON + flattened .txt)."
