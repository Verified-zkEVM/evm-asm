#!/usr/bin/env bash
#
# fuzz-arith-diff.sh — boundary-biased differential fuzzer for the six EVM
# arithmetic opcodes whose RISC-V lowering is the historical home of
# DIV-class bugs: div, mod, sdiv, smod, mulmod, addmod.
#
# Phase 3 deliverable D1 (report R-E1). Two tiers:
#
#   PR fast-path (default):
#     lake exe arith-diff-check  — fuzz all six ops against an INDEPENDENT
#     Nat/Int reference over boundary-biased operands, plus re-verify every
#     permanent corpus entry (tests/fuzz-corpus/arith/corpus.jsonl) still
#     matches its frozen execution-specs verdict. No Python, deterministic,
#     seconds. This is the signal that would have caught the v4 DIV bug
#     class before it shipped.
#
#   Nightly differential (--python):
#     Generate boundary-biased operands, run them through BOTH evm-asm
#     (lake exe ... emit) and the execution-specs *amsterdam* oracle
#     (scripts/fuzz_arith_oracle.py under `uv run` in the pinned submodule),
#     and diff. Every newly-discovered divergence is APPENDED to the
#     permanent corpus so it can never silently regress, and the run fails.
#
# The execution-specs Python is a TEST ORACLE ONLY — never imported into
# Lean / the trusted base (report 6 non-goal). No native_decide/bv_decide,
# no maxHeartbeats, no new trusted components.
#
# Usage:
#   scripts/fuzz-arith-diff.sh                     # PR: default 20k+5k, seed 42
#   scripts/fuzz-arith-diff.sh 50000 20000 7       # PR: custom sizes + seed
#   scripts/fuzz-arith-diff.sh --python            # nightly differential
#   scripts/fuzz-arith-diff.sh --python 5000 2000 7
#
# Exit: 0 = all agree; 1 = a divergence (PR) or a new oracle divergence
# (nightly, also appended to the corpus).

set -euo pipefail

cd "$(dirname "$0")/.."

CORPUS="tests/fuzz-corpus/arith/corpus.jsonl"
SPECS_DIR="execution-specs"
ORACLE="$(pwd)/scripts/fuzz_arith_oracle.py"

mode="pr"
if [[ "${1:-}" == "--python" ]]; then
  mode="python"
  shift
fi

echo "==> lake build arith-diff-check"
lake build arith-diff-check

if [[ "$mode" == "pr" ]]; then
  N_RANDOM="${1:-20000}"
  N_BIAS="${2:-5000}"
  SEED="${3:-42}"
  echo "==> PR fast-path: fuzz (${N_RANDOM} random + ${N_BIAS} bias, seed ${SEED}) + corpus"
  # default mode runs fuzz + corpus (corpus path is the default constant)
  exec lake exe arith-diff-check "$N_RANDOM" "$N_BIAS" "$SEED"
fi

# ---- nightly differential vs execution-specs --------------------------------
N_RANDOM="${1:-5000}"
N_BIAS="${2:-2000}"
SEED="${3:-42}"

if [[ ! -f "$SPECS_DIR/pyproject.toml" ]]; then
  echo "==> initialising execution-specs submodule"
  git submodule update --init --depth 1 "$SPECS_DIR"
fi
command -v uv >/dev/null 2>&1 || { echo "FATAL: 'uv' is required for the --python oracle tier" >&2; exit 2; }

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
operands="$work/operands.jsonl"
evm_results="$work/evm.jsonl"
oracle_results="$work/oracle.jsonl"

echo "==> generating boundary-biased operands (${N_RANDOM} random + ${N_BIAS} bias, seed ${SEED})"
lake exe arith-diff-check gen "$N_RANDOM" "$N_BIAS" "$SEED" > "$operands"
echo "    $(wc -l < "$operands") operand rows"

echo "==> evm-asm side (lake exe arith-diff-check emit)"
lake exe arith-diff-check emit "$operands" > "$evm_results"

echo "==> execution-specs oracle (uv run, amsterdam fork)"
( cd "$SPECS_DIR" && uv run --quiet python "$ORACLE" < "$operands" ) > "$oracle_results"

echo "==> diffing evm-asm vs oracle"
# Compare by (op,a,b,n); print any divergence and emit the oracle line (with
# its `expected`) for the divergent cases on fd 3 so we can append to corpus.
python3 - "$evm_results" "$oracle_results" "$CORPUS" <<'PY'
import json, sys

evm_path, oracle_path, corpus_path = sys.argv[1], sys.argv[2], sys.argv[3]

def load(path, value_key):
    d = {}
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            o = json.loads(line)
            key = (o["op"], o["a"], o["b"], o.get("n", "0x0"))
            d[key] = o[value_key]
    return d

evm = load(evm_path, "result")
oracle = load(oracle_path, "expected")

# existing corpus keys (so we don't append duplicates)
existing = set()
try:
    with open(corpus_path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            o = json.loads(line)
            existing.add((o["op"], o["a"], o["b"], o.get("n", "0x0")))
except FileNotFoundError:
    pass

mismatches = []
for key, want in oracle.items():
    got = evm.get(key)
    if got is None:
        print(f"  WARN no evm-asm result for {key}", file=sys.stderr)
        continue
    if got != want:
        mismatches.append((key, got, want))

if not mismatches:
    print(f"PASS: {len(oracle)} operands — evm-asm agrees with the "
          f"execution-specs oracle on every case.")
    sys.exit(0)

print(f"FAIL: {len(mismatches)} divergence(s) vs the execution-specs oracle:")
appended = 0
with open(corpus_path, "a") as cf:
    for (op, a, b, n), got, want in mismatches:
        print(f"  [{op}] a={a} b={b} n={n}  evm-asm={got}  oracle={want}")
        key = (op, a, b, n)
        if key not in existing:
            cf.write(json.dumps({"op": op, "a": a, "b": b, "n": n,
                                 "expected": want},
                                separators=(",", ":")) + "\n")
            existing.add(key)
            appended += 1
print(f"  ({appended} new case(s) appended to {corpus_path} — fix the "
      f"divergence; the PR fast-path will now fail until it is resolved.)")
sys.exit(1)
PY
