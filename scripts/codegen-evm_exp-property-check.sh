#!/usr/bin/env bash
# codegen-evm_exp-property-check.sh — property testing for EXP via codegen.
#
# Builds evm_exp_from_input once, then generates random (base, exponent)
# pairs and runs them against the ELF, comparing output to Python's
# pow(base, exp, 2**256).  Runs indefinitely by default so you can keep
# re-invoking (or leave it running) to accumulate more random coverage.
#
# Usage:
#   scripts/codegen-evm_exp-property-check.sh [--count=N] [--seed=SEED]
#                                              [--timeout=SECS]
#
#   --count=N      : stop after N total cases; exit 0 iff all passed.
#                    Omit to run forever.
#   --seed=N       : fixed PRNG seed for reproducibility; default: $RANDOM.
#   --timeout=SECS : wall-clock seconds per case before declaring TIMEOUT
#                    (default: 10). Timeouts are treated as runtime
#                    regressions.
#
# Exit:
#   0 — every tested case matched expected (only possible with --count=N)
#   1 — at least one case failed / timed out, or the build step errored
#
# Note: this script originally exposed the x6 counter-clobber regression in
# the EXP loop. The current `_fixed_fixed` body keeps the bit counter in x22;
# keep this property test around as the regression gate before promoting EXP
# into required runtime frontier coverage.

set -euo pipefail

cd "$(dirname "$0")/.."

COUNT=""
SEED="$RANDOM"
TIMEOUT_SECS=10
for arg in "$@"; do
  case "$arg" in
    --count=*)   COUNT="${arg#--count=}" ;;
    --seed=*)    SEED="${arg#--seed=}" ;;
    --timeout=*) TIMEOUT_SECS="${arg#--timeout=}" ;;
  esac
done

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else
    echo "ziskemu not found — install via ziskup or set ZISKEMU=..." >&2
    exit 1
  fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit evm_exp_from_input ELF"
lake exe codegen --program evm_exp_from_input --halt linux93 \
  -o gen-out/evm_exp_from_input

ELF=gen-out/evm_exp_from_input.elf
INPUT=gen-out/evm_exp_from_input.input.bin
OUTPUT=gen-out/evm_exp_from_input.output

export ZISKEMU ELF INPUT OUTPUT COUNT SEED TIMEOUT_SECS

python3 <<'PY'
import os, random, struct, subprocess, sys, pathlib, time

ZISKEMU    = os.environ["ZISKEMU"]
ELF        = os.environ["ELF"]
INPUT      = os.environ["INPUT"]
OUTPUT     = os.environ["OUTPUT"]
COUNT      = int(os.environ["COUNT"]) if os.environ["COUNT"] else None
SEED       = int(os.environ["SEED"])
TIMEOUT    = int(os.environ["TIMEOUT_SECS"])

MASK256 = (1 << 256) - 1
rng = random.Random(SEED)
print(f"Seed: {SEED}  ELF: {ELF}  timeout/case: {TIMEOUT}s")
print()

def pack_input(base: int, exp: int) -> bytes:
    """Pack (base, exp) as the ziskemu -i payload:
       8-byte LE length prefix (= 64) followed by 64 bytes of data."""
    blob = base.to_bytes(32, "little") + exp.to_bytes(32, "little")
    return struct.pack("<Q", len(blob)) + blob

def expected_hex(base: int, exp: int) -> str:
    r = pow(base, exp, 1 << 256)
    return r.to_bytes(32, "little").hex()

# Edge cases that exercise specific code paths.
edge_cases = [
    ("zero_base",       0,           5),
    ("one_base",        1,           (1 << 200) - 1),
    ("zero_exp",        7,           0),
    ("one_exp",         0xdeadbeef,  1),
    ("two_squared",     2,           2),
    ("two_cubed",       2,           3),
    ("two_to_8",        2,           8),
    ("two_to_64",       2,           64),
    ("two_to_256",      2,           256),
    ("max_base_exp1",   MASK256,     1),
    ("max_base_exp2",   MASK256,     2),
    ("three_pow_three", 3,           3),
]

failures = []
passed   = 0
iteration = 0

def run_case(label: str, base: int, exp: int) -> bool:
    global passed, iteration
    iteration += 1
    pathlib.Path(INPUT).write_bytes(pack_input(base, exp))
    expected = expected_hex(base, exp)
    log = pathlib.Path(f"gen-out/evm_exp_from_input.{label}.emu.log")
    t0 = time.time()
    try:
        subprocess.run(
            [ZISKEMU, "-e", ELF, "-i", INPUT, "-o", OUTPUT],
            check=True,
            stdout=log.open("wb"), stderr=subprocess.STDOUT,
            timeout=TIMEOUT,
        )
    except subprocess.TimeoutExpired:
        elapsed = time.time() - t0
        print(f"  [TIMEOUT] #{iteration:5d} {label} ({elapsed:.0f}s)")
        failures.append(label)
        return False
    except subprocess.CalledProcessError as e:
        elapsed = time.time() - t0
        print(f"  [FAIL] #{iteration:5d} {label}: ziskemu rc={e.returncode} ({elapsed:.0f}s)"
              f"  (log: {log})")
        failures.append(label)
        return False
    elapsed = time.time() - t0
    actual = pathlib.Path(OUTPUT).read_bytes()[:32].hex()
    ok = (actual == expected)
    status = "PASS" if ok else "FAIL"
    print(f"  [{status}] #{iteration:5d} {label} ({elapsed:.0f}s)")
    if not ok:
        print(f"           base     = 0x{base:064x}")
        print(f"           exp      = 0x{exp:064x}")
        print(f"           expected = {expected}")
        print(f"           actual   = {actual}")
        failures.append(label)
    else:
        passed += 1
    return ok

# --- edge cases ---
print("=== Edge cases ===")
for label, base, exp in edge_cases:
    run_case(label, base, exp)
    if COUNT is not None and iteration >= COUNT:
        break

# --- random cases (infinite unless --count=N) ---
i = 0
if COUNT is None or iteration < COUNT:
    print()
    print("=== Random cases (Ctrl-C to stop) ===")
    while COUNT is None or iteration < COUNT:
        i += 1
        run_case(f"random_{i:06d}", rng.getrandbits(256), rng.getrandbits(256))

print()
total = passed + len(failures)
if failures:
    shown = failures[:20]
    etc   = f" …+{len(failures)-20} more" if len(failures) > 20 else ""
    print(f"==> FAIL: {len(failures)}/{total} cases mismatched/timed out: {shown}{etc}")
    sys.exit(1)
print(f"==> PASS: all {passed} cases matched expected results")
PY
