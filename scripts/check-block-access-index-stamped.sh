#!/usr/bin/env bash
# EIP-7928 attribution gate: every path that reaches `dispatch_tx_runtime_code`
# must first store this transaction's block_access_index (i+1) into
# `current_block_access_index`.
#
# STATUS: THIS SCRIPT FAILS ON THE CURRENT TREE BY DESIGN and is deliberately NOT
# wired into check-build-parallel.sh yet.  It states the invariant that GH #10695
# will establish; adding the missing store changes what a live rejecting consumer
# sees, so the fix is gated behind a paired sweep and this gate is wired into CI
# together with it.  Its present failure is the control that shows it can fail --
# an ungated check script is indistinguishable from a passing one.
#
# Why this exists.  The SSTORE handler stamps `exec_log_txindex[row]` from that
# global (.Lsstore_append_entry in the emitted guest), and `exec_log_txindex` is
# the a4 base of `bal_all_accounts_tuple_sequences_consistent_skip_list`, whose
# nonzero return rejects the block.  The stamp existed on the EOA-recipient path
# and the creation path but NOT on the contract-recipient path -- which is the
# only transaction class that can execute SSTORE at all.  The four
# recipient-code-hash `bne`s jump straight to `.Lbv_mtx_is_contract`, PAST the
# EOA stamp, so every contract transaction dispatched with the index still at
# its static default 1 (or at whatever the last EOA/creation tx left).  Measured:
# 398/400 rows disagreeing with i+1.  Nothing objected: the comparator's
# per-change loop iterates zero times today, and the Lean comment sitting
# directly above the contract path asserted the stamp was there.
#
# So this checks the emitted `.s`, not the Lean source -- source adjacency is not
# emitted adjacency, and a comment is not a store.
#
# What is checked: an intra-function forward dominance test.  For each call to
# `dispatch_tx_runtime_code`, some store to `current_block_access_index` in the
# same function must dominate it -- i.e. no label between the store and the call
# is branched to from outside that span.  Limitation: this is a linear scan, not
# a full CFG, so indirect jumps (`jr`/`jalr` through a register) are invisible to
# it.  There are none on these paths today; if one appears the test silently
# weakens rather than failing, which is why the label/branch spellings below are
# asserted to match something before any verdict is issued.
#
# Both dispatch sites are held to the invariant, including the single-tx one.  On
# that lane the value the SSTORE handler reads happens to be CORRECT today -- the
# only user tx is i=0, so i+1 = 1, which is the global's static initialiser
# (`current_block_access_index: .dword 1`).  It is included anyway: correctness by
# static initialiser on a mutable global that another lane stores to is the same
# fragility as the missing store, one accident away from the same bug.  An explicit
# stamp of 1 there is free and makes the invariant uniform.
set -uo pipefail
cd "$(dirname "$0")/.."

ELF_DIR="${ELF_DIR:-gen-out/regionmap}"
GUEST_S="$ELF_DIR/stateless_guest.s"
if [[ "${NO_BUILD:-0}" != "1" || ! -f "$GUEST_S" ]]; then
  echo "==> emit stateless_guest asm"
  lake exe codegen --program stateless_guest --halt linux93 -o "$ELF_DIR/stateless_guest" >/dev/null || {
    echo "check-block-access-index-stamped: codegen failed" >&2; exit 1; }
fi
[[ -f $GUEST_S ]] || { echo "check-block-access-index-stamped: $GUEST_S absent" >&2; exit 2; }

python3 - "$GUEST_S" <<'PY'
import re, sys

path = sys.argv[1]
lines = open(path).read().split('\n')

CALL   = re.compile(r'\bjal\s+ra\s*,\s*dispatch_tx_runtime_code\b')
STORE  = re.compile(r'current_block_access_index\b.*\bsd\s')
GLOBAL = re.compile(r'^([A-Za-z_][A-Za-z0-9_$]*):')
LOCAL  = re.compile(r'^(\.[A-Za-z_][A-Za-z0-9_.$]*):')
# Any control transfer naming a label: b*, j, jal, tail.
BRANCH = re.compile(r'\b(?:b[a-z]+|j|jal|tail)\s+(?:[a-z0-9]+\s*,\s*)*(\.?[A-Za-z_][A-Za-z0-9_.$]*)\b')

calls  = [i for i, l in enumerate(lines) if CALL.search(l)]
stores = [i for i, l in enumerate(lines) if STORE.search(l)]
# Selector self-check: if either spelling stops matching, the test would pass
# vacuously.  Refuse instead.
if not calls:
    sys.exit("SELECTOR STALE: no `jal ra, dispatch_tx_runtime_code` found -- test would be vacuous")
if not stores:
    sys.exit("FAIL: no store to current_block_access_index anywhere in the guest")

func_starts = [i for i, l in enumerate(lines) if GLOBAL.match(l)]

def enclosing(n):
    prev = [f for f in func_starts if f < n]
    return prev[-1] if prev else 0

# label -> lines that transfer control to it
targets = {}
for i, l in enumerate(lines):
    if GLOBAL.match(l) or LOCAL.match(l):
        continue
    for m in BRANCH.finditer(l):
        targets.setdefault(m.group(1), []).append(i)

def dominates(s, n, f):
    """Does the store at line s dominate the call at line n, within function f?

    Reports the bypass with the EARLIEST source line, which is the fall-through
    split that actually skips the store, rather than whichever label happens to
    come first in the span (typically a loop back-edge from after the call).
    """
    worst = None
    for i in range(s + 1, n + 1):
        m = LOCAL.match(lines[i]) or GLOBAL.match(lines[i])
        if not m:
            continue
        for src in targets.get(m.group(1), []):
            if f <= src and not (s <= src <= n):
                if worst is None or src < worst[1]:
                    worst = (m.group(1), src)
    if worst is None:
        return True, None, None
    return False, worst[0], worst[1]

bad = []
for n in calls:
    f = enclosing(n)
    fname = GLOBAL.match(lines[f]).group(1) if GLOBAL.match(lines[f]) else '<top>'
    cands = [s for s in stores if f <= s < n]
    if not cands:
        bad.append((n, fname, 'no store to current_block_access_index in the enclosing function'))
        continue
    reasons = []
    for s in cands:
        ok, lbl, src = dominates(s, n, f)
        if ok:
            reasons = None
            break
        reasons.append(f'store at .s:{s+1} bypassed via label {lbl} branched from .s:{src+1}')
    if reasons is not None:
        bad.append((n, fname, '; '.join(reasons)))

print(f'dispatch_tx_runtime_code call sites checked: {len(calls)}')
print(f'current_block_access_index store sites in guest: {len(stores)}')
if bad:
    print('FAIL -- these dispatch sites are reachable without a per-tx block_access_index stamp:',
          file=sys.stderr)
    for n, fname, why in bad:
        print(f'  {path}:{n+1} in {fname}: {why}', file=sys.stderr)
    sys.exit(1)
print('check-block-access-index-stamped: every dispatch is dominated by a stamp')
PY
