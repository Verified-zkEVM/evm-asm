#!/usr/bin/env bash
set -euo pipefail

# codegen-zisk-bal-probes.sh -- EXECUTE the BAL measure pass and the two self-tests (#10680).
#
# Every other check on `bal_serializer_measure_*` is a `#guard` over the emitted string.
# Those pin structure, not behaviour. GH #10754 is the general form of the problem: the
# BAL self-tests have zero callers, and `check-build-units-link.sh` asserts that units
# LINK, so a linkage gate stands where a behaviour gate is assumed.
#
# This script is a behaviour gate. It builds `zisk_bal_serializer_measure`, runs it, and
# compares seven measured lengths against values hand-derived from the RLP rules.
#
# The measure pass cannot be reached from any fixture -- `bal_serializer_measure_account`
# has zero callers -- so a synthetic probe is the only way to execute it at all.
#
# Both discriminating claims were controlled by reintroducing the real defect:
#   * pre-fix widener (u64 LSB at field byte 31): 7/7 assertions fire, case 1 reads 38,
#     i.e. exactly 6 + 32, the predicted over-measurement
#   * `slot_seen_before` removed: ONLY case 2 fires, and it reads exactly 18
#
# Usage: scripts/codegen-zisk-bal-probes.sh
# Exit:  0 all seven match; 1 any mismatch, with the differing rows printed.

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

SPIKE_RUN="${SPIKE_RUN:-$REPO_ROOT/scripts/spike/spike_run}"
OUT_DIR="${OUT_DIR:-gen-out/bal-measure-probe}"
mkdir -p "$OUT_DIR"

# No emulator means no result, so this fails. There is deliberately no graceful-skip
# path: a gate that exits 0 when it could not run reads exactly like a passing gate, and
# that is the defect this script exists to stop repeating. A person runs this, so a
# person sees the failure and knows their toolchain is missing.
if [[ ! -x "$SPIKE_RUN" ]]; then
  echo "==> FAIL: no emulator at $SPIKE_RUN (set SPIKE_RUN to override)" >&2
  exit 1
fi

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_bal_serializer_measure"
lake exe codegen --program zisk_bal_serializer_measure --halt linux93 \
  -o "$OUT_DIR/bsmp"

# A missing ELF must not read as a pass: the comparison below would see a short file and
# we would rather fail loudly here than compare against nothing.
if [[ ! -f "$OUT_DIR/bsmp.elf" ]]; then
  echo "==> FAIL: codegen produced no ELF" >&2
  exit 1
fi

: > "$OUT_DIR/empty.input"
echo "==> run under spike"
"$SPIKE_RUN" "$OUT_DIR/bsmp.elf" "$OUT_DIR/empty.input" "$OUT_DIR/bsmp.output" \
  > "$OUT_DIR/bsmp.emu.log" 2>&1 || true

python3 - "$OUT_DIR/bsmp.output" <<'PY'
import struct, sys
path = sys.argv[1]
try:
    data = open(path, 'rb').read()
except FileNotFoundError:
    print(f"==> FAIL: no probe output at {path}"); sys.exit(1)

# (label, byte offset, expected, what a wrong answer means)
CASES = [
    ("case 1  one change",              0,  6,  "baseline nesting: three header levels"),
    ("case 2  same slot twice",         8,  9,  "18 means the first-occurrence dedup is gone"),
    ("case 3  two distinct slots",     16, 12,  "6 means the slot walk stops early"),
    ("case 4  other address present",  24,  6,  "12 means the address filter is gone"),
    ("case 5  two-byte value",         32,  8,  "6 means multi-byte scalars measure as one byte"),
    ("measure_slot payload",           40,  5,  "the SlotChanges payload the emit pass reads"),
    ("measure_slot inner payload",     48,  3,  "the changes-list payload the emit pass reads"),
    ("case 9  cross-tx read exclusion",160,  1,  "2 means a slot written in another tx was NOT excluded"),
]

# Case 6 is the acceptance criterion in miniature: EMIT the bytes, hash them, compare the
# hash. The expected RLP for case 1's storage_changes is derived by hand from the yellow
# paper -- c5 01 c3 c2 01 05 -- and its keccak-256 is computed here by an independent
# pure-python implementation, validated on keccak256("") before use. Deriving it rather
# than capturing it is what stops a golden file from enshrining a bug as correct.
EXPECTED_RLP = bytes.fromhex('c501c3c20105')

# Case 7: the whole AccountChanges for the same input. 0xe0 is 0xc0 + 32, the account
# payload being 21 (address) + 7 (storage_changes) + four empty lists. The four trailing
# 0xc0 are the point -- an empty field is an empty LIST, not an omitted one, and dropping
# them still yields well-formed RLP for a different account.
EXPECTED_ACCOUNT_RLP = bytes.fromhex(
    'e094aa00000000000000000000000000000000000000c6c501c3c20105c0c0c0c0')

# Case 8: the outer list over TWO accounts. 2 x 33 = 66 bytes of payload is past the
# 55-byte boundary, so the header takes the LONG form f8 42. One account would stay in
# short form and the long-form branch of the header emitter would never run.
# Case 9: slot 7 is read AND written at block_access_index 3; slot 11 is read and never
# written. EIP-7928 excludes a read whose slot is written anywhere in the BLOCK, so only
# 11 survives and the emitted bytes are the single scalar 0x0b. No single-transaction
# fixture can produce this -- read-in-one-tx/written-in-another only exists across txs.
EXPECTED_READS_RLP = bytes.fromhex('0b')

# ---------------------------------------------------------------------------
# PENDING: the end-to-end producer-path case (case 11), not yet built.
#
# Its expectation is DERIVED AND FROZEN HERE BEFORE THE CASE EXISTS, on purpose. Every
# other case in this file derives its bytes from the RLP rules with the producer OUT of
# the loop, so a mistake shows up as a mismatch. Case 11 puts `bal_emit_storage_changes`
# IN the loop, and a digest captured from a run would certify the producer's behaviour by
# definition -- it could not fail, and it would enshrine a reversal bug as correct. That
# is the same trap a captured baseline would have set with the widener's 33-byte scalar.
#
# Scenario: one tx storage write. Address 0xAA.. , slot 7, value 5, block_access_index 1.
# The tx row holds addr and slot as LE stack words; the producer reverses both to BE on
# append (see the builder row field table). SLOT 7 IS NON-SYMMETRIC ON PURPOSE -- a
# BE-vs-LE dword compare matches only byte-symmetric values, so slot 0 would pass under
# the very defect this case exists to catch.
#
# Derivation, from the field table and the yellow paper:
#   StorageChange   [bai=1, value=5]  -> c2 01 05                       3 bytes
#   changes list    payload 3         -> c3 c2 01 05                    4
#   SlotChanges     scalar(7) ++ above, payload 5 -> c5 07 c3 c2 01 05  6
#   storage_changes payload 6         -> c6 c5 07 c3 c2 01 05           7
#   account payload 21 addr + 7 + four empty lists = 32 -> header 0xe0
#
EXPECTED_E2E_ACCOUNT_RLP = bytes.fromhex(
    'e094aa00000000000000000000000000000000000000c6c507c3c20105c0c0c0c0')
# was: e094aa00000000000000000000000000000000000000c6c507c3c20105c0c0c0c0
# EXPECTED_E2E_DIGEST      = 24f0ad8bc447e2a80bdc208c22a07d3a444bfaa952874d78fe7050df2598370d
#
# Construction (verified against the emitted code, not inferred):
#   1. tx rows at 0xa21a0000, count in `tx_storage_writes_count`; addr LE word at 0..31,
#      slot LE word at 32..63.
#   2. block container: one entry whose FIRST 64 BYTES equal the tx row's, and
#      `storage_writes_count` = 1. The scan is eight dword compares over 0..63 and a hit
#      does `addi s5, t5, 64` then jumps to `.Lbesc_have` -- which SKIPS
#      `slot_at_header_state_root`, so no witness globals are needed.
#   3. the container value must DIFFER from 5, or the net-zero check emits nothing.
#   4. call `bal_emit_storage_changes` with a0 = 1, then measure_account + emit_account.
#
# If the first run disagrees with the digest above, that is information about the
# producer. Do not update the constant to match the run.
# ---------------------------------------------------------------------------

EXPECTED_OUTER_RLP = bytes.fromhex(
    'f842'
    'e094aa00000000000000000000000000000000000000c6c501c3c20105c0c0c0c0'
    'e094bb00000000000000000000000000000000000000c6c501c3c20105c0c0c0c0')

if len(data) < 56:
    print(f"==> FAIL: probe output is {len(data)} bytes, need at least 56"); sys.exit(1)

bad = 0
for label, off, exp, meaning in CASES:
    got = struct.unpack_from('<Q', data, off)[0]
    if got == exp:
        print(f"  ok    {label:<28} = {got}")
    else:
        bad += 1
        print(f"  FAIL  {label:<28} expected {exp}, got {got}   ({meaning})")

if bad:
    pass

# --- digest check -----------------------------------------------------------
RC=[0x0000000000000001,0x0000000000008082,0x800000000000808A,0x8000000080008000,
0x000000000000808B,0x0000000080000001,0x8000000080008081,0x8000000000008009,
0x000000000000008A,0x0000000000000088,0x0000000080008009,0x000000008000000A,
0x000000008000808B,0x800000000000008B,0x8000000000008089,0x8000000000008003,
0x8000000000008002,0x8000000000000080,0x000000000000800A,0x800000008000000A,
0x8000000080008081,0x8000000000008080,0x0000000080000001,0x8000000080008008]
ROT=[[0,36,3,41,18],[1,44,10,45,2],[62,6,43,15,61],[28,55,25,21,56],[27,20,39,8,14]]
MASK=(1<<64)-1
def _rol(x,n):
    n%=64; return ((x<<n)|(x>>(64-n)))&MASK
def _f(A):
    for rnd in range(24):
        C=[A[x][0]^A[x][1]^A[x][2]^A[x][3]^A[x][4] for x in range(5)]
        D=[C[(x-1)%5]^_rol(C[(x+1)%5],1) for x in range(5)]
        for x in range(5):
            for y in range(5): A[x][y]^=D[x]
        B=[[0]*5 for _ in range(5)]
        for x in range(5):
            for y in range(5): B[y][(2*x+3*y)%5]=_rol(A[x][y],ROT[x][y])
        for x in range(5):
            for y in range(5): A[x][y]=B[x][y]^((~B[(x+1)%5][y])&B[(x+2)%5][y])
        A[0][0]^=RC[rnd]
    return A
def keccak256(data):
    rate=136; A=[[0]*5 for _ in range(5)]
    p=bytearray(data); p.append(0x01)
    while len(p)%rate: p.append(0)
    p[-1]|=0x80
    for off in range(0,len(p),rate):
        blk=p[off:off+rate]
        for i in range(rate//8):
            A[i%5][i//5]^=int.from_bytes(blk[i*8:i*8+8],'little')
        A=_f(A)
    return b''.join(A[i%5][i//5].to_bytes(8,'little') for i in range(4))

# Validate the reference itself before trusting it. sha3_256 is NOT keccak256, and a
# reference that silently computed the wrong function would agree with nothing.
if keccak256(b'').hex() != 'c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470':
    print("==> FAIL: the built-in keccak reference is wrong; refusing to compare"); sys.exit(1)

want = keccak256(EXPECTED_RLP).hex()
got  = data[64:96].hex()
if got == want:
    print(f"  ok    case 6  emitted digest              = {got[:16]}...")
else:
    bad += 1
    print(f"  FAIL  case 6  emitted digest {got[:16]}... != reference {want[:16]}...")
    print(f"        expected RLP was {EXPECTED_RLP.hex()}")

want_acct = keccak256(EXPECTED_ACCOUNT_RLP).hex()
got_acct  = data[96:128].hex()
if got_acct == want_acct:
    print(f"  ok    case 7  whole-account digest       = {got_acct[:16]}...")
else:
    bad += 1
    print(f"  FAIL  case 7  account digest {got_acct[:16]}... != reference {want_acct[:16]}...")
    print(f"        expected RLP was {EXPECTED_ACCOUNT_RLP.hex()}")

want_outer = keccak256(EXPECTED_OUTER_RLP).hex()
got_outer  = data[128:160].hex()
if got_outer == want_outer:
    print(f"  ok    case 8  outer-list digest (2 accts) = {got_outer[:16]}...")
else:
    bad += 1
    print(f"  FAIL  case 8  outer digest {got_outer[:16]}... != reference {want_outer[:16]}...")
    print(f"        expected RLP was {EXPECTED_OUTER_RLP.hex()}")

want_reads = keccak256(EXPECTED_READS_RLP).hex()
got_reads  = data[192:224].hex()
if got_reads == want_reads:
    print(f"  ok    case 9  emitted reads digest        = {got_reads[:16]}...")
else:
    bad += 1
    print(f"  FAIL  case 9  reads digest {got_reads[:16]}... != reference {want_reads[:16]}...")
    print(f"        expected only the unwritten slot: {EXPECTED_READS_RLP.hex()}")

# Case 10: the accounts are seeded in DESCENDING address order and `rebuild_hash` sorts
# before emitting, so the digest must equal case 8's ascending one. Seeding in order would
# pass whether or not the sort ever ran -- an unsorted emission is a well-formed BAL where
# every byte is right and only the sequence is wrong.
sort_status = struct.unpack_from('<Q', data, 224)[0]
rebuilt_w0  = struct.unpack_from('<Q', data, 232)[0]
want_w0     = int.from_bytes(keccak256(EXPECTED_OUTER_RLP)[:8], 'little')
if sort_status == 0xdead or rebuilt_w0 == 0xdead:
    bad += 1
    print("  FAIL  case 10 sort-then-rebuild          NEVER RAN (sentinel intact -- guest faulted)")
elif sort_status != 0:
    bad += 1
    print(f"  FAIL  case 10 canonical sort returned {sort_status}")
elif rebuilt_w0 != want_w0:
    bad += 1
    print(f"  FAIL  case 10 descending seed gave {rebuilt_w0:#018x}, want {want_w0:#018x} (sort did not run?)")
else:
    print(f"  ok    case 10 sort-then-rebuild digest    = {rebuilt_w0:#018x}")

# Case 11: the producer path. Digest word 0 only -- the output buffer is full.
e2e = struct.unpack_from('<Q', data, 240)[0]
want_e2e = int.from_bytes(keccak256(EXPECTED_E2E_ACCOUNT_RLP)[:8], 'little')
if e2e == 0xdead:
    bad += 1
    print("  FAIL  case 11 producer path              NEVER RAN (sentinel intact)")
elif e2e != want_e2e:
    bad += 1
    print(f"  FAIL  case 11 producer path {e2e:#018x} != {want_e2e:#018x}")
    print("        this is information about the PRODUCER; do not update the constant")
else:
    print(f"  ok    case 11 producer-path digest        = {e2e:#018x}")

# Case 12: the ordering fixture. Two slots, two changes on one, seeded DESCENDING at both
# levels; rebuild_hash sorts, so the digest must equal the ascending encoding. This is the
# first case in the suite that can tell a sort from its absence -- every other case has one
# element at every inner level, and a one-element list is sorted by definition.
#
# Expectation derived and frozen BEFORE the case was written:
EXPECTED_ORDER_RLP = bytes.fromhex(
    'e994aa00000000000000000000000000000000000000cfc503c3c20107c807c6c20105c20206c0c0c0c0')
order = struct.unpack_from('<Q', data, 248)[0]
want_order = int.from_bytes(keccak256(EXPECTED_ORDER_RLP)[:8], 'little')
if order == 0xdead:
    bad += 1
    print("  FAIL  case 12 ordering fixture           NEVER RAN (sentinel intact)")
elif order != want_order:
    bad += 1
    print(f"  FAIL  case 12 ordering fixture {order:#018x} != {want_order:#018x}")
    print("        KNOWN OPEN: the six ordering rules are implemented but this case")
    print("        disagrees. Do NOT update the constant -- it was derived from the spec")
    print("        before the case existed. Investigate the sorts or the derivation.")
else:
    print(f"  ok    case 12 ordering fixture            = {order:#018x}")

print()
if bad:
    print(f"==> FAIL: {bad} checks disagree with the RLP derivation")
    sys.exit(1)
print(f"==> PASS: {len(CASES)}/{len(CASES)} lengths and the emitted digest match the RLP derivation")
PY

# ---------------------------------------------------------------------------
# The two self-tests that had never executed: bal_rlp_encode_selftest (15 cases)
# and bal_canonical_sort_selftest (3 row sets).
# ---------------------------------------------------------------------------

echo
echo "==> emit zisk_bal_selftests"
lake exe codegen --program zisk_bal_selftests --halt linux93 -o "$OUT_DIR/bslf"

if [[ ! -f "$OUT_DIR/bslf.elf" ]]; then
  echo "==> FAIL: codegen produced no ELF for zisk_bal_selftests" >&2
  exit 1
fi

echo "==> run under spike"
"$SPIKE_RUN" "$OUT_DIR/bslf.elf" "$OUT_DIR/empty.input" "$OUT_DIR/bslf.output" \
  > "$OUT_DIR/bslf.emu.log" 2>&1 || true

python3 - "$OUT_DIR/bslf.output" <<'PY'
import struct, sys
data = open(sys.argv[1], 'rb').read()
if len(data) < 16:
    print(f"==> FAIL: selftest output is {len(data)} bytes, need 16"); sys.exit(1)

rlp  = struct.unpack_from('<Q', data, 0)[0]
sort = struct.unpack_from('<Q', data, 8)[0]

# 0xdead is seeded into both slots before the calls. A guest fault before the stores
# leaves the sentinel, which must NOT read as the clean 0 that means "passed" -- the
# first version of this probe faulted inside the sort self-test and reported two zeros.
SENTINEL = 0xdead
bad = 0
if rlp == SENTINEL:
    print("  FAIL  bal_rlp_encode_selftest      NEVER RAN (sentinel intact -- guest faulted)"); bad += 1
elif rlp == 0:
    print("  ok    bal_rlp_encode_selftest      PASS (15 cases)")
else:
    where = f"case {rlp - 100}" if rlp >= 100 else f"code {rlp}"
    print(f"  FAIL  bal_rlp_encode_selftest      failed at {where}"); bad += 1

if sort == SENTINEL:
    print("  FAIL  bal_canonical_sort_selftest  NEVER RAN (sentinel intact -- guest faulted)"); bad += 1
elif sort == 0:
    print("  ok    bal_canonical_sort_selftest  PASS (3 row sets)")
else:
    print(f"  FAIL  bal_canonical_sort_selftest  failed at row set {sort}"); bad += 1

print()
if bad:
    print(f"==> FAIL: {bad}/2 self-tests did not pass"); sys.exit(1)
print("==> PASS: 2/2 self-tests pass")
PY
