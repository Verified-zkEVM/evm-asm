/-
  EvmAsm.Codegen.Programs.BalRlpEncode

  RLP field encoders for the BAL rebuild — GH #10680.

  Implements the field-by-field mapping specified in the serialization contract on
  #10680, from the guest's in-memory representation to canonical RLP bytes. The
  contract was written by a different agent and is treated here as the
  specification: where this file and the contract disagree, the contract wins and
  the disagreement is a finding to report, not something to quietly resolve in the
  encoder. Keeping the spec author and the implementer separate is deliberate — it
  gives two independent derivations of the same mapping.

  ## The mapping, and why it is never a memory copy

  | field | in the guest | canonical RLP |
  |---|---|---|
  | `address` | low 20 bytes of a 256-bit stack word, four LE u64 limbs low-first | fixed 20-byte BE string, leading zeros RETAINED |
  | `slot`, `new_value`, `post_balance` | U256, same LE-limb layout | minimal BE integer string |
  | `block_access_index`, `new_nonce` | native scalar cell | minimal BE integer string |
  | `new_code` | pointer + length | raw bytes, unchanged |

  The canonical BE byte at index `b` of a 32-byte low-limb-first field is field byte
  `31 - b`, so every scalar is byte-reversed on the way out. This is the same
  reversal `BalCanonicalSort` applies to derive sort digits, and the runtime already
  does it for access-table addresses — a raw copy would emit limb order.

  ## The two rules that are easy to get wrong

  **Zero is the empty string.** A numeric zero has *empty* content and encodes as
  `0x80`, not `0x00`. The guest's own canonical decoder rejects non-empty content
  beginning with a zero byte (`RlpWalk.lean:184-201`), so emitting `0x00` would
  produce bytes the guest itself would refuse to parse.

  **An address is not a minimized integer.** Its leading zero bytes are retained: a
  20-byte address string is always 20 bytes plus the `0x94` header. Minimizing it
  would silently shorten addresses with leading zeros — a case that occurs in
  precompile addresses, which are almost all leading zeros.

  ## Encode-then-absorb, still O(1)

  Each encoder builds into a small caller-supplied scratch (at most 33 bytes: a
  1-byte header plus 32 payload) and then absorbs it. That keeps the routines
  independently testable against known vectors while holding memory constant — the
  scratch does not scale with the object being hashed.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.KeccakIncremental

namespace EvmAsm.Codegen

/-- Longest single scalar encoding: a 1-byte header plus 32 payload bytes. -/
def balRlpScalarMaxBytes : Nat := 33

/-! ## `bal_rlp_scalar_len`

    Minimal-BE payload length of a U256 held as four LE u64 limbs, low limb first.

    a0 = pointer to the 32-byte field
    a0 (out) = number of significant BE bytes, 0 for a numeric zero.

    The canonical BE most-significant byte is field byte 31, so the scan walks
    DOWNWARD from 31 and stops at the first non-zero. Returning 0 for zero is what
    makes the caller emit `0x80` rather than a zero byte. Leaf; clobbers t0-t2. -/
def balRlpScalarLenFunction : String :=
  "  .globl bal_rlp_scalar_len\n" ++
  "bal_rlp_scalar_len:\n" ++
  "  li t0, 31\n" ++
  ".Lbrsl_scan:\n" ++
  "  add t1, a0, t0; lbu t2, 0(t1)\n" ++
  "  bnez t2, .Lbrsl_found\n" ++
  "  beqz t0, .Lbrsl_zero\n" ++
  "  addi t0, t0, -1; j .Lbrsl_scan\n" ++
  ".Lbrsl_found:\n" ++
  "  addi a0, t0, 1; ret\n" ++
  ".Lbrsl_zero:\n" ++
  "  li a0, 0; ret\n"

/-! ## `bal_rlp_emit_scalar`

    Absorb the RLP encoding of a U256 held as LE limbs.

    a0 = keccak ctx, a1 = pointer to the 32-byte field, a2 = scratch (>= 33 bytes).

    Encoding, per the contract's scalar rule:
      * 0                   -> `0x80`            (empty content, NOT `0x00`)
      * a single byte < 0x80 -> that byte itself  (RLP self-encoding short form)
      * otherwise            -> `0x80 + len`, then `len` big-endian bytes

    No long-form branch: a U256 is at most 32 bytes, well inside the 55-byte short
    form, so a `0xb7`-family header is unreachable here by construction. -/
def balRlpEmitScalarFunction : String :=
  "  .globl bal_rlp_emit_scalar\n" ++
  "bal_rlp_emit_scalar:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++         -- ctx, field, scratch
  "  mv a0, s1; jal ra, bal_rlp_scalar_len\n" ++
  "  mv s3, a0\n" ++                               -- s3 = significant length
  "  bnez s3, .Lbres_nonzero\n" ++
  -- Zero: a single 0x80 byte.
  "  li t0, 0x80; sb t0, 0(s2)\n" ++
  "  mv a0, s0; mv a1, s2; li a2, 1; jal ra, keccak_absorb\n" ++
  "  j .Lbres_ret\n" ++
  ".Lbres_nonzero:\n" ++
  -- Single byte below 0x80 encodes as itself.
  "  li t0, 1; bne s3, t0, .Lbres_string\n" ++
  "  lbu t1, 0(s1); li t2, 0x80; bgeu t1, t2, .Lbres_string\n" ++
  "  sb t1, 0(s2)\n" ++
  "  mv a0, s0; mv a1, s2; li a2, 1; jal ra, keccak_absorb\n" ++
  "  j .Lbres_ret\n" ++
  ".Lbres_string:\n" ++
  -- 0x80 + len, then the significant bytes most-significant first. The BE byte at
  -- output index i is field byte (len-1-i), which is the reversal.
  "  li t0, 0x80; add t0, t0, s3; sb t0, 0(s2)\n" ++
  "  li t1, 0\n" ++
  ".Lbres_copy:\n" ++
  "  beq t1, s3, .Lbres_copy_done\n" ++
  "  sub t2, s3, t1; addi t2, t2, -1\n" ++          -- source index = len-1-i
  "  add t2, s1, t2; lbu t3, 0(t2)\n" ++
  "  addi t4, s2, 1; add t4, t4, t1; sb t3, 0(t4)\n" ++
  "  addi t1, t1, 1; j .Lbres_copy\n" ++
  ".Lbres_copy_done:\n" ++
  "  addi a2, s3, 1; mv a0, s0; mv a1, s2; jal ra, keccak_absorb\n" ++
  ".Lbres_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret\n"

/-! ## `bal_rlp_emit_address`

    Absorb an address as a fixed 20-byte RLP string: header `0x94` then the 20
    canonical BE bytes.

    a0 = keccak ctx, a1 = pointer to the 32-byte stack word, a2 = scratch (>= 21).

    Leading zeros are RETAINED — this is not a minimized integer. The address
    occupies the low 20 bytes of the LE-limb word, so canonical BE byte `i` is field
    byte `19 - i`. `0x94` is `0x80 + 20`. -/
def balRlpEmitAddressFunction : String :=
  "  .globl bal_rlp_emit_address\n" ++
  "bal_rlp_emit_address:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  "  li t0, 0x94; sb t0, 0(s2)\n" ++
  "  li t1, 0\n" ++
  ".Lbrea_copy:\n" ++
  "  li t0, 20; beq t1, t0, .Lbrea_done\n" ++
  "  li t2, 19; sub t2, t2, t1\n" ++                -- source index = 19 - i
  "  add t2, s1, t2; lbu t3, 0(t2)\n" ++
  "  addi t4, s2, 1; add t4, t4, t1; sb t3, 0(t4)\n" ++
  "  addi t1, t1, 1; j .Lbrea_copy\n" ++
  ".Lbrea_done:\n" ++
  "  mv a0, s0; mv a1, s2; li a2, 21; jal ra, keccak_absorb\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret\n"

/-! ## `bal_rlp_measure_into_throwaway`

    Measure any absorbing emitter by running it against a context that is DISCARDED.

    In a streaming design the usual measure-by-emitting-and-counting trick does not
    work: absorbing mutates the sponge and **cannot be undone**, so a measure pass that
    emitted into the live context would corrupt the digest. Handing the emitter a
    throwaway context preserves the property that matters — the emitter is the single
    implementation of the encoding rule, so measure and emit cannot disagree — while
    leaving the real sponge untouched.

    The name says `throwaway` because the failure mode of passing the live context is
    silent: the digest simply comes out wrong, with every field absorbed twice.

    a0 = throwaway ctx (its contents are meaningless afterwards)
    a1 = emitter address     a2, a3, a4 = the emitter's own a1, a2, a3
    a0 (out) = byte count the emitter reported

    The caller must reset the throwaway context before reuse, or its fill offset
    carries over and a later measurement absorbs at the wrong rate position — which
    changes nothing about the COUNT, but leaves a trap for anyone who later reads the
    throwaway context expecting a digest. -/
def balRlpMeasureIntoThrowawayFunction : String :=
  "bal_rlp_measure_into_throwaway:\n" ++
  "  addi sp, sp, -16; sd ra, 0(sp); sd s0, 8(sp)\n" ++
  "  mv s0, a1\n" ++                                    -- s0 = emitter address
  "  mv a1, a2; mv a2, a3; mv a3, a4\n" ++              -- shift the emitter's args down
  "  jalr ra, 0(s0)\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); addi sp, sp, 16\n" ++
  "  ret\n"

/-! ## `bal_rlp_emit_bytes`

    The RLP **byte-string** shape, absorbed into a keccak context. The one shape this
    layer lacked, and the reason a fully-streaming walk was not previously possible:
    `CodeChange.new_code` is a variable-length blob up to the EIP-170 limit, which
    `bal_rlp_emit_scalar` cannot express — a scalar is at most 32 bytes and takes no
    long-form branch.

    Yellow paper §B, string rule, all three cases:

        len == 1 AND byte < 0x80   → the byte alone, no prefix
        len < 56                   → 0x80 + len, then the bytes
        else                       → 0xb7 + bc, then a bc-byte BE length,
                                     then the bytes  (bc = 1..8, no leading zeros)

    **The single-byte case is not an optimisation and must not be skipped**: emitting
    `0x81 0x05` where the rule says `0x05` is a different byte string, and the digest
    diverges silently.

    Calling convention:
      a0 = keccak ctx
      a1 = data ptr
      a2 = data byte length
      a3 = scratch (>= 9 bytes, for the header)
      ra = return
      a0 (out) = TOTAL BYTES ABSORBED — header plus payload.

    **The return value is what makes measuring possible without a second
    implementation.** Hand this routine a throwaway context and the count it returns is
    the encoded length, computed by the emitter itself. See
    `bal_rlp_measure_into_throwaway`. -/
def balRlpEmitBytesFunction : String :=
  "bal_rlp_emit_bytes:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++       -- ctx, data, len, scratch
  -- CASE 1: exactly one byte, below 0x80 -- the byte is its own encoding.
  "  li t0, 1; bne s2, t0, .Lbreb_short\n" ++
  "  lbu t1, 0(s1); li t2, 0x80; bgeu t1, t2, .Lbreb_short\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1; jal ra, keccak_absorb\n" ++
  "  li a0, 1; j .Lbreb_ret\n" ++
  ".Lbreb_short:\n" ++
  -- CASE 2: fewer than 56 bytes -- 0x80 + len, then the payload.
  "  li t0, 56; bgeu s2, t0, .Lbreb_long\n" ++
  "  li t1, 0x80; add t1, t1, s2; sb t1, 0(s3)\n" ++
  "  mv a0, s0; mv a1, s3; li a2, 1; jal ra, keccak_absorb\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; jal ra, keccak_absorb\n" ++
  "  addi a0, s2, 1; j .Lbreb_ret\n" ++
  ".Lbreb_long:\n" ++
  -- CASE 3: 0xb7 + bc, a bc-byte BE length, then the payload. bc is the significant
  -- byte count of the length with NO leading zeros, which is what makes the encoding
  -- canonical -- a bc that included a leading zero would still parse and would hash
  -- differently.
  "  li t0, 0; mv t1, s2\n" ++                                -- t0 = bc, t1 = len
  ".Lbreb_bc:\n" ++
  "  beqz t1, .Lbreb_bc_done; addi t0, t0, 1; srli t1, t1, 8; j .Lbreb_bc\n" ++
  ".Lbreb_bc_done:\n" ++
  "  li t2, 0xb7; add t2, t2, t0; sb t2, 0(s3)\n" ++          -- scratch[0] = 0xb7+bc
  -- write the length big-endian into scratch[1 .. 1+bc)
  "  mv t3, t0\n" ++
  ".Lbreb_len:\n" ++
  "  beqz t3, .Lbreb_len_done\n" ++
  "  addi t4, t3, -1; slli t4, t4, 3; srl t5, s2, t4; andi t5, t5, 255\n" ++
  "  sub t6, t0, t3; addi t6, t6, 1; add t6, s3, t6; sb t5, 0(t6)\n" ++
  "  addi t3, t3, -1; j .Lbreb_len\n" ++
  ".Lbreb_len_done:\n" ++
  "  addi a2, t0, 1\n" ++                                     -- header length = 1 + bc
  "  mv a0, s0; mv a1, s3; jal ra, keccak_absorb\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; jal ra, keccak_absorb\n" ++
  "  li t0, 0; mv t1, s2\n" ++
  ".Lbreb_bc2:\n" ++
  "  beqz t1, .Lbreb_bc2_done; addi t0, t0, 1; srli t1, t1, 8; j .Lbreb_bc2\n" ++
  ".Lbreb_bc2_done:\n" ++
  "  add a0, s2, t0; addi a0, a0, 1\n" ++                     -- len + bc + 1
  ".Lbreb_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret\n"

/-! ## `bal_rlp_emit_list_header`

    Absorb an RLP list header for a payload of `a1` bytes.

    a0 = keccak ctx, a1 = payload length, a2 = scratch (>= 5).

    `0xc0 + len` for `len <= 55`; otherwise `0xf7 + lenOfLen` then the length in
    minimal BE. Both branches are reachable here, unlike the scalar case: an
    account's payload routinely exceeds 55 bytes. -/
def balRlpEmitListHeaderFunction : String :=
  "  .globl bal_rlp_emit_list_header\n" ++
  "bal_rlp_emit_list_header:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  "  li t0, 55; bgtu s1, t0, .Lbrelh_long\n" ++
  "  li t0, 0xc0; add t0, t0, s1; sb t0, 0(s2)\n" ++
  "  mv a0, s0; mv a1, s2; li a2, 1; jal ra, keccak_absorb\n" ++
  "  j .Lbrelh_ret\n" ++
  ".Lbrelh_long:\n" ++
  -- Count the minimal BE bytes of the length, then emit 0xf7+n and those bytes.
  "  li t1, 0; mv t2, s1\n" ++
  ".Lbrelh_count:\n" ++
  "  beqz t2, .Lbrelh_counted\n" ++
  "  addi t1, t1, 1; srli t2, t2, 8; j .Lbrelh_count\n" ++
  ".Lbrelh_counted:\n" ++
  "  li t0, 0xf7; add t0, t0, t1; sb t0, 0(s2)\n" ++
  "  li t3, 0\n" ++
  ".Lbrelh_emit:\n" ++
  "  beq t3, t1, .Lbrelh_emitted\n" ++
  "  sub t4, t1, t3; addi t4, t4, -1; slli t4, t4, 3\n" ++   -- shift = 8*(n-1-i)
  "  srl t5, s1, t4; andi t5, t5, 255\n" ++
  "  addi t6, s2, 1; add t6, t6, t3; sb t5, 0(t6)\n" ++
  "  addi t3, t3, 1; j .Lbrelh_emit\n" ++
  ".Lbrelh_emitted:\n" ++
  "  addi a2, t1, 1; mv a0, s0; mv a1, s2; jal ra, keccak_absorb\n" ++
  ".Lbrelh_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret\n"

/-! ## `bal_rlp_encode_selftest` -- byte agreement with the REFERENCE encoder

    The encoders' correctness criterion is that their bytes equal the reference
    RLP encoder's bytes. Comparing bytes directly would need the reference output
    in the guest; instead the self-test absorbs its whole output into one keccak
    context and compares the digest against a constant derived offline from
    `ethereum_rlp.rlp.encode` itself.

    That is congruence against the reference implementation, and the direction
    matters: nothing is inferred FROM the digests matching, so no collision
    assumption is involved. The digest is a compact way to compare 128 bytes of
    output; a mismatch means an encoding rule diverges.

    The vector is chosen so that every rule the contract states is load-bearing:

    | case | rule exercised |
    |---|---|
    | `0` | zero is the EMPTY string `0x80`, not `0x00` |
    | `1`, `127` | single byte below `0x80` self-encodes |
    | `128` | first value needing `0x81` + one byte |
    | `256` | two payload bytes, no leading zero |
    | `2^256-1` | maximum width, 32 payload bytes |
    | `0x01…01` | interior zero bytes must be RETAINED, only leading ones dropped |
    | `0x00…01` address | leading zeros RETAINED (precompile shape) |
    | `0xff…ff` address | no minimization at the top end |
    | list `0`, `1`, `55` | short form `0xc0+len` including both edges |
    | list `56`, `300`, `70000` | long form `0xf7+n`, at one, two and three length bytes |

    ABI: a0 = scratch (>= 64 bytes), a1 = keccak ctx, a2 = a 32-byte scalar work
    area. Returns a0 = 0 on agreement, 1 on mismatch.

    Expected digest, from the reference encoder over the same 128-byte sequence:
    `6227255a8b7635117a948a065cfd8aa60a2b5cb810a1eb1d76acc60546981dde`. -/
def balRlpSelftestDigest : List String :=
  ["0x1135768b5a252762", "0xa68afd5c068a947a", "0x1deba110b85c2b0a", "0xde1d984605c6ac76"]

/-- Store a 32-byte LE-limb field equal to the given big-endian byte list. -/
private def balStoreField (reg : String) (limbsLE : List String) : String :=
  String.join (limbsLE.zipIdx.map (fun (v, i) =>
    s!"  li t0, {v}; sd t0, {i * 8}({reg})\n"))

def balRlpEncodeSelftestFunction : String :=
  "  .globl bal_rlp_encode_selftest\n" ++
  "bal_rlp_encode_selftest:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++          -- scratch, ctx, field work area
  "  li s3, 0\n" ++                                 -- s3 = current case index
  "  mv a0, s1; jal ra, keccak_init\n" ++
  -- Scalars. Each is written into the work area as four LE limbs, low limb first,
  -- exactly as the guest's containers hold a U256.
  String.join ([ (["0", "0", "0", "0"], 1)
               , (["1", "0", "0", "0"], 1)
               , (["127", "0", "0", "0"], 1)
               , (["128", "0", "0", "0"], 2)
               , (["256", "0", "0", "0"], 3)
               , (["-1", "-1", "-1", "-1"], 33)
               , (["1", "0", "0", "0x0100000000000000"], 33)
               ].zipIdx.map (fun ((limbs, expect), i) =>
      balStoreField "s2" limbs ++
      "  mv a0, s1; mv a1, s2; mv a2, s0; jal ra, bal_rlp_emit_scalar\n" ++
      "  mv a0, s2; jal ra, bal_rlp_scalar_rlp_len\n" ++
      s!"  li s3, {i}; li t0, {expect}; bne a0, t0, .Lbrst_len_differ\n")) ++
  -- Addresses: low 20 bytes of the LE word.
  balStoreField "s2" ["1", "0", "0", "0"] ++
  "  mv a0, s1; mv a1, s2; mv a2, s0; jal ra, bal_rlp_emit_address\n" ++
  "  li s3, 7; li a0, 21; li t0, 21; bne a0, t0, .Lbrst_len_differ\n" ++
  balStoreField "s2" ["-1", "-1", "0xffffffff", "0"] ++
  "  mv a0, s1; mv a1, s2; mv a2, s0; jal ra, bal_rlp_emit_address\n" ++
  "  li s3, 8; li a0, 21; li t0, 21; bne a0, t0, .Lbrst_len_differ\n" ++
  -- List headers, short and long form.
  String.join ([(0, 1), (1, 1), (55, 1), (56, 2), (300, 3), (70000, 4)].zipIdx.map
      (fun ((n, expect), i) =>
      s!"  mv a0, s1; li a1, {n}; mv a2, s0; jal ra, bal_rlp_emit_list_header\n" ++
      s!"  li a0, {n}; jal ra, bal_rlp_list_header_len\n" ++
      s!"  li s3, {9 + i}; li t0, {expect}; bne a0, t0, .Lbrst_len_differ\n")) ++
  -- Finalise and compare against the reference digest.
  "  mv a0, s1; addi a1, s0, 32; jal ra, keccak_final\n" ++
  String.join (balRlpSelftestDigest.zipIdx.map (fun (d, i) =>
    s!"  li t0, {d}; ld t1, {32 + i * 8}(s0); bne t0, t1, .Lbrst_differ\n")) ++
  -- Each measure result was asserted AGAINST ITS OWN EXPECTED LENGTH above, not
  -- accumulated into a total. A total cannot distinguish correct lengths from
  -- OFFSETTING ERRORS: one case over by a byte and another under by a byte sums to
  -- the same 128 and passes. This vector spans the 0x81 prefix, two-byte payloads,
  -- the 55/56 boundary and one, two and three length bytes, so a short-form
  -- off-by-one compensated by a long-form off-by-one is exactly the available shape.
  -- Per-case assertion removes that path rather than making it unlikely.
  "  li a0, 0; j .Lbrst_ret\n" ++
  ".Lbrst_len_differ:\n" ++
  -- 100 + case index: localises WHICH length disagreed, and stays distinguishable
  -- from the digest mismatch code 1.
  "  addi a0, s3, 100; j .Lbrst_ret\n" ++
  ".Lbrst_differ:\n" ++
  "  li a0, 1\n" ++
  ".Lbrst_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"

/-! ## Length helpers for the two-pass walk

    RLP puts a list's header BEFORE its payload, and the header's own size depends
    on the payload length. A serializer that streams into a hash — rather than
    building the bytes in a buffer it can back-fill — therefore has to know every
    payload length before it emits anything. So the walk is two passes: measure,
    then emit.

    These two helpers are the part of that arithmetic which does NOT depend on any
    row layout, so they are correct regardless of how the builder's rows are
    finally shaped. Everything shape-dependent belongs in the walk itself.

    Both are pure functions of their inputs with no memory writes, so they can be
    called in the measure pass without disturbing the sponge. -/

/-! ### `bal_rlp_scalar_rlp_len`

    Total encoded length of a U256 held as LE limbs, header included.

    a0 = pointer to the 32-byte field.  a0 (out) = encoded byte count.

    Mirrors `bal_rlp_emit_scalar`'s three cases exactly, and that mirroring is the
    hazard: if the two ever disagree, the measure pass reserves a different number of
    bytes than the emit pass writes, and every subsequent header in the stream is
    wrong. The cases are `0` -> 1 byte (`0x80`), a single byte below `0x80` -> 1 byte,
    otherwise `1 + len`. Leaf; clobbers t0. -/
def balRlpScalarRlpLenFunction : String :=
  "  .globl bal_rlp_scalar_rlp_len\n" ++
  "bal_rlp_scalar_rlp_len:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp)\n" ++
  "  mv s0, a0\n" ++
  "  jal ra, bal_rlp_scalar_len\n" ++
  -- a0 = significant byte count; 0 means the value is zero -> the single 0x80.
  "  beqz a0, .Lbrsr_one\n" ++
  "  li t0, 1; bne a0, t0, .Lbrsr_string\n" ++
  -- One significant byte: self-encoding only when it is below 0x80.
  "  lbu t0, 0(s0); li a0, 1\n" ++
  "  li t1, 0x80; bltu t0, t1, .Lbrsr_ret\n" ++
  "  li a0, 2; j .Lbrsr_ret\n" ++         -- 0x81 plus the byte
  ".Lbrsr_string:\n" ++
  "  addi a0, a0, 1; j .Lbrsr_ret\n" ++   -- 0x80+len header plus len bytes
  ".Lbrsr_one:\n" ++
  "  li a0, 1\n" ++
  ".Lbrsr_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); addi sp, sp, 16\n" ++
  "  ret\n"

/-! ### `bal_rlp_list_header_len`

    Size of the RLP list header for a payload of `a0` bytes.

    a0 (out) = 1 for a payload of 55 or fewer bytes, else 1 plus the number of
    minimal big-endian bytes needed for the length.

    Mirrors `bal_rlp_emit_list_header`. Pure arithmetic; no memory access at all, so
    it is safe to call anywhere in the measure pass. Leaf; clobbers t0-t2. -/
def balRlpListHeaderLenFunction : String :=
  "  .globl bal_rlp_list_header_len\n" ++
  "bal_rlp_list_header_len:\n" ++
  "  li t0, 55; bgtu a0, t0, .Lbrlhl_long\n" ++
  "  li a0, 1; ret\n" ++
  ".Lbrlhl_long:\n" ++
  "  li t1, 0; mv t2, a0\n" ++
  ".Lbrlhl_count:\n" ++
  "  beqz t2, .Lbrlhl_counted\n" ++
  "  addi t1, t1, 1; srli t2, t2, 8; j .Lbrlhl_count\n" ++
  ".Lbrlhl_counted:\n" ++
  "  addi a0, t1, 1; ret\n"

/-- All encoders, in emission order. -/
def balRlpEncodeFunctions : String :=
  balRlpScalarLenFunction ++
  balRlpEmitScalarFunction ++
  balRlpEmitAddressFunction ++
  balRlpMeasureIntoThrowawayFunction ++
  balRlpEmitBytesFunction ++
  balRlpEmitListHeaderFunction ++
  balRlpScalarRlpLenFunction ++
  balRlpListHeaderLenFunction ++
  balRlpEncodeSelftestFunction

/-! ## Anti-drift guards on the emitted text

    Not a correctness argument. The encoders' correctness is byte agreement with
    the reference RLP encoder, which is a runtime comparison; these only stop a
    later edit from silently changing a rule.

    Fully qualified, one per line — a `#guard` in the wrong namespace auto-binds its
    identifiers as implicits and passes vacuously, and one wrapping to a second line
    silently covers only the first. -/

#guard balRlpScalarMaxBytes == 33

#guard (balRlpEncodeFunctions.splitOn "bal_rlp_scalar_len:").length == 2
#guard (balRlpEncodeFunctions.splitOn "bal_rlp_emit_scalar:").length == 2
#guard (balRlpEncodeFunctions.splitOn "bal_rlp_emit_address:").length == 2
#guard (balRlpEncodeFunctions.splitOn "bal_rlp_emit_list_header:").length == 2
#guard (balRlpEncodeFunctions.splitOn "bal_rlp_scalar_rlp_len:").length == 2
#guard (balRlpEncodeFunctions.splitOn "bal_rlp_list_header_len:").length == 2
-- The byte-string emitter's three yellow-paper cases must all be present. The
-- single-byte-no-prefix case is the one most easily "optimised" away, and emitting
-- 0x81 0x05 where the rule says 0x05 is a different string with a different digest.
#guard (balRlpEmitBytesFunction.splitOn ".Lbreb_short:").length == 2
#guard (balRlpEmitBytesFunction.splitOn ".Lbreb_long:").length == 2
#guard (balRlpEmitBytesFunction.splitOn "li t2, 0x80; bgeu t1, t2, .Lbreb_short").length == 2
-- 0x80 + len for the short form, 0xb7 + bc for the long form.
#guard (balRlpEmitBytesFunction.splitOn "li t1, 0x80; add t1, t1, s2").length == 2
#guard (balRlpEmitBytesFunction.splitOn "li t2, 0xb7; add t2, t2, t0").length == 2
-- The 56-byte boundary decides short versus long and must be an unsigned compare.
#guard (balRlpEmitBytesFunction.splitOn "li t0, 56; bgeu s2, t0, .Lbreb_long").length == 2
-- It must return a byte count, since that is what makes throwaway measuring work.
#guard (balRlpEmitBytesFunction.splitOn "add a0, s2, t0; addi a0, a0, 1").length == 2

-- The agreement check must be PER CASE, not an aggregate. A total cannot distinguish
-- correct lengths from offsetting errors -- one case over and another under sums to
-- the same value and passes -- and this vector spans the short-form/long-form
-- boundary where exactly that compensation is available.
--
-- Fifteen cases, so fifteen comparisons: 7 scalars, 2 addresses, 6 list headers.
#guard (balRlpEncodeSelftestFunction.splitOn "bne a0, t0, .Lbrst_len_differ").length == 16
-- No aggregate may remain, or a later edit could quietly go back to summing.
#guard (balRlpEncodeSelftestFunction.splitOn "li t0, 128; bne s3, t0").length == 1
-- The failure must LOCALISE which case disagreed, and stay distinguishable from the
-- digest mismatch code 1.
#guard (balRlpEncodeSelftestFunction.splitOn "addi a0, s3, 100").length == 2

-- COVERAGE TRIPWIRE. The per-case vector covers the fifteen cases in it; the
-- divergence risk this file carries is borne by routines added LATER, whose measure
-- and emit paths would be mirrored but untested. There is no way to assert "every
-- future routine has a case", so this asserts the ROUTINE COUNT instead: adding a
-- seventh `.globl bal_rlp_*` breaks the build and forces the author to look at the
-- self-test rather than discover the gap when a header comes out a byte short.
--
-- If you are here because you added a routine: add its case to
-- `bal_rlp_encode_selftest` and its expected length to the per-case assertions, THEN
-- bump this. Bumping it alone restores the build and removes the only thing that
-- would have told you.
#guard (balRlpEncodeFunctions.splitOn "  .globl bal_rlp_").length == 8

-- THE INVARIANT THAT HAS NO ESCAPE HATCH. The count above can be silenced by bumping
-- a number, which makes it a tripwire rather than a check. This one cannot: EVERY
-- measure call must have a per-case assertion, and every assertion must correspond to
-- a measure call or to one of the two fixed-width address cases. Add a measure call
-- without an assertion and it fails; add an assertion without a measure call and it
-- fails. `splitOn` lengths are occurrences + 1, hence the -2.
#guard (balRlpEncodeSelftestFunction.splitOn "bne a0, t0, .Lbrst_len_differ").length
         == (balRlpEncodeSelftestFunction.splitOn "jal ra, bal_rlp_scalar_rlp_len").length
          + (balRlpEncodeSelftestFunction.splitOn "jal ra, bal_rlp_list_header_len").length
          + (balRlpEncodeSelftestFunction.splitOn "li t0, 21; bne").length - 2

-- The vector must keep spanning every distinct length class the encoders can produce:
-- 1 (empty/self-encoding and the short header), 2, 3 and 4 (one, two and three header
-- length bytes), 21 (fixed address) and 33 (full-width U256). Pinning the classes stops
-- a future edit from deleting the only case that exercises one.
#guard (balRlpEncodeSelftestFunction.splitOn "li t0, 1; bne").length >= 2
#guard (balRlpEncodeSelftestFunction.splitOn "li t0, 2; bne").length >= 2
#guard (balRlpEncodeSelftestFunction.splitOn "li t0, 3; bne").length >= 2
#guard (balRlpEncodeSelftestFunction.splitOn "li t0, 4; bne").length >= 2
#guard (balRlpEncodeSelftestFunction.splitOn "li t0, 21; bne").length == 3
#guard (balRlpEncodeSelftestFunction.splitOn "li t0, 33; bne").length == 3

-- Every routine currently defined IS exercised by the self-test. Checked by name so
-- the tripwire above cannot be satisfied by a routine that exists but is never run.
#guard (balRlpEncodeSelftestFunction.splitOn "jal ra, bal_rlp_scalar_len").length >= 1
#guard (balRlpEncodeSelftestFunction.splitOn "jal ra, bal_rlp_emit_scalar").length == 8
#guard (balRlpEncodeSelftestFunction.splitOn "jal ra, bal_rlp_emit_address").length == 3
#guard (balRlpEncodeSelftestFunction.splitOn "jal ra, bal_rlp_emit_list_header").length == 7
#guard (balRlpEncodeSelftestFunction.splitOn "jal ra, bal_rlp_scalar_rlp_len").length == 8
#guard (balRlpEncodeSelftestFunction.splitOn "jal ra, bal_rlp_list_header_len").length == 7

-- Zero must encode as the EMPTY string 0x80, never as 0x00. The guest's own
-- decoder rejects non-empty content starting with a zero byte, so 0x00 would emit
-- bytes the guest itself refuses to parse.
#guard (balRlpEmitScalarFunction.splitOn "li t0, 0x80; sb t0, 0(s2)").length == 2
-- The length scan must return 0 for a zero field, which is what selects that path.
#guard (balRlpScalarLenFunction.splitOn "li a0, 0; ret").length == 2

-- The scalar scan must walk DOWNWARD from byte 31: the canonical BE most
-- significant byte is the field's HIGHEST byte, because the field is LE limbs.
-- An upward scan would find the least significant non-zero byte and report a
-- plausible wrong length.
#guard (balRlpScalarLenFunction.splitOn "li t0, 31").length == 2
#guard (balRlpScalarLenFunction.splitOn "addi t0, t0, -1").length == 2

-- Scalar payload bytes must be REVERSED out of the field (source index len-1-i).
#guard (balRlpEmitScalarFunction.splitOn "sub t2, s3, t1; addi t2, t2, -1").length == 2

-- An address is a FIXED 20-byte string with leading zeros retained: header 0x94
-- and 21 absorbed bytes, never a minimized integer. Precompile addresses are
-- almost all leading zeros, so minimizing would shorten exactly those.
#guard (balRlpEmitAddressFunction.splitOn "li t0, 0x94").length == 2
#guard (balRlpEmitAddressFunction.splitOn "li a2, 21").length == 2
-- ...and reversed out of the low 20 bytes (source index 19-i).
#guard (balRlpEmitAddressFunction.splitOn "li t2, 19; sub t2, t2, t1").length == 2

-- The list header needs BOTH forms. Unlike the scalar case the long form is
-- reachable: an account's payload routinely exceeds 55 bytes, so a short-form-only
-- encoder would corrupt every non-trivial account rather than failing loudly.
#guard (balRlpEmitListHeaderFunction.splitOn "li t0, 0xc0").length == 2
#guard (balRlpEmitListHeaderFunction.splitOn "li t0, 0xf7").length == 2
#guard (balRlpEmitListHeaderFunction.splitOn "li t0, 55").length == 2

end EvmAsm.Codegen
