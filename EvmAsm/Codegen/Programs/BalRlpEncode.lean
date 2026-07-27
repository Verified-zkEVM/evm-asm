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
  "  mv a0, s1; jal ra, keccak_init\n" ++
  -- Scalars. Each is written into the work area as four LE limbs, low limb first,
  -- exactly as the guest's containers hold a U256.
  String.join ([ (["0", "0", "0", "0"], "0")
               , (["1", "0", "0", "0"], "1")
               , (["127", "0", "0", "0"], "127")
               , (["128", "0", "0", "0"], "128")
               , (["256", "0", "0", "0"], "256")
               , (["-1", "-1", "-1", "-1"], "2^256-1")
               , (["1", "0", "0", "0x0100000000000000"], "0x01..01")
               ].map (fun (limbs, _) =>
      balStoreField "s2" limbs ++
      "  mv a0, s1; mv a1, s2; mv a2, s0; jal ra, bal_rlp_emit_scalar\n")) ++
  -- Addresses: low 20 bytes of the LE word.
  balStoreField "s2" ["1", "0", "0", "0"] ++
  "  mv a0, s1; mv a1, s2; mv a2, s0; jal ra, bal_rlp_emit_address\n" ++
  balStoreField "s2" ["-1", "-1", "0xffffffff", "0"] ++
  "  mv a0, s1; mv a1, s2; mv a2, s0; jal ra, bal_rlp_emit_address\n" ++
  -- List headers, short and long form.
  String.join (["0", "1", "55", "56", "300", "70000"].map (fun n =>
      s!"  mv a0, s1; li a1, {n}; mv a2, s0; jal ra, bal_rlp_emit_list_header\n")) ++
  -- Finalise and compare against the reference digest.
  "  mv a0, s1; addi a1, s0, 32; jal ra, keccak_final\n" ++
  String.join (balRlpSelftestDigest.zipIdx.map (fun (d, i) =>
    s!"  li t0, {d}; ld t1, {32 + i * 8}(s0); bne t0, t1, .Lbrst_differ\n")) ++
  "  li a0, 0; j .Lbrst_ret\n" ++
  ".Lbrst_differ:\n" ++
  "  li a0, 1\n" ++
  ".Lbrst_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"

/-- All encoders, in emission order. -/
def balRlpEncodeFunctions : String :=
  balRlpScalarLenFunction ++
  balRlpEmitScalarFunction ++
  balRlpEmitAddressFunction ++
  balRlpEmitListHeaderFunction ++
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
