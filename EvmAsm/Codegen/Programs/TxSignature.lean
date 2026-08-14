/-
  EvmAsm.Codegen.Programs.TxSignature

  Transaction signature extractors carved out of
  `EvmAsm.Codegen.Programs.Tx` per the file-size hard cap. Hosts:

    K138  tx_legacy_extract_signature                (9-field legacy)
    K139  tx_eip1559_extract_signature               (12-field EIP-1559)
    K140  tx_eip2930_extract_signature               (11-field EIP-2930)
    K141  tx_eip4844_extract_signature               (14-field EIP-4844)
    K142  tx_eip7702_extract_signature               (13-field EIP-7702)
    K143  eip7702_authorization_extract_signature    (auth-tuple sig)

  Each extracts `(y_parity / v, r, s)` from the appropriate RLP
  shape into a caller-supplied 65-byte buffer. The extractors use
  `Programs/RlpWalk.lean` cursor helpers so adjacent signature fields
  are consumed by one list walk, then canonical-strict content decoders
  validate and decode the scalar payloads.

  The six generated source strings are now Program-backed conversions. The
  reusable String combinator remains above the generated blocks as the source
  pattern for future extractors; `scripts/asm_to_program.py rewrite` evaluates
  such combinator calls through Lean before generating the Program, fixture,
  and `_eq_prog` drift guard.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

private def repeatAsm : Nat -> String -> String
  | 0, _ => ""
  | n + 1, s => s ++ repeatAsm n s

private def txSignatureSkipAsm (p : String) (n : Nat) : String :=
  repeatAsm n <|
    "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, ." ++ p ++ "_fail; mv s5, a0\n"

private def txSignatureWalkExtractFunction (name p ptrComment : String) (skip : Nat) : String :=
  name ++ ":\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                   # " ++ ptrComment ++ " ptr\n" ++
  "  mv s1, a1                   # " ++ ptrComment ++ " len\n" ++
  "  mv s2, a2                   # y_parity/v out\n" ++
  "  mv s3, a3                   # r out (32 B)\n" ++
  "  mv s4, a4                   # s out (32 B)\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, ." ++ p ++ "_fail\n" ++
  "  mv s5, a0                   # cursor\n" ++
  "  mv s6, a1                   # end\n" ++
  txSignatureSkipAsm p skip ++
  "  # ---- Signature field 0: y_parity/v (canonical uint <= 8 bytes) -> u64 ----\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, ." ++ p ++ "_fail\n" ++
  "  sub t0, a0, a2; mv s7, a0; mv a0, t0; mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64_strict\n" ++
  "  bnez a1, ." ++ p ++ "_size\n" ++
  "  sd a0, 0(s2); mv s5, s7\n" ++
  "  # ---- Signature field 1: r (canonical u256 BE <= 32 bytes) ----\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, ." ++ p ++ "_fail\n" ++
  "  sub t0, a0, a2; mv s7, a0; mv a0, t0; mv a1, a2; mv a2, s3\n" ++
  "  jal ra, rlp_content_to_u256_be_strict\n" ++
  "  bnez a0, ." ++ p ++ "_size\n" ++
  "  mv s5, s7\n" ++
  "  # ---- Signature field 2: s (canonical u256 BE <= 32 bytes) ----\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, ." ++ p ++ "_fail\n" ++
  "  sub t0, a0, a2; mv a0, t0; mv a1, a2; mv a2, s4\n" ++
  "  jal ra, rlp_content_to_u256_be_strict\n" ++
  "  bnez a0, ." ++ p ++ "_size\n" ++
  "  li a0, 0\n" ++
  "  j ." ++ p ++ "_ret\n" ++
  "." ++ p ++ "_fail:\n" ++
  "  li a0, 1\n" ++
  "  j ." ++ p ++ "_ret\n" ++
  "." ++ p ++ "_size:\n" ++
  "  li a0, 2\n" ++
  "." ++ p ++ "_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-! ## tx_legacy_extract_signature -- PR-K138

    Extract `(v, r, s)` from a 9-field legacy transaction RLP:

      legacy_tx = rlp([nonce, gas_price, gas_limit, to,
                       value, data, v, r, s])

    Output convention:
      * v: u64 (the on-the-wire v byte; pass through
        `derive_chain_id_from_v` (K37) to split into chain_id /
        is_eip155).
      * r, s: 32-byte right-aligned, zero-padded big-endian
        buffers — the canonical signature scalars.

    Used by the legacy-tx sender-recovery path:
      1. K138 extracts `(v, r, s)`.
      2. K37 `derive_chain_id_from_v` splits v.
      3. tx_signing_hash_legacy (future) computes the message
         digest from fields 0..5 (+ optional EIP-155 tail).
      4. `zkvm_secp256k1_ecrecover` produces a 64-byte pubkey.
      5. K99 `address_from_pubkey` derives the 20-byte sender
         address.

    PR-K36 `tx_legacy_decode` already extracts these three
    fields as part of full-record extraction; K138 is the
    narrower accessor for callers that only need the signature
    (e.g., when the other fields were already extracted by a
    previous pass).

    Composes:
      - RlpWalk cursor helpers across fields 6, 7, 8
      - canonical content decoders for v/r/s

    Calling convention:
      a0 (input)  : tx_rlp ptr
      a1 (input)  : tx_rlp byte length
      a2 (input)  : v u64 out ptr
      a3 (input)  : r 32-byte BE out ptr
      a4 (input)  : s 32-byte BE out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fields 6/7/8 missing / trailing bytes
        2 : v > 8 bytes (cannot fit in u64) or r/s > 32 bytes -/
def txLegacyExtractSignature_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_legacy_extract_signature + 68)),
    .BNE .x12 .x0 (brOff (GuestAddrs.tx_legacy_extract_signature + 352) (GuestAddrs.tx_legacy_extract_signature + 72)),
    .MV .x21 .x10,
    .MV .x22 .x11,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_legacy_extract_signature + 92)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_legacy_extract_signature + 352) (GuestAddrs.tx_legacy_extract_signature + 96)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_legacy_extract_signature + 112)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_legacy_extract_signature + 352) (GuestAddrs.tx_legacy_extract_signature + 116)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_legacy_extract_signature + 132)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_legacy_extract_signature + 352) (GuestAddrs.tx_legacy_extract_signature + 136)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_legacy_extract_signature + 152)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_legacy_extract_signature + 352) (GuestAddrs.tx_legacy_extract_signature + 156)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_legacy_extract_signature + 172)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_legacy_extract_signature + 352) (GuestAddrs.tx_legacy_extract_signature + 176)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_legacy_extract_signature + 192)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_legacy_extract_signature + 352) (GuestAddrs.tx_legacy_extract_signature + 196)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_legacy_extract_signature + 212)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_legacy_extract_signature + 352) (GuestAddrs.tx_legacy_extract_signature + 216)),
    .SUB .x5 .x10 .x12,
    .MV .x23 .x10,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.tx_legacy_extract_signature + 236)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_legacy_extract_signature + 360) (GuestAddrs.tx_legacy_extract_signature + 240)),
    .SD .x18 .x10 (0 : BitVec 12),
    .MV .x21 .x23,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_legacy_extract_signature + 260)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_legacy_extract_signature + 352) (GuestAddrs.tx_legacy_extract_signature + 264)),
    .SUB .x5 .x10 .x12,
    .MV .x23 .x10,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_legacy_extract_signature + 288)),
    .BNE .x10 .x0 (brOff (GuestAddrs.tx_legacy_extract_signature + 360) (GuestAddrs.tx_legacy_extract_signature + 292)),
    .MV .x21 .x23,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_legacy_extract_signature + 308)),
    .BNE .x11 .x0 (40 : BitVec 13),
    .BNE .x10 .x22 (brOff (GuestAddrs.tx_legacy_extract_signature + 352) (GuestAddrs.tx_legacy_extract_signature + 316)),
    .SUB .x5 .x10 .x12,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_legacy_extract_signature + 336)),
    .BNE .x10 .x0 (20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txLegacyExtractSignature_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txLegacyExtractSignature_relocs : RelocTable :=
  [ (17, .jal .x1 "rlp_walk_init"),
    (23, .jal .x1 "rlp_walk_next"),
    (28, .jal .x1 "rlp_walk_next"),
    (33, .jal .x1 "rlp_walk_next"),
    (38, .jal .x1 "rlp_walk_next"),
    (43, .jal .x1 "rlp_walk_next"),
    (48, .jal .x1 "rlp_walk_next"),
    (53, .jal .x1 "rlp_walk_next"),
    (59, .jal .x1 "rlp_content_to_u64_strict"),
    (65, .jal .x1 "rlp_walk_next"),
    (72, .jal .x1 "rlp_content_to_u256_be_strict"),
    (77, .jal .x1 "rlp_walk_next"),
    (84, .jal .x1 "rlp_content_to_u256_be_strict") ]

def txLegacyExtractSignatureFunction : String :=
  "tx_legacy_extract_signature:\n" ++ emitProgramR txLegacyExtractSignature_prog txLegacyExtractSignature_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txLegacyExtractSignature_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txLegacyExtractSignatureFunction_eq_prog :
    txLegacyExtractSignatureFunction = "tx_legacy_extract_signature:\n" ++ emitProgramR txLegacyExtractSignature_prog txLegacyExtractSignature_relocs := rfl

#guard txLegacyExtractSignatureFunction.startsWith "tx_legacy_extract_signature:\n"
#guard txLegacyExtractSignature_prog.length = 102
/-- `zisk_tx_legacy_extract_signature`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : tx_rlp_len
      bytes  8..   : tx_rlp
    Output layout (72 bytes):
      bytes  0.. 8 : status
      bytes  8..16 : v
      bytes 16..48 : r (32 B BE)
      bytes 48..80 : s (32 B BE) -- truncated at 256 B cap is fine -/
def ziskTxLegacyExtractSignaturePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # tx_rlp_len\n" ++
  "  addi a0, a5, 16             # tx_rlp ptr\n" ++
  "  li a2, 0xa0010008           # v out\n" ++
  "  li a3, 0xa0010010           # r out (32 B)\n" ++
  "  li a4, 0xa0010030           # s out (32 B)\n" ++
  "  jal ra, tx_legacy_extract_signature\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ltlxs_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  txLegacyExtractSignatureFunction ++ "\n" ++
  ".Ltlxs_pdone:"

def ziskTxLegacyExtractSignatureDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "tlxs_offset:\n" ++
  "  .zero 8\n" ++
  "tlxs_length:\n" ++
  "  .zero 8"


/-! ## tx_eip1559_extract_signature -- PR-K139

    Extract `(y_parity, r, s)` from the inner RLP of an EIP-1559
    (type-2) transaction:

      inner = rlp([chain_id, nonce,
                   max_priority_fee_per_gas, max_fee_per_gas,
                   gas_limit, to, value, data, access_list,
                   y_parity, r, s])

    The caller is expected to have stripped the leading `0x02`
    type byte (matching PR-K41 `tx_eip1559_decode`'s convention),
    so `a0` points at the inner list's RLP prefix.

    Output convention (mirrors K138 `tx_legacy_extract_signature`):
      * y_parity: u64 (0 or 1; not the legacy `v` byte — no
        EIP-155 split needed because chain_id already lives in
        field 0).
      * r, s: 32-byte right-aligned, zero-padded big-endian
        buffers — the canonical signature scalars consumed by
        `zkvm_secp256k1_ecrecover`.

    Companion in the sender-recovery pipeline to K138
    (legacy), with EIP-2930 / EIP-4844 / EIP-7702 variants
    landing in follow-up PRs (same shape, different field
    indices).

    Composes:
      - RlpWalk cursor helpers across fields 9, 10, 11
      - canonical content decoders for y_parity/r/s

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : y_parity u64 out ptr
      a3 (input)  : r 32-byte BE out ptr
      a4 (input)  : s 32-byte BE out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fields 9/10/11 missing
        2 : y_parity > 8 bytes or r/s > 32 bytes -/
def txEip1559ExtractSignature_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_eip1559_extract_signature + 68)),
    .BNE .x12 .x0 (brOff (GuestAddrs.tx_eip1559_extract_signature + 408) (GuestAddrs.tx_eip1559_extract_signature + 72)),
    .MV .x21 .x10,
    .MV .x22 .x11,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_extract_signature + 92)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip1559_extract_signature + 408) (GuestAddrs.tx_eip1559_extract_signature + 96)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_extract_signature + 112)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip1559_extract_signature + 408) (GuestAddrs.tx_eip1559_extract_signature + 116)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_extract_signature + 132)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip1559_extract_signature + 408) (GuestAddrs.tx_eip1559_extract_signature + 136)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_extract_signature + 152)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip1559_extract_signature + 408) (GuestAddrs.tx_eip1559_extract_signature + 156)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_extract_signature + 172)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip1559_extract_signature + 408) (GuestAddrs.tx_eip1559_extract_signature + 176)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_extract_signature + 192)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip1559_extract_signature + 408) (GuestAddrs.tx_eip1559_extract_signature + 196)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_extract_signature + 212)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip1559_extract_signature + 408) (GuestAddrs.tx_eip1559_extract_signature + 216)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_extract_signature + 232)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip1559_extract_signature + 408) (GuestAddrs.tx_eip1559_extract_signature + 236)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_extract_signature + 252)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip1559_extract_signature + 408) (GuestAddrs.tx_eip1559_extract_signature + 256)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_extract_signature + 272)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip1559_extract_signature + 408) (GuestAddrs.tx_eip1559_extract_signature + 276)),
    .SUB .x5 .x10 .x12,
    .MV .x23 .x10,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.tx_eip1559_extract_signature + 296)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip1559_extract_signature + 416) (GuestAddrs.tx_eip1559_extract_signature + 300)),
    .SD .x18 .x10 (0 : BitVec 12),
    .MV .x21 .x23,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_extract_signature + 320)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip1559_extract_signature + 408) (GuestAddrs.tx_eip1559_extract_signature + 324)),
    .SUB .x5 .x10 .x12,
    .MV .x23 .x10,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_eip1559_extract_signature + 348)),
    .BNE .x10 .x0 (brOff (GuestAddrs.tx_eip1559_extract_signature + 416) (GuestAddrs.tx_eip1559_extract_signature + 352)),
    .MV .x21 .x23,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_extract_signature + 368)),
    .BNE .x11 .x0 (36 : BitVec 13),
    .SUB .x5 .x10 .x12,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_eip1559_extract_signature + 392)),
    .BNE .x10 .x0 (20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txEip1559ExtractSignature_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txEip1559ExtractSignature_relocs : RelocTable :=
  [ (17, .jal .x1 "rlp_walk_init"),
    (23, .jal .x1 "rlp_walk_next"),
    (28, .jal .x1 "rlp_walk_next"),
    (33, .jal .x1 "rlp_walk_next"),
    (38, .jal .x1 "rlp_walk_next"),
    (43, .jal .x1 "rlp_walk_next"),
    (48, .jal .x1 "rlp_walk_next"),
    (53, .jal .x1 "rlp_walk_next"),
    (58, .jal .x1 "rlp_walk_next"),
    (63, .jal .x1 "rlp_walk_next"),
    (68, .jal .x1 "rlp_walk_next"),
    (74, .jal .x1 "rlp_content_to_u64_strict"),
    (80, .jal .x1 "rlp_walk_next"),
    (87, .jal .x1 "rlp_content_to_u256_be_strict"),
    (92, .jal .x1 "rlp_walk_next"),
    (98, .jal .x1 "rlp_content_to_u256_be_strict") ]

def txEip1559ExtractSignatureFunction : String :=
  "tx_eip1559_extract_signature:\n" ++ emitProgramR txEip1559ExtractSignature_prog txEip1559ExtractSignature_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txEip1559ExtractSignature_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txEip1559ExtractSignatureFunction_eq_prog :
    txEip1559ExtractSignatureFunction = "tx_eip1559_extract_signature:\n" ++ emitProgramR txEip1559ExtractSignature_prog txEip1559ExtractSignature_relocs := rfl

#guard txEip1559ExtractSignatureFunction.startsWith "tx_eip1559_extract_signature:\n"
#guard txEip1559ExtractSignature_prog.length = 116
/-- `zisk_tx_eip1559_extract_signature`: probe BuildUnit.
    Input layout (after the host header):
      bytes  0.. 8 : inner_rlp_len
      bytes  8..   : inner_rlp (no leading 0x02 type byte)
    Output layout (80 bytes):
      bytes  0.. 8 : status
      bytes  8..16 : y_parity (u64)
      bytes 16..48 : r (32 B BE)
      bytes 48..80 : s (32 B BE) -/
def ziskTxEip1559ExtractSignaturePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # inner_rlp_len\n" ++
  "  addi a0, a5, 16             # inner_rlp ptr\n" ++
  "  li a2, 0xa0010008           # y_parity out\n" ++
  "  li a3, 0xa0010010           # r out (32 B)\n" ++
  "  li a4, 0xa0010030           # s out (32 B)\n" ++
  "  jal ra, tx_eip1559_extract_signature\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ltxes_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  txEip1559ExtractSignatureFunction ++ "\n" ++
  ".Ltxes_pdone:"

def ziskTxEip1559ExtractSignatureDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "txes_offset:\n" ++
  "  .zero 8\n" ++
  "txes_length:\n" ++
  "  .zero 8"


/-! ## tx_eip2930_extract_signature -- PR-K140

    Extract `(y_parity, r, s)` from the inner RLP body of an
    EIP-2930 (type-1) access-list transaction:

      inner = rlp([chain_id, nonce, gas_price, gas_limit,
                   to, value, data, access_list,
                   y_parity, r, s])

    EIP-2930 is structurally simpler than EIP-1559 (a single
    `gas_price` field instead of the
    `(max_priority_fee_per_gas, max_fee_per_gas)` pair), so the
    signature triple sits at fields 8/9/10 of an 11-field list.

    Caller is expected to have stripped the leading `0x01` type
    byte (matching PR-K42 `tx_eip2930_decode`'s convention), so
    `a0` points at the inner list's RLP prefix.

    Companion in the sender-recovery pipeline to PR-K138
    (legacy) and PR-K139 (EIP-1559); EIP-4844 / EIP-7702 variants
    land in follow-up PRs.

    Composes:
      - RlpWalk cursor helpers across fields 8, 9, 10
      - canonical content decoders for y_parity/r/s

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : y_parity u64 out ptr
      a3 (input)  : r 32-byte BE out ptr
      a4 (input)  : s 32-byte BE out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fields 8/9/10 missing
        2 : y_parity > 8 bytes or r/s > 32 bytes -/
def txEip2930ExtractSignature_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_eip2930_extract_signature + 68)),
    .BNE .x12 .x0 (brOff (GuestAddrs.tx_eip2930_extract_signature + 388) (GuestAddrs.tx_eip2930_extract_signature + 72)),
    .MV .x21 .x10,
    .MV .x22 .x11,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_extract_signature + 92)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip2930_extract_signature + 388) (GuestAddrs.tx_eip2930_extract_signature + 96)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_extract_signature + 112)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip2930_extract_signature + 388) (GuestAddrs.tx_eip2930_extract_signature + 116)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_extract_signature + 132)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip2930_extract_signature + 388) (GuestAddrs.tx_eip2930_extract_signature + 136)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_extract_signature + 152)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip2930_extract_signature + 388) (GuestAddrs.tx_eip2930_extract_signature + 156)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_extract_signature + 172)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip2930_extract_signature + 388) (GuestAddrs.tx_eip2930_extract_signature + 176)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_extract_signature + 192)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip2930_extract_signature + 388) (GuestAddrs.tx_eip2930_extract_signature + 196)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_extract_signature + 212)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip2930_extract_signature + 388) (GuestAddrs.tx_eip2930_extract_signature + 216)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_extract_signature + 232)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip2930_extract_signature + 388) (GuestAddrs.tx_eip2930_extract_signature + 236)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_extract_signature + 252)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip2930_extract_signature + 388) (GuestAddrs.tx_eip2930_extract_signature + 256)),
    .SUB .x5 .x10 .x12,
    .MV .x23 .x10,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.tx_eip2930_extract_signature + 276)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip2930_extract_signature + 396) (GuestAddrs.tx_eip2930_extract_signature + 280)),
    .SD .x18 .x10 (0 : BitVec 12),
    .MV .x21 .x23,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_extract_signature + 300)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip2930_extract_signature + 388) (GuestAddrs.tx_eip2930_extract_signature + 304)),
    .SUB .x5 .x10 .x12,
    .MV .x23 .x10,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_eip2930_extract_signature + 328)),
    .BNE .x10 .x0 (brOff (GuestAddrs.tx_eip2930_extract_signature + 396) (GuestAddrs.tx_eip2930_extract_signature + 332)),
    .MV .x21 .x23,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_extract_signature + 348)),
    .BNE .x11 .x0 (36 : BitVec 13),
    .SUB .x5 .x10 .x12,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_eip2930_extract_signature + 372)),
    .BNE .x10 .x0 (20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txEip2930ExtractSignature_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txEip2930ExtractSignature_relocs : RelocTable :=
  [ (17, .jal .x1 "rlp_walk_init"),
    (23, .jal .x1 "rlp_walk_next"),
    (28, .jal .x1 "rlp_walk_next"),
    (33, .jal .x1 "rlp_walk_next"),
    (38, .jal .x1 "rlp_walk_next"),
    (43, .jal .x1 "rlp_walk_next"),
    (48, .jal .x1 "rlp_walk_next"),
    (53, .jal .x1 "rlp_walk_next"),
    (58, .jal .x1 "rlp_walk_next"),
    (63, .jal .x1 "rlp_walk_next"),
    (69, .jal .x1 "rlp_content_to_u64_strict"),
    (75, .jal .x1 "rlp_walk_next"),
    (82, .jal .x1 "rlp_content_to_u256_be_strict"),
    (87, .jal .x1 "rlp_walk_next"),
    (93, .jal .x1 "rlp_content_to_u256_be_strict") ]

def txEip2930ExtractSignatureFunction : String :=
  "tx_eip2930_extract_signature:\n" ++ emitProgramR txEip2930ExtractSignature_prog txEip2930ExtractSignature_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txEip2930ExtractSignature_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txEip2930ExtractSignatureFunction_eq_prog :
    txEip2930ExtractSignatureFunction = "tx_eip2930_extract_signature:\n" ++ emitProgramR txEip2930ExtractSignature_prog txEip2930ExtractSignature_relocs := rfl

#guard txEip2930ExtractSignatureFunction.startsWith "tx_eip2930_extract_signature:\n"
#guard txEip2930ExtractSignature_prog.length = 111
/-- `zisk_tx_eip2930_extract_signature`: probe BuildUnit.
    Input layout (after the host header):
      bytes  0.. 8 : inner_rlp_len
      bytes  8..   : inner_rlp (no leading 0x01 type byte)
    Output layout (80 bytes): status, y_parity, r (32 B), s (32 B). -/
def ziskTxEip2930ExtractSignaturePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # inner_rlp_len\n" ++
  "  addi a0, a5, 16             # inner_rlp ptr\n" ++
  "  li a2, 0xa0010008           # y_parity out\n" ++
  "  li a3, 0xa0010010           # r out (32 B)\n" ++
  "  li a4, 0xa0010030           # s out (32 B)\n" ++
  "  jal ra, tx_eip2930_extract_signature\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lt29es_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  txEip2930ExtractSignatureFunction ++ "\n" ++
  ".Lt29es_pdone:"

def ziskTxEip2930ExtractSignatureDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "t29es_offset:\n" ++
  "  .zero 8\n" ++
  "t29es_length:\n" ++
  "  .zero 8"


/-! ## tx_eip4844_extract_signature -- PR-K141

    Extract `(y_parity, r, s)` from the inner RLP body of an
    EIP-4844 (type-3) blob transaction:

      inner = rlp([chain_id, nonce,
                   max_priority_fee_per_gas, max_fee_per_gas,
                   gas_limit, to, value, data,
                   access_list,
                   max_fee_per_blob_gas, blob_versioned_hashes,
                   y_parity, r, s])

    Compared to EIP-1559 (12 fields), EIP-4844 inserts
    `max_fee_per_blob_gas` and `blob_versioned_hashes` between
    `access_list` and `y_parity`, so the signature triple sits at
    fields 11/12/13 of a 14-field list.

    Caller is expected to have stripped the leading 0x03 type byte
    (matching PR-K45 `tx_eip4844_decode`'s convention).

    Companion in the sender-recovery pipeline to PR-K138 (legacy),
    PR-K139 (EIP-1559), and PR-K140 (EIP-2930); EIP-7702 variant
    lands in a follow-up PR.

    Composes:
      - RlpWalk cursor helpers across fields 11, 12, 13
      - canonical content decoders for y_parity/r/s

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : y_parity u64 out ptr
      a3 (input)  : r 32-byte BE out ptr
      a4 (input)  : s 32-byte BE out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fields 11/12/13 missing
        2 : y_parity > 8 bytes or r/s > 32 bytes -/
def txEip4844ExtractSignature_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_eip4844_extract_signature + 68)),
    .BNE .x12 .x0 (brOff (GuestAddrs.tx_eip4844_extract_signature + 448) (GuestAddrs.tx_eip4844_extract_signature + 72)),
    .MV .x21 .x10,
    .MV .x22 .x11,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_extract_signature + 92)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip4844_extract_signature + 448) (GuestAddrs.tx_eip4844_extract_signature + 96)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_extract_signature + 112)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip4844_extract_signature + 448) (GuestAddrs.tx_eip4844_extract_signature + 116)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_extract_signature + 132)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip4844_extract_signature + 448) (GuestAddrs.tx_eip4844_extract_signature + 136)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_extract_signature + 152)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip4844_extract_signature + 448) (GuestAddrs.tx_eip4844_extract_signature + 156)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_extract_signature + 172)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip4844_extract_signature + 448) (GuestAddrs.tx_eip4844_extract_signature + 176)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_extract_signature + 192)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip4844_extract_signature + 448) (GuestAddrs.tx_eip4844_extract_signature + 196)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_extract_signature + 212)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip4844_extract_signature + 448) (GuestAddrs.tx_eip4844_extract_signature + 216)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_extract_signature + 232)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip4844_extract_signature + 448) (GuestAddrs.tx_eip4844_extract_signature + 236)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_extract_signature + 252)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip4844_extract_signature + 448) (GuestAddrs.tx_eip4844_extract_signature + 256)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_extract_signature + 272)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip4844_extract_signature + 448) (GuestAddrs.tx_eip4844_extract_signature + 276)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_extract_signature + 292)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip4844_extract_signature + 448) (GuestAddrs.tx_eip4844_extract_signature + 296)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_extract_signature + 312)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip4844_extract_signature + 448) (GuestAddrs.tx_eip4844_extract_signature + 316)),
    .SUB .x5 .x10 .x12,
    .MV .x23 .x10,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.tx_eip4844_extract_signature + 336)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip4844_extract_signature + 456) (GuestAddrs.tx_eip4844_extract_signature + 340)),
    .SD .x18 .x10 (0 : BitVec 12),
    .MV .x21 .x23,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_extract_signature + 360)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip4844_extract_signature + 448) (GuestAddrs.tx_eip4844_extract_signature + 364)),
    .SUB .x5 .x10 .x12,
    .MV .x23 .x10,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_eip4844_extract_signature + 388)),
    .BNE .x10 .x0 (brOff (GuestAddrs.tx_eip4844_extract_signature + 456) (GuestAddrs.tx_eip4844_extract_signature + 392)),
    .MV .x21 .x23,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_extract_signature + 408)),
    .BNE .x11 .x0 (36 : BitVec 13),
    .SUB .x5 .x10 .x12,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_eip4844_extract_signature + 432)),
    .BNE .x10 .x0 (20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txEip4844ExtractSignature_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txEip4844ExtractSignature_relocs : RelocTable :=
  [ (17, .jal .x1 "rlp_walk_init"),
    (23, .jal .x1 "rlp_walk_next"),
    (28, .jal .x1 "rlp_walk_next"),
    (33, .jal .x1 "rlp_walk_next"),
    (38, .jal .x1 "rlp_walk_next"),
    (43, .jal .x1 "rlp_walk_next"),
    (48, .jal .x1 "rlp_walk_next"),
    (53, .jal .x1 "rlp_walk_next"),
    (58, .jal .x1 "rlp_walk_next"),
    (63, .jal .x1 "rlp_walk_next"),
    (68, .jal .x1 "rlp_walk_next"),
    (73, .jal .x1 "rlp_walk_next"),
    (78, .jal .x1 "rlp_walk_next"),
    (84, .jal .x1 "rlp_content_to_u64_strict"),
    (90, .jal .x1 "rlp_walk_next"),
    (97, .jal .x1 "rlp_content_to_u256_be_strict"),
    (102, .jal .x1 "rlp_walk_next"),
    (108, .jal .x1 "rlp_content_to_u256_be_strict") ]

def txEip4844ExtractSignatureFunction : String :=
  "tx_eip4844_extract_signature:\n" ++ emitProgramR txEip4844ExtractSignature_prog txEip4844ExtractSignature_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txEip4844ExtractSignature_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txEip4844ExtractSignatureFunction_eq_prog :
    txEip4844ExtractSignatureFunction = "tx_eip4844_extract_signature:\n" ++ emitProgramR txEip4844ExtractSignature_prog txEip4844ExtractSignature_relocs := rfl

#guard txEip4844ExtractSignatureFunction.startsWith "tx_eip4844_extract_signature:\n"
#guard txEip4844ExtractSignature_prog.length = 126
/-- `zisk_tx_eip4844_extract_signature`: probe BuildUnit. -/
def ziskTxEip4844ExtractSignaturePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # inner_rlp_len\n" ++
  "  addi a0, a5, 16             # inner_rlp ptr\n" ++
  "  li a2, 0xa0010008           # y_parity out\n" ++
  "  li a3, 0xa0010010           # r out (32 B)\n" ++
  "  li a4, 0xa0010030           # s out (32 B)\n" ++
  "  jal ra, tx_eip4844_extract_signature\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lt44es_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  txEip4844ExtractSignatureFunction ++ "\n" ++
  ".Lt44es_pdone:"

def ziskTxEip4844ExtractSignatureDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "t44es_offset:\n" ++
  "  .zero 8\n" ++
  "t44es_length:\n" ++
  "  .zero 8"


/-! ## tx_eip7702_extract_signature -- PR-K142

    Extract `(y_parity, r, s)` from the inner RLP body of an
    EIP-7702 (type-4) set-code transaction:

      inner = rlp([chain_id, nonce,
                   max_priority_fee_per_gas, max_fee_per_gas,
                   gas_limit, to, value, data,
                   access_list, authorization_list,
                   y_parity, r, s])

    Compared to EIP-1559 (12 fields), EIP-7702 inserts a single
    `authorization_list` field between `access_list` and
    `y_parity`, so the outer-transaction signature triple sits at
    fields 10/11/12 of a 13-field list.

    Note: EIP-7702 carries TWO layers of signatures — the outer
    transaction signature (this PR's target) AND a per-entry
    `(y_parity, r, s)` inside each authorization tuple in
    `authorization_list`. K142 only handles the outer triple.
    Sub-extracting per-authorization signatures lands in a
    follow-up PR (one per authorization).

    Caller is expected to have stripped the leading 0x04 type byte
    (matching PR-K44 `tx_eip7702_decode`'s convention).

    Completes the four-EIP sig-extractor family:
      * PR-K138 legacy
      * PR-K139 EIP-1559
      * PR-K140 EIP-2930
      * PR-K141 EIP-4844
      * PR-K142 EIP-7702

    Composes:
      - RlpWalk cursor helpers across fields 10, 11, 12
      - canonical content decoders for y_parity/r/s

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : y_parity u64 out ptr
      a3 (input)  : r 32-byte BE out ptr
      a4 (input)  : s 32-byte BE out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fields 10/11/12 missing
        2 : y_parity > 8 bytes or r/s > 32 bytes -/
def txEip7702ExtractSignature_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_eip7702_extract_signature + 68)),
    .BNE .x12 .x0 (brOff (GuestAddrs.tx_eip7702_extract_signature + 428) (GuestAddrs.tx_eip7702_extract_signature + 72)),
    .MV .x21 .x10,
    .MV .x22 .x11,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_extract_signature + 92)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip7702_extract_signature + 428) (GuestAddrs.tx_eip7702_extract_signature + 96)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_extract_signature + 112)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip7702_extract_signature + 428) (GuestAddrs.tx_eip7702_extract_signature + 116)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_extract_signature + 132)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip7702_extract_signature + 428) (GuestAddrs.tx_eip7702_extract_signature + 136)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_extract_signature + 152)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip7702_extract_signature + 428) (GuestAddrs.tx_eip7702_extract_signature + 156)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_extract_signature + 172)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip7702_extract_signature + 428) (GuestAddrs.tx_eip7702_extract_signature + 176)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_extract_signature + 192)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip7702_extract_signature + 428) (GuestAddrs.tx_eip7702_extract_signature + 196)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_extract_signature + 212)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip7702_extract_signature + 428) (GuestAddrs.tx_eip7702_extract_signature + 216)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_extract_signature + 232)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip7702_extract_signature + 428) (GuestAddrs.tx_eip7702_extract_signature + 236)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_extract_signature + 252)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip7702_extract_signature + 428) (GuestAddrs.tx_eip7702_extract_signature + 256)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_extract_signature + 272)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip7702_extract_signature + 428) (GuestAddrs.tx_eip7702_extract_signature + 276)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_extract_signature + 292)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip7702_extract_signature + 428) (GuestAddrs.tx_eip7702_extract_signature + 296)),
    .SUB .x5 .x10 .x12,
    .MV .x23 .x10,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.tx_eip7702_extract_signature + 316)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip7702_extract_signature + 436) (GuestAddrs.tx_eip7702_extract_signature + 320)),
    .SD .x18 .x10 (0 : BitVec 12),
    .MV .x21 .x23,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_extract_signature + 340)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_eip7702_extract_signature + 428) (GuestAddrs.tx_eip7702_extract_signature + 344)),
    .SUB .x5 .x10 .x12,
    .MV .x23 .x10,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_eip7702_extract_signature + 368)),
    .BNE .x10 .x0 (brOff (GuestAddrs.tx_eip7702_extract_signature + 436) (GuestAddrs.tx_eip7702_extract_signature + 372)),
    .MV .x21 .x23,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_extract_signature + 388)),
    .BNE .x11 .x0 (36 : BitVec 13),
    .SUB .x5 .x10 .x12,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_eip7702_extract_signature + 412)),
    .BNE .x10 .x0 (20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txEip7702ExtractSignature_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txEip7702ExtractSignature_relocs : RelocTable :=
  [ (17, .jal .x1 "rlp_walk_init"),
    (23, .jal .x1 "rlp_walk_next"),
    (28, .jal .x1 "rlp_walk_next"),
    (33, .jal .x1 "rlp_walk_next"),
    (38, .jal .x1 "rlp_walk_next"),
    (43, .jal .x1 "rlp_walk_next"),
    (48, .jal .x1 "rlp_walk_next"),
    (53, .jal .x1 "rlp_walk_next"),
    (58, .jal .x1 "rlp_walk_next"),
    (63, .jal .x1 "rlp_walk_next"),
    (68, .jal .x1 "rlp_walk_next"),
    (73, .jal .x1 "rlp_walk_next"),
    (79, .jal .x1 "rlp_content_to_u64_strict"),
    (85, .jal .x1 "rlp_walk_next"),
    (92, .jal .x1 "rlp_content_to_u256_be_strict"),
    (97, .jal .x1 "rlp_walk_next"),
    (103, .jal .x1 "rlp_content_to_u256_be_strict") ]

def txEip7702ExtractSignatureFunction : String :=
  "tx_eip7702_extract_signature:\n" ++ emitProgramR txEip7702ExtractSignature_prog txEip7702ExtractSignature_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txEip7702ExtractSignature_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txEip7702ExtractSignatureFunction_eq_prog :
    txEip7702ExtractSignatureFunction = "tx_eip7702_extract_signature:\n" ++ emitProgramR txEip7702ExtractSignature_prog txEip7702ExtractSignature_relocs := rfl

#guard txEip7702ExtractSignatureFunction.startsWith "tx_eip7702_extract_signature:\n"
#guard txEip7702ExtractSignature_prog.length = 121
/-- `zisk_tx_eip7702_extract_signature`: probe BuildUnit. -/
def ziskTxEip7702ExtractSignaturePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # inner_rlp_len\n" ++
  "  addi a0, a5, 16             # inner_rlp ptr\n" ++
  "  li a2, 0xa0010008           # y_parity out\n" ++
  "  li a3, 0xa0010010           # r out (32 B)\n" ++
  "  li a4, 0xa0010030           # s out (32 B)\n" ++
  "  jal ra, tx_eip7702_extract_signature\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lt77es_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  txEip7702ExtractSignatureFunction ++ "\n" ++
  ".Lt77es_pdone:"

def ziskTxEip7702ExtractSignatureDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "t77es_offset:\n" ++
  "  .zero 8\n" ++
  "t77es_length:\n" ++
  "  .zero 8"


/-! ## eip7702_authorization_extract_signature -- PR-K143

    Extract `(y_parity, r, s)` from a single EIP-7702
    *authorization tuple*. Each entry inside an EIP-7702
    transaction's `authorization_list` is a 6-field RLP list:

      authorization = rlp([chain_id, address, nonce,
                           y_parity, r, s])

    so the signature triple sits at fields 3/4/5 of a 6-field
    list — one field earlier on each axis than the legacy tx
    layout because there is no `data`, `to`, or `access_list`
    field in an authorization tuple.

    Companion to PR-K142 `tx_eip7702_extract_signature`, which
    extracts the *outer* transaction signature. EIP-7702 carries
    two layers of signatures:

      * Outer transaction sig (K142): authorises the whole tx.
      * Per-authorization sig (K143): authorises a single
        `(chain_id, address, nonce)` delegation to be applied
        before the tx body runs.

    The full sender-recovery pipeline for an EIP-7702 delegation:
      1. K143 extracts (y_parity, r, s) from the authorization
         tuple.
      2. tx_eip7702_authorization_signing_hash (future) =
         keccak256(MAGIC || rlp([chain_id, address, nonce]))
         where `MAGIC = 0x05` per the EIP.
      3. `zkvm_secp256k1_ecrecover` → 64-byte pubkey of the
         **delegator** (not the tx sender).
      4. K99 `address_from_pubkey` → 20-byte delegator address.

    The caller is responsible for first extracting the i-th authorization tuple
    from `authorization_list`; K143 operates on the already-
    extracted tuple bytes.

    Composes:
      - RlpWalk cursor helpers across fields 3, 4, 5
      - canonical content decoders for y_parity/r/s

    Calling convention:
      a0 (input)  : authorization_tuple_rlp ptr
      a1 (input)  : authorization_tuple_rlp byte length
      a2 (input)  : y_parity u64 out ptr
      a3 (input)  : r 32-byte BE out ptr
      a4 (input)  : s 32-byte BE out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fields 3/4/5 missing
        2 : y_parity > 8 bytes or r/s > 32 bytes -/
def eip7702AuthorizationExtractSignature_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.eip7702_authorization_extract_signature + 68)),
    .BNE .x12 .x0 (brOff (GuestAddrs.eip7702_authorization_extract_signature + 288) (GuestAddrs.eip7702_authorization_extract_signature + 72)),
    .MV .x21 .x10,
    .MV .x22 .x11,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.eip7702_authorization_extract_signature + 92)),
    .BNE .x11 .x0 (brOff (GuestAddrs.eip7702_authorization_extract_signature + 288) (GuestAddrs.eip7702_authorization_extract_signature + 96)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.eip7702_authorization_extract_signature + 112)),
    .BNE .x11 .x0 (brOff (GuestAddrs.eip7702_authorization_extract_signature + 288) (GuestAddrs.eip7702_authorization_extract_signature + 116)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.eip7702_authorization_extract_signature + 132)),
    .BNE .x11 .x0 (brOff (GuestAddrs.eip7702_authorization_extract_signature + 288) (GuestAddrs.eip7702_authorization_extract_signature + 136)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.eip7702_authorization_extract_signature + 152)),
    .BNE .x11 .x0 (brOff (GuestAddrs.eip7702_authorization_extract_signature + 288) (GuestAddrs.eip7702_authorization_extract_signature + 156)),
    .SUB .x5 .x10 .x12,
    .MV .x23 .x10,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.eip7702_authorization_extract_signature + 176)),
    .BNE .x11 .x0 (brOff (GuestAddrs.eip7702_authorization_extract_signature + 296) (GuestAddrs.eip7702_authorization_extract_signature + 180)),
    .SD .x18 .x10 (0 : BitVec 12),
    .MV .x21 .x23,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.eip7702_authorization_extract_signature + 200)),
    .BNE .x11 .x0 (brOff (GuestAddrs.eip7702_authorization_extract_signature + 288) (GuestAddrs.eip7702_authorization_extract_signature + 204)),
    .SUB .x5 .x10 .x12,
    .MV .x23 .x10,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.eip7702_authorization_extract_signature + 228)),
    .BNE .x10 .x0 (brOff (GuestAddrs.eip7702_authorization_extract_signature + 296) (GuestAddrs.eip7702_authorization_extract_signature + 232)),
    .MV .x21 .x23,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.eip7702_authorization_extract_signature + 248)),
    .BNE .x11 .x0 (36 : BitVec 13),
    .SUB .x5 .x10 .x12,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.eip7702_authorization_extract_signature + 272)),
    .BNE .x10 .x0 (20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `eip7702AuthorizationExtractSignature_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def eip7702AuthorizationExtractSignature_relocs : RelocTable :=
  [ (17, .jal .x1 "rlp_walk_init"),
    (23, .jal .x1 "rlp_walk_next"),
    (28, .jal .x1 "rlp_walk_next"),
    (33, .jal .x1 "rlp_walk_next"),
    (38, .jal .x1 "rlp_walk_next"),
    (44, .jal .x1 "rlp_content_to_u64_strict"),
    (50, .jal .x1 "rlp_walk_next"),
    (57, .jal .x1 "rlp_content_to_u256_be_strict"),
    (62, .jal .x1 "rlp_walk_next"),
    (68, .jal .x1 "rlp_content_to_u256_be_strict") ]

def eip7702AuthorizationExtractSignatureFunction : String :=
  "eip7702_authorization_extract_signature:\n" ++ emitProgramR eip7702AuthorizationExtractSignature_prog eip7702AuthorizationExtractSignature_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `eip7702AuthorizationExtractSignature_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem eip7702AuthorizationExtractSignatureFunction_eq_prog :
    eip7702AuthorizationExtractSignatureFunction = "eip7702_authorization_extract_signature:\n" ++ emitProgramR eip7702AuthorizationExtractSignature_prog eip7702AuthorizationExtractSignature_relocs := rfl

#guard eip7702AuthorizationExtractSignatureFunction.startsWith "eip7702_authorization_extract_signature:\n"
#guard eip7702AuthorizationExtractSignature_prog.length = 86
/-- `zisk_eip7702_authorization_extract_signature`: probe BuildUnit.
    Input layout (after the host header):
      bytes  0.. 8 : tuple_rlp_len
      bytes  8..   : tuple_rlp -/
def ziskEip7702AuthorizationExtractSignaturePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # tuple_rlp_len\n" ++
  "  addi a0, a5, 16             # tuple_rlp ptr\n" ++
  "  li a2, 0xa0010008           # y_parity out\n" ++
  "  li a3, 0xa0010010           # r out (32 B)\n" ++
  "  li a4, 0xa0010030           # s out (32 B)\n" ++
  "  jal ra, eip7702_authorization_extract_signature\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lta77es_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  eip7702AuthorizationExtractSignatureFunction ++ "\n" ++
  ".Lta77es_pdone:"

def ziskEip7702AuthorizationExtractSignatureDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ta77es_offset:\n" ++
  "  .zero 8\n" ++
  "ta77es_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
