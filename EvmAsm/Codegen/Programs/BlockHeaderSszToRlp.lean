/-
  EvmAsm.Codegen.Programs.BlockHeaderSszToRlp

  block_header_ssz_to_rlp (bead evm-asm-fhsxz.2.4.1): re-encode an Amsterdam
  block header from its SSZ ExecutionPayload (plus four roots not carried in
  the payload) into the canonical RLP the consensus block hash is taken over.
  This is the prerequisite for the Step-2 verdict: validate_header_rlp_pair
  needs the current block's header as RLP, and the block-hash linkage is
  keccak256(rlp(header)).

  The 23 Amsterdam header fields (execution-specs amsterdam/blocks.py), in RLP
  order, with their source:
    parent_hash, ommers_hash(=EMPTY_OMMER_HASH const), coinbase, state_root,
    transactions_root(INPUT), receipt_root, bloom, difficulty(=0),
    number, gas_limit, gas_used, timestamp, extra_data, prev_randao,
    nonce(=0 Bytes8), base_fee_per_gas, withdrawals_root(INPUT),
    blob_gas_used, excess_blob_gas, parent_beacon_block_root(INPUT),
    requests_hash(INPUT), block_access_list_hash(INPUT), slot_number.
  transactions_root / withdrawals_root / parent_beacon_block_root /
  requests_hash / block_access_list_hash are NOT in the fixed SSZ payload (the
  payload carries the lists/bytes; commitments are computed separately) ->
  passed in by the caller.

  No-misaligned invariant: the payload's u64 fields sit at byte offsets ≡4 mod
  8, so a plain `ld` would trap on verified RV64. We read every integer field
  byte-wise (LE) and reverse to big-endian via `bhr_rev_le_be`, then
  rlp_encode_uint_be (which strips leading zeros to the minimal RLP form);
  byte-string fields go through rlp_encode_bytes (byte-wise). All scratch
  stores are u64/aligned.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

-- (HashBridge provides zkvm_keccak256, used by the probe to hash the
-- re-encoded header into the block hash, since the 627-byte RLP exceeds
-- ziskemu's 256-byte OUTPUT capture.)

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bhr_rev_le_be -- reverse `len` little-endian bytes into big-endian.
    a0 = src ptr, a1 = len, a2 = dst ptr. Leaf (LBU/SB only). -/
def bhrRevLeBe_prog : Program :=
  [ .ADD .x5 .x10 .x11,
    .MV .x6 .x12,
    .MV .x7 .x11,
    .BEQ .x7 .x0 (28 : BitVec 13),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .LBU .x28 .x5 (0 : BitVec 12),
    .SB .x6 .x28 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bhrRevLeBeFunction : String :=
  "bhr_rev_le_be:\n" ++ emitProgram bhrRevLeBe_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bhrRevLeBe_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bhrRevLeBeFunction_eq_prog :
    bhrRevLeBeFunction = "bhr_rev_le_be:\n" ++ emitProgram bhrRevLeBe_prog := rfl

#guard bhrRevLeBeFunction.startsWith "bhr_rev_le_be:\n"
/-- `block_header_ssz_to_rlp`.
    a0 = SSZ ExecutionPayload ptr     a1 = transactions_root ptr (32B)
    a2 = withdrawals_root ptr (32B)   a3 = parent_beacon_block_root ptr (32B)
    a4 = requests_hash ptr (32B)      a5 = out RLP buffer ptr
    a6 = u64 out length ptr           a7 = block_access_list_hash ptr (32B)
    a0 (output) = 0. -/
def blockHeaderSszToRlp_prog : Program :=
  [ .ADDI .x2 .x2 (-96 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .SD .x2 .x24 (72 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .MV .x24 .x17,
    .LI .x23 (0 : Word),
    .ADDI .x10 .x8 (0 : BitVec 12),
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 88)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 88)),
    .ADD .x12 .x12 .x23,
    .AUIPC .x13 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 100)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 100)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.block_header_ssz_to_rlp + 108)),
    .AUIPC .x5 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 112)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 112)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x6,
    .AUIPC .x10 (laHi GuestAddrs.bhr_empty_ommers (GuestAddrs.block_header_ssz_to_rlp + 128)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bhr_empty_ommers (GuestAddrs.block_header_ssz_to_rlp + 128)),
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 140)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 140)),
    .ADD .x12 .x12 .x23,
    .AUIPC .x13 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 152)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 152)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.block_header_ssz_to_rlp + 160)),
    .AUIPC .x5 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 164)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 164)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x6,
    .ADDI .x10 .x8 (32 : BitVec 12),
    .LI .x11 (20 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 188)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 188)),
    .ADD .x12 .x12 .x23,
    .AUIPC .x13 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 200)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 200)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.block_header_ssz_to_rlp + 208)),
    .AUIPC .x5 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 212)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 212)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x6,
    .ADDI .x10 .x8 (52 : BitVec 12),
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 236)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 236)),
    .ADD .x12 .x12 .x23,
    .AUIPC .x13 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 248)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 248)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.block_header_ssz_to_rlp + 256)),
    .AUIPC .x5 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 260)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 260)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x6,
    .MV .x10 .x9,
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 284)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 284)),
    .ADD .x12 .x12 .x23,
    .AUIPC .x13 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 296)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 296)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.block_header_ssz_to_rlp + 304)),
    .AUIPC .x5 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 308)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 308)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x6,
    .ADDI .x10 .x8 (84 : BitVec 12),
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 332)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 332)),
    .ADD .x12 .x12 .x23,
    .AUIPC .x13 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 344)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 344)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.block_header_ssz_to_rlp + 352)),
    .AUIPC .x5 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 356)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 356)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x6,
    .ADDI .x10 .x8 (116 : BitVec 12),
    .LI .x11 (256 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 380)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 380)),
    .ADD .x12 .x12 .x23,
    .AUIPC .x13 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 392)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 392)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.block_header_ssz_to_rlp + 400)),
    .AUIPC .x5 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 404)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 404)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x6,
    .AUIPC .x10 (laHi GuestAddrs.bhr_zero8 (GuestAddrs.block_header_ssz_to_rlp + 420)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bhr_zero8 (GuestAddrs.block_header_ssz_to_rlp + 420)),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 432)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 432)),
    .ADD .x12 .x12 .x23,
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_uint_be (GuestAddrs.block_header_ssz_to_rlp + 444)),
    .ADD .x23 .x23 .x10,
    .ADDI .x10 .x8 (404 : BitVec 12),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 460)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 460)),
    .JAL .x1 (jalOff GuestAddrs.bhr_rev_le_be (GuestAddrs.block_header_ssz_to_rlp + 468)),
    .AUIPC .x10 (laHi GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 472)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 472)),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 484)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 484)),
    .ADD .x12 .x12 .x23,
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_uint_be (GuestAddrs.block_header_ssz_to_rlp + 496)),
    .ADD .x23 .x23 .x10,
    .ADDI .x10 .x8 (412 : BitVec 12),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 512)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 512)),
    .JAL .x1 (jalOff GuestAddrs.bhr_rev_le_be (GuestAddrs.block_header_ssz_to_rlp + 520)),
    .AUIPC .x10 (laHi GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 524)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 524)),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 536)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 536)),
    .ADD .x12 .x12 .x23,
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_uint_be (GuestAddrs.block_header_ssz_to_rlp + 548)),
    .ADD .x23 .x23 .x10,
    .ADDI .x10 .x8 (420 : BitVec 12),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 564)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 564)),
    .JAL .x1 (jalOff GuestAddrs.bhr_rev_le_be (GuestAddrs.block_header_ssz_to_rlp + 572)),
    .AUIPC .x10 (laHi GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 576)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 576)),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 588)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 588)),
    .ADD .x12 .x12 .x23,
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_uint_be (GuestAddrs.block_header_ssz_to_rlp + 600)),
    .ADD .x23 .x23 .x10,
    .ADDI .x10 .x8 (428 : BitVec 12),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 616)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 616)),
    .JAL .x1 (jalOff GuestAddrs.bhr_rev_le_be (GuestAddrs.block_header_ssz_to_rlp + 624)),
    .AUIPC .x10 (laHi GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 628)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 628)),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 640)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 640)),
    .ADD .x12 .x12 .x23,
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_uint_be (GuestAddrs.block_header_ssz_to_rlp + 652)),
    .ADD .x23 .x23 .x10,
    .LBU .x5 .x8 (436 : BitVec 12),
    .LBU .x6 .x8 (437 : BitVec 12),
    .SLLI .x6 .x6 (8 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LBU .x6 .x8 (438 : BitVec 12),
    .SLLI .x6 .x6 (16 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LBU .x6 .x8 (439 : BitVec 12),
    .SLLI .x6 .x6 (24 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LBU .x7 .x8 (504 : BitVec 12),
    .LBU .x6 .x8 (505 : BitVec 12),
    .SLLI .x6 .x6 (8 : BitVec 6),
    .OR .x7 .x7 .x6,
    .LBU .x6 .x8 (506 : BitVec 12),
    .SLLI .x6 .x6 (16 : BitVec 6),
    .OR .x7 .x7 .x6,
    .LBU .x6 .x8 (507 : BitVec 12),
    .SLLI .x6 .x6 (24 : BitVec 6),
    .OR .x7 .x7 .x6,
    .SUB .x11 .x7 .x5,
    .ADD .x10 .x8 .x5,
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 748)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 748)),
    .ADD .x12 .x12 .x23,
    .AUIPC .x13 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 760)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 760)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.block_header_ssz_to_rlp + 768)),
    .AUIPC .x5 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 772)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 772)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x6,
    .ADDI .x10 .x8 (372 : BitVec 12),
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 796)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 796)),
    .ADD .x12 .x12 .x23,
    .AUIPC .x13 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 808)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 808)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.block_header_ssz_to_rlp + 816)),
    .AUIPC .x5 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 820)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 820)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x6,
    .AUIPC .x10 (laHi GuestAddrs.bhr_zero8 (GuestAddrs.block_header_ssz_to_rlp + 836)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bhr_zero8 (GuestAddrs.block_header_ssz_to_rlp + 836)),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 848)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 848)),
    .ADD .x12 .x12 .x23,
    .AUIPC .x13 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 860)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 860)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.block_header_ssz_to_rlp + 868)),
    .AUIPC .x5 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 872)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 872)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x6,
    .ADDI .x10 .x8 (440 : BitVec 12),
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 896)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 896)),
    .JAL .x1 (jalOff GuestAddrs.bhr_rev_le_be (GuestAddrs.block_header_ssz_to_rlp + 904)),
    .AUIPC .x10 (laHi GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 908)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 908)),
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 920)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 920)),
    .ADD .x12 .x12 .x23,
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_uint_be (GuestAddrs.block_header_ssz_to_rlp + 932)),
    .ADD .x23 .x23 .x10,
    .MV .x10 .x18,
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 948)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 948)),
    .ADD .x12 .x12 .x23,
    .AUIPC .x13 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 960)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 960)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.block_header_ssz_to_rlp + 968)),
    .AUIPC .x5 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 972)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 972)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x6,
    .ADDI .x10 .x8 (512 : BitVec 12),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 996)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 996)),
    .JAL .x1 (jalOff GuestAddrs.bhr_rev_le_be (GuestAddrs.block_header_ssz_to_rlp + 1004)),
    .AUIPC .x10 (laHi GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 1008)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 1008)),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 1020)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 1020)),
    .ADD .x12 .x12 .x23,
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_uint_be (GuestAddrs.block_header_ssz_to_rlp + 1032)),
    .ADD .x23 .x23 .x10,
    .ADDI .x10 .x8 (520 : BitVec 12),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 1048)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 1048)),
    .JAL .x1 (jalOff GuestAddrs.bhr_rev_le_be (GuestAddrs.block_header_ssz_to_rlp + 1056)),
    .AUIPC .x10 (laHi GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 1060)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 1060)),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 1072)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 1072)),
    .ADD .x12 .x12 .x23,
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_uint_be (GuestAddrs.block_header_ssz_to_rlp + 1084)),
    .ADD .x23 .x23 .x10,
    .MV .x10 .x19,
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 1100)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 1100)),
    .ADD .x12 .x12 .x23,
    .AUIPC .x13 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 1112)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 1112)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.block_header_ssz_to_rlp + 1120)),
    .AUIPC .x5 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 1124)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 1124)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x6,
    .MV .x10 .x20,
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 1148)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 1148)),
    .ADD .x12 .x12 .x23,
    .AUIPC .x13 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 1160)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 1160)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.block_header_ssz_to_rlp + 1168)),
    .AUIPC .x5 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 1172)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 1172)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x6,
    .MV .x10 .x24,
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 1196)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 1196)),
    .ADD .x12 .x12 .x23,
    .AUIPC .x13 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 1208)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 1208)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.block_header_ssz_to_rlp + 1216)),
    .AUIPC .x5 (laHi GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 1220)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bhr_flen (GuestAddrs.block_header_ssz_to_rlp + 1220)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x6,
    .ADDI .x10 .x8 (532 : BitVec 12),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 1244)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 1244)),
    .JAL .x1 (jalOff GuestAddrs.bhr_rev_le_be (GuestAddrs.block_header_ssz_to_rlp + 1252)),
    .AUIPC .x10 (laHi GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 1256)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bhr_uint_be (GuestAddrs.block_header_ssz_to_rlp + 1256)),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 1268)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 1268)),
    .ADD .x12 .x12 .x23,
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_uint_be (GuestAddrs.block_header_ssz_to_rlp + 1280)),
    .ADD .x23 .x23 .x10,
    .MV .x10 .x23,
    .MV .x11 .x21,
    .AUIPC .x12 (laHi GuestAddrs.bhr_prefix_len (GuestAddrs.block_header_ssz_to_rlp + 1296)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bhr_prefix_len (GuestAddrs.block_header_ssz_to_rlp + 1296)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_list_prefix (GuestAddrs.block_header_ssz_to_rlp + 1304)),
    .AUIPC .x5 (laHi GuestAddrs.bhr_prefix_len (GuestAddrs.block_header_ssz_to_rlp + 1308)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bhr_prefix_len (GuestAddrs.block_header_ssz_to_rlp + 1308)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x7 .x21 .x6,
    .AUIPC .x28 (laHi GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 1324)),
    .ADDI .x28 .x28 (laLo GuestAddrs.bhr_payload (GuestAddrs.block_header_ssz_to_rlp + 1324)),
    .MV .x29 .x23,
    .BEQ .x29 .x0 (28 : BitVec 13),
    .LBU .x30 .x28 (0 : BitVec 12),
    .SB .x7 .x30 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADD .x6 .x6 .x23,
    .SD .x22 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .ADDI .x2 .x2 (96 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blockHeaderSszToRlp_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blockHeaderSszToRlp_relocs : RelocTable :=
  [ (22, .la .x12 "bhr_payload"),
    (25, .la .x13 "bhr_flen"),
    (27, .jal .x1 "rlp_encode_bytes"),
    (28, .la .x5 "bhr_flen"),
    (32, .la .x10 "bhr_empty_ommers"),
    (35, .la .x12 "bhr_payload"),
    (38, .la .x13 "bhr_flen"),
    (40, .jal .x1 "rlp_encode_bytes"),
    (41, .la .x5 "bhr_flen"),
    (47, .la .x12 "bhr_payload"),
    (50, .la .x13 "bhr_flen"),
    (52, .jal .x1 "rlp_encode_bytes"),
    (53, .la .x5 "bhr_flen"),
    (59, .la .x12 "bhr_payload"),
    (62, .la .x13 "bhr_flen"),
    (64, .jal .x1 "rlp_encode_bytes"),
    (65, .la .x5 "bhr_flen"),
    (71, .la .x12 "bhr_payload"),
    (74, .la .x13 "bhr_flen"),
    (76, .jal .x1 "rlp_encode_bytes"),
    (77, .la .x5 "bhr_flen"),
    (83, .la .x12 "bhr_payload"),
    (86, .la .x13 "bhr_flen"),
    (88, .jal .x1 "rlp_encode_bytes"),
    (89, .la .x5 "bhr_flen"),
    (95, .la .x12 "bhr_payload"),
    (98, .la .x13 "bhr_flen"),
    (100, .jal .x1 "rlp_encode_bytes"),
    (101, .la .x5 "bhr_flen"),
    (105, .la .x10 "bhr_zero8"),
    (108, .la .x12 "bhr_payload"),
    (111, .jal .x1 "rlp_encode_uint_be"),
    (115, .la .x12 "bhr_uint_be"),
    (117, .jal .x1 "bhr_rev_le_be"),
    (118, .la .x10 "bhr_uint_be"),
    (121, .la .x12 "bhr_payload"),
    (124, .jal .x1 "rlp_encode_uint_be"),
    (128, .la .x12 "bhr_uint_be"),
    (130, .jal .x1 "bhr_rev_le_be"),
    (131, .la .x10 "bhr_uint_be"),
    (134, .la .x12 "bhr_payload"),
    (137, .jal .x1 "rlp_encode_uint_be"),
    (141, .la .x12 "bhr_uint_be"),
    (143, .jal .x1 "bhr_rev_le_be"),
    (144, .la .x10 "bhr_uint_be"),
    (147, .la .x12 "bhr_payload"),
    (150, .jal .x1 "rlp_encode_uint_be"),
    (154, .la .x12 "bhr_uint_be"),
    (156, .jal .x1 "bhr_rev_le_be"),
    (157, .la .x10 "bhr_uint_be"),
    (160, .la .x12 "bhr_payload"),
    (163, .jal .x1 "rlp_encode_uint_be"),
    (187, .la .x12 "bhr_payload"),
    (190, .la .x13 "bhr_flen"),
    (192, .jal .x1 "rlp_encode_bytes"),
    (193, .la .x5 "bhr_flen"),
    (199, .la .x12 "bhr_payload"),
    (202, .la .x13 "bhr_flen"),
    (204, .jal .x1 "rlp_encode_bytes"),
    (205, .la .x5 "bhr_flen"),
    (209, .la .x10 "bhr_zero8"),
    (212, .la .x12 "bhr_payload"),
    (215, .la .x13 "bhr_flen"),
    (217, .jal .x1 "rlp_encode_bytes"),
    (218, .la .x5 "bhr_flen"),
    (224, .la .x12 "bhr_uint_be"),
    (226, .jal .x1 "bhr_rev_le_be"),
    (227, .la .x10 "bhr_uint_be"),
    (230, .la .x12 "bhr_payload"),
    (233, .jal .x1 "rlp_encode_uint_be"),
    (237, .la .x12 "bhr_payload"),
    (240, .la .x13 "bhr_flen"),
    (242, .jal .x1 "rlp_encode_bytes"),
    (243, .la .x5 "bhr_flen"),
    (249, .la .x12 "bhr_uint_be"),
    (251, .jal .x1 "bhr_rev_le_be"),
    (252, .la .x10 "bhr_uint_be"),
    (255, .la .x12 "bhr_payload"),
    (258, .jal .x1 "rlp_encode_uint_be"),
    (262, .la .x12 "bhr_uint_be"),
    (264, .jal .x1 "bhr_rev_le_be"),
    (265, .la .x10 "bhr_uint_be"),
    (268, .la .x12 "bhr_payload"),
    (271, .jal .x1 "rlp_encode_uint_be"),
    (275, .la .x12 "bhr_payload"),
    (278, .la .x13 "bhr_flen"),
    (280, .jal .x1 "rlp_encode_bytes"),
    (281, .la .x5 "bhr_flen"),
    (287, .la .x12 "bhr_payload"),
    (290, .la .x13 "bhr_flen"),
    (292, .jal .x1 "rlp_encode_bytes"),
    (293, .la .x5 "bhr_flen"),
    (299, .la .x12 "bhr_payload"),
    (302, .la .x13 "bhr_flen"),
    (304, .jal .x1 "rlp_encode_bytes"),
    (305, .la .x5 "bhr_flen"),
    (311, .la .x12 "bhr_uint_be"),
    (313, .jal .x1 "bhr_rev_le_be"),
    (314, .la .x10 "bhr_uint_be"),
    (317, .la .x12 "bhr_payload"),
    (320, .jal .x1 "rlp_encode_uint_be"),
    (324, .la .x12 "bhr_prefix_len"),
    (326, .jal .x1 "rlp_encode_list_prefix"),
    (327, .la .x5 "bhr_prefix_len"),
    (331, .la .x28 "bhr_payload") ]

def blockHeaderSszToRlpFunction : String :=
  "block_header_ssz_to_rlp:\n" ++ emitProgramR blockHeaderSszToRlp_prog blockHeaderSszToRlp_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blockHeaderSszToRlp_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem blockHeaderSszToRlpFunction_eq_prog :
    blockHeaderSszToRlpFunction = "block_header_ssz_to_rlp:\n" ++ emitProgramR blockHeaderSszToRlp_prog blockHeaderSszToRlp_relocs := rfl

#guard blockHeaderSszToRlpFunction.startsWith "block_header_ssz_to_rlp:\n"
/-- `zisk_block_header_ssz_to_rlp`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8   payload_len (u64, informational)
      +16  transactions_root (32B)
      +48  withdrawals_root (32B)
      +80  parent_beacon_block_root (32B)
      +112 requests_hash (32B)
      +144 block_access_list_hash (32B)
      +176 SSZ ExecutionPayload bytes
    Output: OUTPUT+0 = header RLP length (u64); OUTPUT+8 = block hash
    (keccak256 of the re-encoded header RLP, 32 B). The RLP itself is built in
    `bhr_result` scratch (the 627-byte RLP exceeds the 256-byte OUTPUT). -/
def ziskBlockHeaderSszToRlpPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  addi a1, t0, 16             # transactions_root\n" ++
  "  addi a2, t0, 48             # withdrawals_root\n" ++
  "  addi a3, t0, 80             # parent_beacon_block_root\n" ++
  "  addi a4, t0, 112            # requests_hash\n" ++
  "  addi a7, t0, 144            # block_access_list_hash\n" ++
  "  addi a0, t0, 176            # SSZ ExecutionPayload\n" ++
  "  la a5, bhr_result           # header RLP buffer\n" ++
  "  la a6, bhr_result_len\n" ++
  "  jal ra, block_header_ssz_to_rlp\n" ++
  "  # block hash = keccak256(header RLP) -> OUTPUT+8; rlp_len -> OUTPUT+0.\n" ++
  "  la t0, bhr_result_len; ld a1, 0(t0)\n" ++
  "  la a0, bhr_result\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  la t0, bhr_result_len; ld t1, 0(t0); li t2, 0xa0010000; sd t1, 0(t2)\n" ++
  "  j .Lbhr_pdone\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  bhrRevLeBeFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHeaderSszToRlpFunction ++ "\n" ++
  ".Lbhr_pdone:"

def ziskBlockHeaderSszToRlpDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "bhr_empty_ommers:\n" ++
  "  .byte 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a\n" ++
  "  .byte 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a\n" ++
  "  .byte 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13\n" ++
  "  .byte 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47\n" ++
  ".balign 8\n" ++
  "bhr_zero8:\n  .zero 8\n" ++
  "bhr_flen:\n  .zero 8\n" ++
  "bhr_prefix_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bhr_uint_be:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "zk3_state:\n  .zero 200\n" ++
  "bhr_result_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "bhr_payload:\n  .zero 1024\n" ++
  ".balign 8\n" ++
  "bhr_result:\n  .zero 1024"


end EvmAsm.Codegen
