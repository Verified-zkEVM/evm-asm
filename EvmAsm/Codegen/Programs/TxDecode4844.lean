/-
  EvmAsm.Codegen.Programs.TxDecode4844

  EIP-4844 typed-transaction decoder split out of `TxDecode.lean`.

  Hosts:
    K45  tx_eip4844_decode   (14-field EIP-4844)

  Uses the cursor-advancing walker pair (`EvmAsm.Codegen.Programs.
  RlpWalk`) instead of the index-based `rlp_field_to_*` wrappers,
  so all 14 fields are decoded in a single left-to-right pass
  (14 item visits) rather than 0+1+...+13 = 91 re-walks.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## tx_eip4844_decode -- PR-K45 full 14-field EIP-4844 decoder

    Decode the inner (post-type-byte) RLP body of an EIP-4844
    (type-3) blob transaction into a flat 248-byte output struct.
    Inner RLP shape (14 fields):

      rlp([
        chain_id, nonce,
        max_priority_fee_per_gas, max_fee_per_gas,
        gas_limit, to, value, data,
        access_list,
        max_fee_per_blob_gas, blob_versioned_hashes,
        y_parity, r, s
      ])

    Compared to PR-K41 EIP-1559 (12 fields), EIP-4844 inserts
    `max_fee_per_blob_gas` (u256) and `blob_versioned_hashes`
    (list of 32-byte hashes) between `access_list` and `y_parity`.

    NOTE on max_fee_per_blob_gas: the spec type is u256, but
    real-world blob fees fit comfortably in u64 (mainnet typical
    range is 1 wei .. low gwei). To keep the struct within
    ziskemu's 256-byte output cap, this decoder stores the field
    as `u64` (low 64 bits of the u256) and TOLERATES values that
    exceed u64 -- the full u256 (BE) is also persisted to the
    `.data` cell `tcbg_blob_fee_be` for callers (EIP-8037 gate /
    `BlockVerdict`) that need the complete value. In the high
    blob-fee regime (parent excess_blob_gas > ~328M) the blob gas
    price exceeds u64, so a valid tx's max_fee_per_blob_gas does
    too; the old index-based reject false-rejected those valid
    blob txs.

    Output struct (248 bytes; u32 offsets/lengths):

       0..  8  chain_id                  (u64 LE)
       8.. 16  nonce                     (u64 LE)
      16.. 48  max_priority_fee_per_gas  (u256 BE)
      48.. 80  max_fee_per_gas           (u256 BE)
      80.. 88  gas_limit                 (u64 LE)
      88..108  to (20-byte address; zero for creation -- but
                  EIP-4844 spec disallows creation, so empty
                  to is just reported via to_present=0)
     108..112  to_present (u32; 0 = creation, 1 = call)
     112..144  value                     (u256 BE)
     144..148  data_offset               (u32)
     148..152  data_length               (u32)
     152..156  access_list_offset        (u32; whole encoded item)
     156..160  access_list_length        (u32; whole encoded item)
     160..168  max_fee_per_blob_gas      (u64 LE; low 64 bits of the u256)
     168..172  blob_versioned_hashes_off (u32; whole encoded item)
     172..176  blob_versioned_hashes_len (u32; whole encoded item)
     176..184  y_parity                  (u64; 0 or 1)
     184..216  r                         (u256 BE)
     216..248  s                         (u256 BE)

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : output struct ptr (248 bytes)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail -/
def txEip4844Decode_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x18 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_eip4844_decode + 32)),
    .BNE .x12 .x0 (728 : BitVec 13),
    .MV .x9 .x11,
    .MV .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_decode + 56)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (700 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64 (GuestAddrs.tx_eip4844_decode + 76)),
    .BNE .x11 .x0 (684 : BitVec 13),
    .SD .x18 .x10 (0 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_decode + 96)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (660 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64 (GuestAddrs.tx_eip4844_decode + 116)),
    .BNE .x11 .x0 (644 : BitVec 13),
    .SD .x18 .x10 (8 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_decode + 136)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (620 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (16 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be (GuestAddrs.tx_eip4844_decode + 160)),
    .BNE .x10 .x0 (600 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_decode + 176)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (580 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be (GuestAddrs.tx_eip4844_decode + 200)),
    .BNE .x10 .x0 (560 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_decode + 216)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (540 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64 (GuestAddrs.tx_eip4844_decode + 236)),
    .BNE .x11 .x0 (524 : BitVec 13),
    .SD .x18 .x10 (80 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_decode + 256)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (500 : BitVec 13),
    .BEQ .x12 .x0 (56 : BitVec 13),
    .LI .x5 (20 : Word),
    .BNE .x12 .x5 (488 : BitVec 13),
    .SUB .x28 .x10 .x12,
    .ADDI .x29 .x18 (88 : BitVec 12),
    .LD .x30 .x28 (0 : BitVec 12),
    .SD .x29 .x30 (0 : BitVec 12),
    .LD .x30 .x28 (8 : BitVec 12),
    .SD .x29 .x30 (8 : BitVec 12),
    .LWU .x30 .x28 (16 : BitVec 12),
    .SW .x29 .x30 (16 : BitVec 12),
    .LI .x30 (1 : Word),
    .SW .x18 .x30 (108 : BitVec 12),
    .JAL .x0 (24 : BitVec 21),
    .ADDI .x29 .x18 (88 : BitVec 12),
    .SD .x29 .x0 (0 : BitVec 12),
    .SD .x29 .x0 (8 : BitVec 12),
    .SW .x29 .x0 (16 : BitVec 12),
    .SW .x18 .x0 (108 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_decode + 352)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (404 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (112 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be (GuestAddrs.tx_eip4844_decode + 376)),
    .BNE .x10 .x0 (384 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_decode + 392)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (364 : BitVec 13),
    .SUB .x28 .x10 .x12,
    .SUB .x6 .x28 .x8,
    .SW .x18 .x6 (144 : BitVec 12),
    .SW .x18 .x12 (148 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_decode + 428)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (328 : BitVec 13),
    .SUB .x28 .x10 .x12,
    .SUB .x6 .x28 .x8,
    .SW .x18 .x6 (152 : BitVec 12),
    .SW .x18 .x12 (156 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_decode + 464)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (292 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .AUIPC .x12 (laHi GuestAddrs.tcbg_blob_fee_be (GuestAddrs.tx_eip4844_decode + 484)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tcbg_blob_fee_be (GuestAddrs.tx_eip4844_decode + 484)),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be (GuestAddrs.tx_eip4844_decode + 492)),
    .BNE .x10 .x0 (268 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.tcbg_blob_fee_be (GuestAddrs.tx_eip4844_decode + 500)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tcbg_blob_fee_be (GuestAddrs.tx_eip4844_decode + 500)),
    .LBU .x6 .x5 (24 : BitVec 12),
    .SLLI .x6 .x6 (56 : BitVec 6),
    .LBU .x7 .x5 (25 : BitVec 12),
    .SLLI .x7 .x7 (48 : BitVec 6),
    .OR .x6 .x6 .x7,
    .LBU .x7 .x5 (26 : BitVec 12),
    .SLLI .x7 .x7 (40 : BitVec 6),
    .OR .x6 .x6 .x7,
    .LBU .x7 .x5 (27 : BitVec 12),
    .SLLI .x7 .x7 (32 : BitVec 6),
    .OR .x6 .x6 .x7,
    .LBU .x7 .x5 (28 : BitVec 12),
    .SLLI .x7 .x7 (24 : BitVec 6),
    .OR .x6 .x6 .x7,
    .LBU .x7 .x5 (29 : BitVec 12),
    .SLLI .x7 .x7 (16 : BitVec 6),
    .OR .x6 .x6 .x7,
    .LBU .x7 .x5 (30 : BitVec 12),
    .SLLI .x7 .x7 (8 : BitVec 6),
    .OR .x6 .x6 .x7,
    .LBU .x7 .x5 (31 : BitVec 12),
    .OR .x6 .x6 .x7,
    .SD .x18 .x6 (160 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_decode + 608)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (148 : BitVec 13),
    .SUB .x28 .x10 .x12,
    .SUB .x6 .x28 .x8,
    .SW .x18 .x6 (168 : BitVec 12),
    .SW .x18 .x12 (172 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_decode + 644)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (112 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64 (GuestAddrs.tx_eip4844_decode + 664)),
    .BNE .x11 .x0 (96 : BitVec 13),
    .SD .x18 .x10 (176 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_decode + 684)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (72 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (184 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be (GuestAddrs.tx_eip4844_decode + 708)),
    .BNE .x10 .x0 (52 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip4844_decode + 724)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (32 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (216 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be (GuestAddrs.tx_eip4844_decode + 748)),
    .BNE .x10 .x0 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txEip4844Decode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txEip4844Decode_relocs : RelocTable :=
  [ (8, .jal .x1 "rlp_walk_init"),
    (14, .jal .x1 "rlp_walk_next"),
    (19, .jal .x1 "rlp_content_to_u64"),
    (24, .jal .x1 "rlp_walk_next"),
    (29, .jal .x1 "rlp_content_to_u64"),
    (34, .jal .x1 "rlp_walk_next"),
    (40, .jal .x1 "rlp_content_to_u256_be"),
    (44, .jal .x1 "rlp_walk_next"),
    (50, .jal .x1 "rlp_content_to_u256_be"),
    (54, .jal .x1 "rlp_walk_next"),
    (59, .jal .x1 "rlp_content_to_u64"),
    (64, .jal .x1 "rlp_walk_next"),
    (88, .jal .x1 "rlp_walk_next"),
    (94, .jal .x1 "rlp_content_to_u256_be"),
    (98, .jal .x1 "rlp_walk_next"),
    (107, .jal .x1 "rlp_walk_next"),
    (116, .jal .x1 "rlp_walk_next"),
    (121, .la .x12 "tcbg_blob_fee_be"),
    (123, .jal .x1 "rlp_content_to_u256_be"),
    (125, .la .x5 "tcbg_blob_fee_be"),
    (152, .jal .x1 "rlp_walk_next"),
    (161, .jal .x1 "rlp_walk_next"),
    (166, .jal .x1 "rlp_content_to_u64"),
    (171, .jal .x1 "rlp_walk_next"),
    (177, .jal .x1 "rlp_content_to_u256_be"),
    (181, .jal .x1 "rlp_walk_next"),
    (187, .jal .x1 "rlp_content_to_u256_be") ]

def txEip4844DecodeFunction : String :=
  "tx_eip4844_decode:\n" ++ emitProgramR txEip4844Decode_prog txEip4844Decode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txEip4844Decode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txEip4844DecodeFunction_eq_prog :
    txEip4844DecodeFunction = "tx_eip4844_decode:\n" ++ emitProgramR txEip4844Decode_prog txEip4844Decode_relocs := rfl

#guard txEip4844DecodeFunction.startsWith "tx_eip4844_decode:\n"
#guard txEip4844Decode_prog.length = 199
/-- `zisk_tx_eip4844_decode`: probe BuildUnit. Reads (inner_len,
    inner_bytes) from host input -- caller is expected to have
    stripped the 0x03 type byte. Writes (status, 248-byte struct)
    to OUTPUT (256 bytes total). -/
def ziskTxEip4844DecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # inner_len\n" ++
  "  addi a0, a3, 16             # inner ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 248 bytes (31 × 8 dwords).\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 31\n" ++
  ".Lt48_zinit:\n" ++
  "  beqz t1, .Lt48_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt48_zinit\n" ++
  ".Lt48_zdone:\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lt48_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  ".Lt48_pdone:"

/-- The decoder holds (cursor, end) in callee-saved registers and
    derives every content pointer arithmetically, so the only
    `.data` cell it needs is `tcbg_blob_fee_be` -- the full BE
    u256 of `max_fee_per_blob_gas` that downstream consumers
    (`BlockVerdict` / EIP-8037 gate) read back. Declaring it here
    (previously it was only declared in unrelated probe data
    sections, leaving the standalone 4844 + dispatch probes unable
    to link) makes this probe self-contained. -/
def ziskTxEip4844DecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "tcbg_blob_fee_be:\n" ++
  "  .zero 32"

def ziskTxEip4844DecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip4844DecodePrologue
  dataAsm     := ziskTxEip4844DecodeDataSection
}

end EvmAsm.Codegen
