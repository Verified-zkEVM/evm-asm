/-
  EvmAsm.Codegen.Programs.TxDecode1559

  EIP-1559 typed-transaction decoder split out of `TxDecode.lean`.

  Hosts:
    K41  tx_eip1559_decode   (12-field EIP-1559)

  Uses the cursor-advancing walker pair (`EvmAsm.Codegen.Programs.
  RlpWalk`) instead of the index-based `rlp_field_to_*` wrappers,
  so all 12 fields are decoded in a single left-to-right pass
  (12 item visits) rather than 0+1+...+11 = 66 re-walks.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## tx_eip1559_decode -- PR-K41 full 12-field EIP-1559 decoder

    Decode the inner (post-type-byte) RLP body of an EIP-1559
    (type-2) transaction into a flat 248-byte output struct.
    Inner RLP shape (12 fields):

      rlp([
        chain_id, nonce,
        max_priority_fee_per_gas, max_fee_per_gas,
        gas_limit, to, value, data, access_list,
        y_parity, r, s
      ])

    Output struct (248 bytes):
       0..  8  chain_id              (u64 LE)
       8.. 16  nonce                 (u64 LE)
      16.. 48  max_priority_fee_per_gas (u256 BE)
      48.. 80  max_fee_per_gas       (u256 BE)
      80.. 88  gas_limit             (u64 LE)
      88..108  to (20-byte address; zero for creation)
     108..112  to_present (u32; 0 = creation, 1 = call)
     112..144  value                 (u256 BE)
     144..152  data_offset           (u64 within inner RLP)
     152..160  data_length           (u64)
     160..168  access_list_offset    (u64; whole encoded item incl. prefix)
     168..176  access_list_length    (u64; whole encoded item incl. prefix)
     176..184  y_parity              (u64; 0 or 1)
     184..216  r                     (u256 BE)
     216..248  s                     (u256 BE)

    access_list semantics: per `rlp_walk_next`'s contract for list
    items, the recorded (offset, length) span the *full* encoded
    sub-list including its RLP prefix, so the caller can recurse
    into it.  Byte-string items (data) are prefix-stripped.

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : output struct ptr (248 bytes)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail -/
def txEip1559Decode_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x18 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_eip1559_decode + 32)),
    .BNE .x12 .x0 (548 : BitVec 13),
    .MV .x9 .x11,
    .MV .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_decode + 56)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (520 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.tx_eip1559_decode + 76)),
    .BNE .x11 .x0 (504 : BitVec 13),
    .SD .x18 .x10 (0 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_decode + 96)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (480 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.tx_eip1559_decode + 116)),
    .BNE .x11 .x0 (464 : BitVec 13),
    .SD .x18 .x10 (8 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_decode + 136)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (440 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (16 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_eip1559_decode + 160)),
    .BNE .x10 .x0 (420 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_decode + 176)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (400 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_eip1559_decode + 200)),
    .BNE .x10 .x0 (380 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_decode + 216)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (360 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.tx_eip1559_decode + 236)),
    .BNE .x11 .x0 (344 : BitVec 13),
    .SD .x18 .x10 (80 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_decode + 256)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (320 : BitVec 13),
    .BEQ .x12 .x0 (56 : BitVec 13),
    .LI .x5 (20 : Word),
    .BNE .x12 .x5 (308 : BitVec 13),
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
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_decode + 352)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (224 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (112 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_eip1559_decode + 376)),
    .BNE .x10 .x0 (204 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_decode + 392)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (184 : BitVec 13),
    .SUB .x28 .x10 .x12,
    .SUB .x6 .x28 .x8,
    .SD .x18 .x6 (144 : BitVec 12),
    .SD .x18 .x12 (152 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_decode + 428)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (148 : BitVec 13),
    .SUB .x28 .x10 .x12,
    .SUB .x6 .x28 .x8,
    .SD .x18 .x6 (160 : BitVec 12),
    .SD .x18 .x12 (168 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_decode + 464)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (112 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.tx_eip1559_decode + 484)),
    .BNE .x11 .x0 (96 : BitVec 13),
    .SD .x18 .x10 (176 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_decode + 504)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (72 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (184 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_eip1559_decode + 528)),
    .BNE .x10 .x0 (52 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip1559_decode + 544)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (32 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (216 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_eip1559_decode + 568)),
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

/-- Reloc side-table for `txEip1559Decode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txEip1559Decode_relocs : RelocTable :=
  [ (8, .jal .x1 "rlp_walk_init"),
    (14, .jal .x1 "rlp_walk_next"),
    (19, .jal .x1 "rlp_content_to_u64_strict"),
    (24, .jal .x1 "rlp_walk_next"),
    (29, .jal .x1 "rlp_content_to_u64_strict"),
    (34, .jal .x1 "rlp_walk_next"),
    (40, .jal .x1 "rlp_content_to_u256_be_strict"),
    (44, .jal .x1 "rlp_walk_next"),
    (50, .jal .x1 "rlp_content_to_u256_be_strict"),
    (54, .jal .x1 "rlp_walk_next"),
    (59, .jal .x1 "rlp_content_to_u64_strict"),
    (64, .jal .x1 "rlp_walk_next"),
    (88, .jal .x1 "rlp_walk_next"),
    (94, .jal .x1 "rlp_content_to_u256_be_strict"),
    (98, .jal .x1 "rlp_walk_next"),
    (107, .jal .x1 "rlp_walk_next"),
    (116, .jal .x1 "rlp_walk_next"),
    (121, .jal .x1 "rlp_content_to_u64_strict"),
    (126, .jal .x1 "rlp_walk_next"),
    (132, .jal .x1 "rlp_content_to_u256_be_strict"),
    (136, .jal .x1 "rlp_walk_next"),
    (142, .jal .x1 "rlp_content_to_u256_be_strict") ]

def txEip1559DecodeFunction : String :=
  "tx_eip1559_decode:\n" ++ emitProgramR txEip1559Decode_prog txEip1559Decode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txEip1559Decode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txEip1559DecodeFunction_eq_prog :
    txEip1559DecodeFunction = "tx_eip1559_decode:\n" ++ emitProgramR txEip1559Decode_prog txEip1559Decode_relocs := rfl

#guard txEip1559DecodeFunction.startsWith "tx_eip1559_decode:\n"
#guard txEip1559Decode_prog.length = 154
/-- `zisk_tx_eip1559_decode`: probe BuildUnit. Reads (inner_len,
    inner_bytes) from host input -- caller is expected to have
    stripped the 0x02 type byte. Writes (status, 248-byte struct)
    to OUTPUT (256 bytes total, matching ziskemu's output cap). -/
def ziskTxEip1559DecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # inner_len\n" ++
  "  addi a0, a3, 16             # inner ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 248 bytes (31 × 8 dwords).\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 31\n" ++
  ".Lt1d_zinit:\n" ++
  "  beqz t1, .Lt1d_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt1d_zinit\n" ++
  ".Lt1d_zdone:\n" ++
  "  jal ra, tx_eip1559_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lt1d_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  txEip1559DecodeFunction ++ "\n" ++
  ".Lt1d_pdone:"

/-- The decoder holds (cursor, end) in callee-saved registers and
    derives every content pointer arithmetically, so it needs no
    `.data` scratch. -/
def ziskTxEip1559DecodeDataSection : String := ""

def ziskTxEip1559DecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip1559DecodePrologue
  dataAsm     := ziskTxEip1559DecodeDataSection
}

end EvmAsm.Codegen
