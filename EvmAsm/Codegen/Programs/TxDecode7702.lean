/-
  EvmAsm.Codegen.Programs.TxDecode7702

  EIP-7702 typed-transaction decoder split out of `TxDecode.lean`.

  Hosts:
    K44  tx_eip7702_decode   (13-field EIP-7702)

  Uses the cursor-advancing walker pair (`EvmAsm.Codegen.Programs.
  RlpWalk`) instead of the index-based `rlp_field_to_*` wrappers,
  so all 13 fields are decoded in a single left-to-right pass
  (13 item visits) rather than 0+1+...+12 = 78 re-walks.

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
open EvmAsm.Rv64.Program

/-! ## tx_eip7702_decode -- PR-K44 full 13-field EIP-7702 decoder

    Decode the inner (post-type-byte) RLP body of an EIP-7702
    (type-4) set-code transaction into a flat 240-byte output
    struct. Inner RLP shape (13 fields):

      rlp([
        chain_id, nonce,
        max_priority_fee_per_gas, max_fee_per_gas,
        gas_limit, to, value, data,
        access_list, authorization_list,
        y_parity, r, s
      ])

    Compared to PR-K41 EIP-1559 (12 fields), EIP-7702 inserts an
    `authorization_list` after `access_list` -- a list of
    (chain_id, address, nonce, y_parity, r, s) authorization
    tuples. The decoder records only its outer (offset, length)
    bounds; sub-decoding into individual authorization entries
    lands in a follow-up PR.

    Output struct (240 bytes; u32 offsets/lengths to fit the
    256-byte ziskemu output cap):

       0..  8  chain_id              (u64 LE)
       8.. 16  nonce                 (u64 LE)
      16.. 48  max_priority_fee_per_gas (u256 BE)
      48.. 80  max_fee_per_gas       (u256 BE)
      80.. 88  gas_limit             (u64 LE)
      88..108  to (20-byte address; zero for creation -- but
                  EIP-7702 spec requires `to` so empty paths
                  are still reported as creation status=1)
     108..112  to_present (u32; 0 = creation, 1 = call)
     112..144  value                 (u256 BE)
     144..148  data_offset           (u32)
     148..152  data_length           (u32)
     152..156  access_list_offset    (u32; whole encoded item)
     156..160  access_list_length    (u32; whole encoded item)
     160..164  auth_list_offset      (u32; whole encoded item)
     164..168  auth_list_length      (u32; whole encoded item)
     168..176  y_parity              (u64; 0 or 1)
     176..208  r                     (u256 BE)
     208..240  s                     (u256 BE)

    access_list / authorization_list semantics: per
    `rlp_walk_next`'s contract for list items, the recorded
    (offset, length) span the *full* encoded sub-list including
    its RLP prefix.  Byte-string items (data) are prefix-stripped.

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : output struct ptr (240 bytes)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail -/
def txEip7702Decode_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x18 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_eip7702_decode + 32)),
    .BNE .x12 .x0 (584 : BitVec 13),
    .MV .x9 .x11,
    .MV .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_decode + 56)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (556 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64 (GuestAddrs.tx_eip7702_decode + 76)),
    .BNE .x11 .x0 (540 : BitVec 13),
    .SD .x18 .x10 (0 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_decode + 96)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (516 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64 (GuestAddrs.tx_eip7702_decode + 116)),
    .BNE .x11 .x0 (500 : BitVec 13),
    .SD .x18 .x10 (8 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_decode + 136)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (476 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (16 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be (GuestAddrs.tx_eip7702_decode + 160)),
    .BNE .x10 .x0 (456 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_decode + 176)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (436 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be (GuestAddrs.tx_eip7702_decode + 200)),
    .BNE .x10 .x0 (416 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_decode + 216)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (396 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64 (GuestAddrs.tx_eip7702_decode + 236)),
    .BNE .x11 .x0 (380 : BitVec 13),
    .SD .x18 .x10 (80 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_decode + 256)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (356 : BitVec 13),
    .BEQ .x12 .x0 (56 : BitVec 13),
    .LI .x5 (20 : Word),
    .BNE .x12 .x5 (344 : BitVec 13),
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
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_decode + 352)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (260 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (112 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be (GuestAddrs.tx_eip7702_decode + 376)),
    .BNE .x10 .x0 (240 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_decode + 392)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (220 : BitVec 13),
    .SUB .x28 .x10 .x12,
    .SUB .x6 .x28 .x8,
    .SW .x18 .x6 (144 : BitVec 12),
    .SW .x18 .x12 (148 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_decode + 428)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (184 : BitVec 13),
    .SUB .x28 .x10 .x12,
    .SUB .x6 .x28 .x8,
    .SW .x18 .x6 (152 : BitVec 12),
    .SW .x18 .x12 (156 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_decode + 464)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (148 : BitVec 13),
    .SUB .x28 .x10 .x12,
    .SUB .x6 .x28 .x8,
    .SW .x18 .x6 (160 : BitVec 12),
    .SW .x18 .x12 (164 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_decode + 500)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (112 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64 (GuestAddrs.tx_eip7702_decode + 520)),
    .BNE .x11 .x0 (96 : BitVec 13),
    .SD .x18 .x10 (168 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_decode + 540)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (72 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (176 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be (GuestAddrs.tx_eip7702_decode + 564)),
    .BNE .x10 .x0 (52 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_decode + 580)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (32 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (208 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be (GuestAddrs.tx_eip7702_decode + 604)),
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

/-- Reloc side-table for `txEip7702Decode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txEip7702Decode_relocs : RelocTable :=
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
    (125, .jal .x1 "rlp_walk_next"),
    (130, .jal .x1 "rlp_content_to_u64"),
    (135, .jal .x1 "rlp_walk_next"),
    (141, .jal .x1 "rlp_content_to_u256_be"),
    (145, .jal .x1 "rlp_walk_next"),
    (151, .jal .x1 "rlp_content_to_u256_be") ]

def txEip7702DecodeFunction : String :=
  "tx_eip7702_decode:\n" ++ emitProgramR txEip7702Decode_prog txEip7702Decode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txEip7702Decode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txEip7702DecodeFunction_eq_prog :
    txEip7702DecodeFunction = "tx_eip7702_decode:\n" ++ emitProgramR txEip7702Decode_prog txEip7702Decode_relocs := rfl

#guard txEip7702DecodeFunction.startsWith "tx_eip7702_decode:\n"
#guard txEip7702Decode_prog.length = 163
/-- `zisk_tx_eip7702_decode`: probe BuildUnit. Reads (inner_len,
    inner_bytes) from host input -- caller is expected to have
    stripped the 0x04 type byte. Writes (status, 240-byte struct)
    to OUTPUT (248 bytes total). -/
def ziskTxEip7702DecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # inner_len\n" ++
  "  addi a0, a3, 16             # inner ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 240 bytes (30 × 8 dwords).\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 30\n" ++
  ".Lt77_zinit:\n" ++
  "  beqz t1, .Lt77_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt77_zinit\n" ++
  ".Lt77_zdone:\n" ++
  "  jal ra, tx_eip7702_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lt77_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  txEip7702DecodeFunction ++ "\n" ++
  ".Lt77_pdone:"

/-- The decoder holds (cursor, end) in callee-saved registers and
    derives every content pointer arithmetically, so it needs no
    `.data` scratch. -/
def ziskTxEip7702DecodeDataSection : String := ""

def ziskTxEip7702DecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip7702DecodePrologue
  dataAsm     := ziskTxEip7702DecodeDataSection
}

end EvmAsm.Codegen
