/-
  EvmAsm.Codegen.Programs.TxDecode2930

  EIP-2930 typed-transaction decoder split out of `TxDecode.lean`.

  Hosts:
    K42  tx_eip2930_decode   (11-field EIP-2930)

  Uses the cursor-advancing walker pair (`EvmAsm.Codegen.Programs.
  RlpWalk`) instead of the index-based `rlp_field_to_*` wrappers,
  so all 11 fields are decoded in a single left-to-right pass
  (11 item visits) rather than 0+1+...+10 = 55 re-walks.

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

/-! ## tx_eip2930_decode -- PR-K42 full 11-field EIP-2930 decoder

    Decode the inner (post-type-byte) RLP body of an EIP-2930
    (type-1) access-list transaction into a flat 216-byte output
    struct. Inner RLP shape (11 fields):

      rlp([
        chain_id, nonce, gas_price, gas_limit,
        to, value, data, access_list,
        y_parity, r, s
      ])

    EIP-2930 is structurally simpler than EIP-1559: a single
    `gas_price` field (legacy-style) instead of the
    `(max_priority_fee_per_gas, max_fee_per_gas)` pair.

    Output struct (216 bytes):
       0..  8  chain_id              (u64 LE)
       8.. 16  nonce                 (u64 LE)
      16.. 48  gas_price             (u256 BE)
      48.. 56  gas_limit             (u64 LE)
      56.. 76  to (20-byte address; zero for creation)
      76.. 80  to_present (u32; 0 = creation, 1 = call)
      80..112  value                 (u256 BE)
     112..120  data_offset           (u64 within inner RLP)
     120..128  data_length           (u64)
     128..136  access_list_offset    (u64; whole encoded item incl. prefix)
     136..144  access_list_length    (u64; whole encoded item incl. prefix)
     144..152  y_parity              (u64; 0 or 1)
     152..184  r                     (u256 BE)
     184..216  s                     (u256 BE)

    access_list semantics: per `rlp_walk_next`'s contract for list
    items, the recorded (offset, length) span the *full* encoded
    sub-list including its RLP prefix, so the caller can recurse
    into it.  Byte-string items (data) are prefix-stripped.

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : output struct ptr (216 bytes)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail -/
def txEip2930Decode_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x18 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_eip2930_decode + 32)),
    .BNE .x12 .x0 (508 : BitVec 13),
    .MV .x9 .x11,
    .MV .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_decode + 56)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (480 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.tx_eip2930_decode + 76)),
    .BNE .x11 .x0 (464 : BitVec 13),
    .SD .x18 .x10 (0 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_decode + 96)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (440 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.tx_eip2930_decode + 116)),
    .BNE .x11 .x0 (424 : BitVec 13),
    .SD .x18 .x10 (8 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_decode + 136)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (400 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (16 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_eip2930_decode + 160)),
    .BNE .x10 .x0 (380 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_decode + 176)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (360 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.tx_eip2930_decode + 196)),
    .BNE .x11 .x0 (344 : BitVec 13),
    .SD .x18 .x10 (48 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_decode + 216)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (320 : BitVec 13),
    .BEQ .x12 .x0 (56 : BitVec 13),
    .LI .x5 (20 : Word),
    .BNE .x12 .x5 (308 : BitVec 13),
    .SUB .x28 .x10 .x12,
    .ADDI .x29 .x18 (56 : BitVec 12),
    .LD .x30 .x28 (0 : BitVec 12),
    .SD .x29 .x30 (0 : BitVec 12),
    .LD .x30 .x28 (8 : BitVec 12),
    .SD .x29 .x30 (8 : BitVec 12),
    .LWU .x30 .x28 (16 : BitVec 12),
    .SW .x29 .x30 (16 : BitVec 12),
    .LI .x30 (1 : Word),
    .SW .x18 .x30 (76 : BitVec 12),
    .JAL .x0 (24 : BitVec 21),
    .ADDI .x29 .x18 (56 : BitVec 12),
    .SD .x29 .x0 (0 : BitVec 12),
    .SD .x29 .x0 (8 : BitVec 12),
    .SW .x29 .x0 (16 : BitVec 12),
    .SW .x18 .x0 (76 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_decode + 312)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (224 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_eip2930_decode + 336)),
    .BNE .x10 .x0 (204 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_decode + 352)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (184 : BitVec 13),
    .SUB .x28 .x10 .x12,
    .SUB .x6 .x28 .x8,
    .SD .x18 .x6 (112 : BitVec 12),
    .SD .x18 .x12 (120 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_decode + 388)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (148 : BitVec 13),
    .SUB .x28 .x10 .x12,
    .SUB .x6 .x28 .x8,
    .SD .x18 .x6 (128 : BitVec 12),
    .SD .x18 .x12 (136 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_decode + 424)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (112 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.tx_eip2930_decode + 444)),
    .BNE .x11 .x0 (96 : BitVec 13),
    .SD .x18 .x10 (144 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_decode + 464)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (72 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (152 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_eip2930_decode + 488)),
    .BNE .x10 .x0 (52 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip2930_decode + 504)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (32 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (184 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_eip2930_decode + 528)),
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

/-- Reloc side-table for `txEip2930Decode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txEip2930Decode_relocs : RelocTable :=
  [ (8, .jal .x1 "rlp_walk_init"),
    (14, .jal .x1 "rlp_walk_next"),
    (19, .jal .x1 "rlp_content_to_u64_strict"),
    (24, .jal .x1 "rlp_walk_next"),
    (29, .jal .x1 "rlp_content_to_u64_strict"),
    (34, .jal .x1 "rlp_walk_next"),
    (40, .jal .x1 "rlp_content_to_u256_be_strict"),
    (44, .jal .x1 "rlp_walk_next"),
    (49, .jal .x1 "rlp_content_to_u64_strict"),
    (54, .jal .x1 "rlp_walk_next"),
    (78, .jal .x1 "rlp_walk_next"),
    (84, .jal .x1 "rlp_content_to_u256_be_strict"),
    (88, .jal .x1 "rlp_walk_next"),
    (97, .jal .x1 "rlp_walk_next"),
    (106, .jal .x1 "rlp_walk_next"),
    (111, .jal .x1 "rlp_content_to_u64_strict"),
    (116, .jal .x1 "rlp_walk_next"),
    (122, .jal .x1 "rlp_content_to_u256_be_strict"),
    (126, .jal .x1 "rlp_walk_next"),
    (132, .jal .x1 "rlp_content_to_u256_be_strict") ]

def txEip2930DecodeFunction : String :=
  "tx_eip2930_decode:\n" ++ emitProgramR txEip2930Decode_prog txEip2930Decode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txEip2930Decode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txEip2930DecodeFunction_eq_prog :
    txEip2930DecodeFunction = "tx_eip2930_decode:\n" ++ emitProgramR txEip2930Decode_prog txEip2930Decode_relocs := rfl

#guard txEip2930DecodeFunction.startsWith "tx_eip2930_decode:\n"
#guard txEip2930Decode_prog.length = 144
/-- `zisk_tx_eip2930_decode`: probe BuildUnit. Reads (inner_len,
    inner_bytes) from host input -- caller is expected to have
    stripped the 0x01 type byte. Writes (status, 216-byte struct)
    to OUTPUT (224 bytes total). -/
def ziskTxEip2930DecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # inner_len\n" ++
  "  addi a0, a3, 16             # inner ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 216 bytes (27 × 8 dwords).\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 27\n" ++
  ".Lt29_zinit:\n" ++
  "  beqz t1, .Lt29_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt29_zinit\n" ++
  ".Lt29_zdone:\n" ++
  "  jal ra, tx_eip2930_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lt29_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  txEip2930DecodeFunction ++ "\n" ++
  ".Lt29_pdone:"

/-- The decoder holds (cursor, end) in callee-saved registers and
    derives every content pointer arithmetically, so it needs no
    `.data` scratch. -/
def ziskTxEip2930DecodeDataSection : String := ""


end EvmAsm.Codegen
