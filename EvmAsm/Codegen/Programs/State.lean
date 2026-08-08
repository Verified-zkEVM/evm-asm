/-
  EvmAsm.Codegen.Programs.State

  Account-state ops carved out of `EvmAsm.Codegen.Programs` per
  the file-size hard cap. Hosts:

    K27  account_decode             (RLP splitter for Account)
    K28  account_at_address         (compose lookup + decode)
    K29  slot_at_index              (storage trie lookup)
    K31  account_encode             (mutating side of K27)
    K33  state_root_single_account  (end-to-end recompute)

  K27 splits the 4-field Account RLP record; K28 walks the
  state MPT via K17 + K100 and pipes the leaf through K27;
  K29 likewise walks the storage MPT and decodes a u256 slot;
  K31 encodes back; K33 recomputes the trie root for the
  single-account case.

  Depends on RLP / MPT / HashBridge submodules.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## account_decode -- PR-K27 RLP splitter for Account records

    Decode an RLP-encoded Ethereum Account (the value bytes
    that `mpt_lookup_by_key` returns for state-trie addresses)
    into four caller-supplied output slots.

    Calling convention:
      a0 (input)  : account RLP bytes ptr
      a1 (input)  : account RLP byte length
      a2 (input)  : u64 nonce out ptr (8 bytes; written LE u64)
      a3 (input)  : u256 balance out ptr (32 bytes; written BE,
                    left-zero-padded for values < 32 bytes)
      a4 (input)  : storage_root out ptr (32 bytes)
      a5 (input)  : code_hash out ptr (32 bytes)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail

    Composes PR-K20 `rlp_list_nth_item` four times. Field types
    enforced:
      * nonce / balance : variable-length BE big-int (length
                          in [0, 8] for nonce, [0, 32] for balance)
      * storage_root / code_hash : exactly 32 bytes each. -/
def accountDecode_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 68)),
    .ADDI .x13 .x13 (laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 68)),
    .AUIPC .x14 (laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 76)),
    .ADDI .x14 .x14 (laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 76)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.account_decode + 84)),
    .BNE .x10 .x0 (brOff (GuestAddrs.account_decode + 552) (GuestAddrs.account_decode + 88)),
    .AUIPC .x5 (laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 92)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 92)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 104)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 104)),
    .LD .x28 .x5 (0 : BitVec 12),
    .ADD .x28 .x8 .x28,
    .BEQ .x6 .x0 (24 : BitVec 13),
    .LBU .x29 .x28 (0 : BitVec 12),
    .BNE .x29 .x0 (16 : BitVec 13),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .LI .x7 (8 : Word),
    .BLTU .x7 .x6 (brOff (GuestAddrs.account_decode + 552) (GuestAddrs.account_decode + 148)),
    .LI .x7 (0 : Word),
    .BEQ .x6 .x0 (28 : BitVec 13),
    .SLLI .x7 .x7 (8 : BitVec 6),
    .LBU .x29 .x28 (0 : BitVec 12),
    .OR .x7 .x7 .x29,
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .SD .x18 .x7 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (1 : Word),
    .AUIPC .x13 (laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 200)),
    .ADDI .x13 .x13 (laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 200)),
    .AUIPC .x14 (laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 208)),
    .ADDI .x14 .x14 (laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 208)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.account_decode + 216)),
    .BNE .x10 .x0 (brOff (GuestAddrs.account_decode + 552) (GuestAddrs.account_decode + 220)),
    .AUIPC .x5 (laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 224)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 224)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 236)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 236)),
    .LD .x28 .x5 (0 : BitVec 12),
    .ADD .x28 .x8 .x28,
    .BEQ .x6 .x0 (24 : BitVec 13),
    .LBU .x29 .x28 (0 : BitVec 12),
    .BNE .x29 .x0 (16 : BitVec 13),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .LI .x7 (32 : Word),
    .BLTU .x7 .x6 (brOff (GuestAddrs.account_decode + 552) (GuestAddrs.account_decode + 280)),
    .SD .x19 .x0 (0 : BitVec 12),
    .SD .x19 .x0 (8 : BitVec 12),
    .SD .x19 .x0 (16 : BitVec 12),
    .SD .x19 .x0 (24 : BitVec 12),
    .SUB .x7 .x7 .x6,
    .ADD .x29 .x19 .x7,
    .BEQ .x6 .x0 (28 : BitVec 13),
    .LBU .x30 .x28 (0 : BitVec 12),
    .SB .x29 .x30 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (2 : Word),
    .AUIPC .x13 (laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 348)),
    .ADDI .x13 .x13 (laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 348)),
    .AUIPC .x14 (laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 356)),
    .ADDI .x14 .x14 (laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 356)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.account_decode + 364)),
    .BNE .x10 .x0 (brOff (GuestAddrs.account_decode + 552) (GuestAddrs.account_decode + 368)),
    .AUIPC .x5 (laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 372)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 372)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (32 : Word),
    .BNE .x6 .x7 (brOff (GuestAddrs.account_decode + 592) (GuestAddrs.account_decode + 388)),
    .AUIPC .x5 (laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 392)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 392)),
    .LD .x28 .x5 (0 : BitVec 12),
    .ADD .x28 .x8 .x28,
    .LBU .x29 .x28 (0 : BitVec 12),
    .SB .x20 .x29 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .BNE .x6 .x0 (-20 : BitVec 13),
    .NOP,
    .NOP,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (3 : Word),
    .AUIPC .x13 (laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 452)),
    .ADDI .x13 .x13 (laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 452)),
    .AUIPC .x14 (laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 460)),
    .ADDI .x14 .x14 (laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 460)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.account_decode + 468)),
    .BNE .x10 .x0 (brOff (GuestAddrs.account_decode + 552) (GuestAddrs.account_decode + 472)),
    .AUIPC .x5 (laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 476)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 476)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (32 : Word),
    .BNE .x6 .x7 (brOff (GuestAddrs.account_decode + 644) (GuestAddrs.account_decode + 492)),
    .AUIPC .x5 (laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 496)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 496)),
    .LD .x28 .x5 (0 : BitVec 12),
    .ADD .x28 .x8 .x28,
    .LBU .x29 .x28 (0 : BitVec 12),
    .SB .x21 .x29 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .BNE .x6 .x0 (-20 : BitVec 13),
    .NOP,
    .NOP,
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12),
    .BEQ .x6 .x0 (8 : BitVec 13),
    .JAL .x0 (-44 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.iw_empty_trie_root (GuestAddrs.account_decode + 600)),
    .ADDI .x5 .x5 (laLo GuestAddrs.iw_empty_trie_root (GuestAddrs.account_decode + 600)),
    .LD .x7 .x5 (0 : BitVec 12),
    .SD .x20 .x7 (0 : BitVec 12),
    .LD .x7 .x5 (8 : BitVec 12),
    .SD .x20 .x7 (8 : BitVec 12),
    .LD .x7 .x5 (16 : BitVec 12),
    .SD .x20 .x7 (16 : BitVec 12),
    .LD .x7 .x5 (24 : BitVec 12),
    .SD .x20 .x7 (24 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.account_decode + 440) (GuestAddrs.account_decode + 640)),
    .BEQ .x6 .x0 (8 : BitVec 13),
    .JAL .x0 (jalOff (GuestAddrs.account_decode + 552) (GuestAddrs.account_decode + 648)),
    .AUIPC .x5 (laHi GuestAddrs.aie_empty_code_hash (GuestAddrs.account_decode + 652)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aie_empty_code_hash (GuestAddrs.account_decode + 652)),
    .LD .x7 .x5 (0 : BitVec 12),
    .SD .x21 .x7 (0 : BitVec 12),
    .LD .x7 .x5 (8 : BitVec 12),
    .SD .x21 .x7 (8 : BitVec 12),
    .LD .x7 .x5 (16 : BitVec 12),
    .SD .x21 .x7 (16 : BitVec 12),
    .LD .x7 .x5 (24 : BitVec 12),
    .SD .x21 .x7 (24 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.account_decode + 544) (GuestAddrs.account_decode + 692)) ]

/-- Reloc side-table for `accountDecode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountDecode_relocs : RelocTable :=
  [ (17, .la .x13 "ad_offset"),
    (19, .la .x14 "ad_length"),
    (21, .jal .x1 "rlp_list_nth_item"),
    (23, .la .x5 "ad_length"),
    (26, .la .x5 "ad_offset"),
    (50, .la .x13 "ad_offset"),
    (52, .la .x14 "ad_length"),
    (54, .jal .x1 "rlp_list_nth_item"),
    (56, .la .x5 "ad_length"),
    (59, .la .x5 "ad_offset"),
    (87, .la .x13 "ad_offset"),
    (89, .la .x14 "ad_length"),
    (91, .jal .x1 "rlp_list_nth_item"),
    (93, .la .x5 "ad_length"),
    (98, .la .x5 "ad_offset"),
    (113, .la .x13 "ad_offset"),
    (115, .la .x14 "ad_length"),
    (117, .jal .x1 "rlp_list_nth_item"),
    (119, .la .x5 "ad_length"),
    (124, .la .x5 "ad_offset"),
    (150, .la .x5 "iw_empty_trie_root"),
    (163, .la .x5 "aie_empty_code_hash") ]

def accountDecodeFunction : String :=
  "account_decode:\n" ++ emitProgramR accountDecode_prog accountDecode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountDecode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountDecodeFunction_eq_prog :
    accountDecodeFunction = "account_decode:\n" ++ emitProgramR accountDecode_prog accountDecode_relocs := rfl

#guard accountDecodeFunction.startsWith "account_decode:\n"
#guard accountDecode_prog.length = 174
/-- `zisk_account_decode`: probe BuildUnit. Reads
    (account_len, account_bytes) from host input, writes
    (status, nonce, balance, storage_root, code_hash) to OUTPUT.
    Input layout:
      bytes  0.. 8 : account_len (u64)
      bytes  8..   : account RLP bytes
    Output layout:
      bytes   0.. 8 : status (u64)
      bytes   8..16 : nonce (u64 LE)
      bytes  16..48 : balance (u256 BE)
      bytes  48..80 : storage_root
      bytes  80..112: code_hash -/
def ziskAccountDecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # account_len\n" ++
  "  addi a0, a6, 16             # account ptr\n" ++
  "  li a2, 0xa0010008\n" ++
  "  li a3, 0xa0010010\n" ++
  "  li a4, 0xa0010030\n" ++
  "  li a5, 0xa0010050\n" ++
  "  # Pre-zero all outputs so a parse failure surfaces as zeros.\n" ++
  "  sd zero, 0(a2)\n" ++
  "  sd zero,  0(a3); sd zero,  8(a3); sd zero, 16(a3); sd zero, 24(a3)\n" ++
  "  sd zero,  0(a4); sd zero,  8(a4); sd zero, 16(a4); sd zero, 24(a4)\n" ++
  "  sd zero,  0(a5); sd zero,  8(a5); sd zero, 16(a5); sd zero, 24(a5)\n" ++
  "  jal ra, account_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lad_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  ".Lad_pdone:"

def ziskAccountDecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ad_offset:\n" ++
  "  .zero 8\n" ++
  "ad_length:\n" ++
  "  .zero 8"

def ziskAccountDecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountDecodePrologue
  dataAsm     := ziskAccountDecodeDataSection
}

/-! ## account_at_address -- PR-K28 compose lookup + decode

    Take a raw Ethereum address, walk the state trie, decode
    the resulting Account RLP into its four fields. The
    cleanest top-of-K-stack abstraction: caller sees only
    `(address, state_root, witness) → fields`.

    Output struct layout (104 bytes at caller-supplied ptr):
      offset  0..  8 : nonce (u64 LE)
      offset  8.. 40 : balance (u256 BE, left-zero-padded)
      offset 40.. 72 : storage_root (32 B)
      offset 72..104 : code_hash (32 B)

    Calling convention:
      a0 (input)  : address bytes ptr
      a1 (input)  : address byte length (typically 20)
      a2 (input)  : state_root ptr (32 bytes)
      a3 (input)  : witness section ptr
      a4 (input)  : witness section_len
      a5 (input)  : output struct ptr (104 bytes)
      ra (input)  : return

      a0 (output) :
        0 = found and decoded
        1 = not found in trie     (output zeroed)
        2 = mpt_walk parse error  (output zeroed)
        3 = account_decode failure (output zeroed)

    Internal:
      Step 1: mpt_lookup_by_key(addr, ..., aa_value_scratch).
      Step 2: account_decode(scratch_val, scratch_len, ...).
    Reuses the K-stack primitive scratches. -/
def accountAtAddress_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x15,
    .AUIPC .x15 (laHi GuestAddrs.aa_value_scratch (GuestAddrs.account_at_address + 20)),
    .ADDI .x15 .x15 (laLo GuestAddrs.aa_value_scratch (GuestAddrs.account_at_address + 20)),
    .AUIPC .x16 (laHi GuestAddrs.aa_value_len (GuestAddrs.account_at_address + 28)),
    .ADDI .x16 .x16 (laLo GuestAddrs.aa_value_len (GuestAddrs.account_at_address + 28)),
    .JAL .x1 (jalOff GuestAddrs.mpt_lookup_by_key (GuestAddrs.account_at_address + 36)),
    .MV .x9 .x10,
    .BEQ .x10 .x0 (64 : BitVec 13),
    .SD .x8 .x0 (0 : BitVec 12),
    .SD .x8 .x0 (8 : BitVec 12),
    .SD .x8 .x0 (16 : BitVec 12),
    .SD .x8 .x0 (24 : BitVec 12),
    .SD .x8 .x0 (32 : BitVec 12),
    .SD .x8 .x0 (40 : BitVec 12),
    .SD .x8 .x0 (48 : BitVec 12),
    .SD .x8 .x0 (56 : BitVec 12),
    .SD .x8 .x0 (64 : BitVec 12),
    .SD .x8 .x0 (72 : BitVec 12),
    .SD .x8 .x0 (80 : BitVec 12),
    .SD .x8 .x0 (88 : BitVec 12),
    .SD .x8 .x0 (96 : BitVec 12),
    .MV .x10 .x9,
    .JAL .x0 (112 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.aa_value_scratch (GuestAddrs.account_at_address + 108)),
    .ADDI .x10 .x10 (laLo GuestAddrs.aa_value_scratch (GuestAddrs.account_at_address + 108)),
    .AUIPC .x5 (laHi GuestAddrs.aa_value_len (GuestAddrs.account_at_address + 116)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aa_value_len (GuestAddrs.account_at_address + 116)),
    .LD .x11 .x5 (0 : BitVec 12),
    .MV .x12 .x8,
    .ADDI .x13 .x8 (8 : BitVec 12),
    .ADDI .x14 .x8 (40 : BitVec 12),
    .ADDI .x15 .x8 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.account_decode (GuestAddrs.account_at_address + 144)),
    .BEQ .x10 .x0 (64 : BitVec 13),
    .SD .x8 .x0 (0 : BitVec 12),
    .SD .x8 .x0 (8 : BitVec 12),
    .SD .x8 .x0 (16 : BitVec 12),
    .SD .x8 .x0 (24 : BitVec 12),
    .SD .x8 .x0 (32 : BitVec 12),
    .SD .x8 .x0 (40 : BitVec 12),
    .SD .x8 .x0 (48 : BitVec 12),
    .SD .x8 .x0 (56 : BitVec 12),
    .SD .x8 .x0 (64 : BitVec 12),
    .SD .x8 .x0 (72 : BitVec 12),
    .SD .x8 .x0 (80 : BitVec 12),
    .SD .x8 .x0 (88 : BitVec 12),
    .SD .x8 .x0 (96 : BitVec 12),
    .LI .x10 (3 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountAtAddress_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountAtAddress_relocs : RelocTable :=
  [ (5, .la .x15 "aa_value_scratch"),
    (7, .la .x16 "aa_value_len"),
    (9, .jal .x1 "mpt_lookup_by_key"),
    (27, .la .x10 "aa_value_scratch"),
    (29, .la .x5 "aa_value_len"),
    (36, .jal .x1 "account_decode") ]

def accountAtAddressFunction : String :=
  "account_at_address:\n" ++ emitProgramR accountAtAddress_prog accountAtAddress_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountAtAddress_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountAtAddressFunction_eq_prog :
    accountAtAddressFunction = "account_at_address:\n" ++ emitProgramR accountAtAddress_prog accountAtAddress_relocs := rfl

#guard accountAtAddressFunction.startsWith "account_at_address:\n"
#guard accountAtAddress_prog.length = 59
/-- `zisk_account_at_address`: probe BuildUnit. Reads
    (witness_len, addr_len, state_root, addr, witness) from
    host input. Writes (status, nonce, balance, storage_root,
    code_hash) to OUTPUT.
    Output layout:
      bytes   0.. 8 : status
      bytes   8..16 : nonce
      bytes  16..48 : balance
      bytes  48..80 : storage_root
      bytes  80..112: code_hash -/
def ziskAccountAtAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # witness_len\n" ++
  "  ld t5, 16(a7)               # addr_len\n" ++
  "  addi a2, a7, 24             # state_root ptr\n" ++
  "  addi a0, a7, 56             # address ptr\n" ++
  "  mv a1, t5                   # addr_len\n" ++
  "  add a3, a0, t5              # witness ptr = address + addr_len\n" ++
  "  mv a4, t6                   # witness_len\n" ++
  "  li a5, 0xa0010008           # output struct at OUTPUT + 8\n" ++
  "  # Pre-zero 104 bytes of output struct so a failure surfaces as zeros.\n" ++
  "  sd zero, 0(a5); sd zero, 8(a5); sd zero, 16(a5); sd zero, 24(a5)\n" ++
  "  sd zero, 32(a5); sd zero, 40(a5); sd zero, 48(a5); sd zero, 56(a5)\n" ++
  "  sd zero, 64(a5); sd zero, 72(a5); sd zero, 80(a5); sd zero, 88(a5)\n" ++
  "  sd zero, 96(a5)\n" ++
  "  jal ra, account_at_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Laa_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  accountAtAddressFunction ++ "\n" ++
  ".Laa_pdone:"

def ziskAccountAtAddressDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_lookup_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_lookup_offset:\n" ++
  "  .zero 8\n" ++
  "mw_lookup_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_child_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_path_offset:\n" ++
  "  .zero 8\n" ++
  "mw_path_length:\n" ++
  "  .zero 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 32\n" ++
  "mlk_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "mlk_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "ad_offset:\n" ++
  "  .zero 8\n" ++
  "ad_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aa_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aa_value_scratch:\n" ++
  "  .zero 256"

def ziskAccountAtAddressProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountAtAddressPrologue
  dataAsm     := ziskAccountAtAddressDataSection
}

/-! ## slot_at_index -- PR-K29 storage trie lookup

    Storage-trie counterpart to `account_at_address`. Takes a
    32-byte slot index (big-endian u256) and walks the
    per-account storage trie, decoding the looked-up value as
    a u256.

    Per `execution-specs/.../trie.py::encode_node`, the value
    stored in the storage trie is `rlp.encode(slot_value:U256)`
    -- one RLP layer on top of the canonical leading-zero-
    stripped big-int. `mpt_walk` strips the leaf's outer item-1
    string prefix (one layer), so the value bytes we receive
    are exactly `rlp.encode(slot_value)`. We then apply one
    more layer of RLP decoding to recover the u256.

    Encoding cheat-sheet for slot values:
      slot_value = 0          → 0x80         (RLP empty)
      slot_value = 1          → 0x01         (single byte)
      slot_value = 0x7f       → 0x7f
      slot_value = 0x80       → 0x81 0x80    (1-byte string)
      slot_value = 0x0100     → 0x82 0x01 0x00 (2-byte string)
      slot_value = 2^256 - 1  → 0xa0 + 32 × 0xff

    Calling convention:
      a0 (input)  : slot_idx bytes ptr (32-byte big-endian u256)
      a1 (input)  : slot_idx byte length (typically 32)
      a2 (input)  : storage_root ptr (32 bytes)
      a3 (input)  : witness section ptr
      a4 (input)  : witness section_len
      a5 (input)  : output u256 BE ptr (32 bytes)
      ra (input)  : return

      a0 (output) :
        0 found and decoded
        1 not found (output zeroed)
        2 mpt_walk parse error (output zeroed)
        3 RLP-u256 decode failure (output zeroed)

    Internal: `mpt_lookup_by_key(slot_idx, ..., si_value_scratch)`
    then `slot_decode_u256` over the looked-up bytes. -/
def slotDecodeU256_prog : Program :=
  [ .SD .x12 .x0 (0 : BitVec 12),
    .SD .x12 .x0 (8 : BitVec 12),
    .SD .x12 .x0 (16 : BitVec 12),
    .SD .x12 .x0 (24 : BitVec 12),
    .BEQ .x11 .x0 (104 : BitVec 13),
    .LBU .x5 .x10 (0 : BitVec 12),
    .LI .x6 (128 : Word),
    .BLTU .x5 .x6 (80 : BitVec 13),
    .BEQ .x5 .x6 (80 : BitVec 13),
    .LI .x6 (161 : Word),
    .BGEU .x5 .x6 (80 : BitVec 13),
    .LI .x6 (128 : Word),
    .SUB .x7 .x5 .x6,
    .ADDI .x28 .x11 (-1 : BitVec 12),
    .BLTU .x28 .x7 (64 : BitVec 13),
    .LI .x29 (32 : Word),
    .SUB .x29 .x29 .x7,
    .ADD .x30 .x12 .x29,
    .ADDI .x31 .x10 (1 : BitVec 12),
    .MV .x28 .x7,
    .BEQ .x28 .x0 (32 : BitVec 13),
    .LBU .x6 .x31 (0 : BitVec 12),
    .SB .x30 .x6 (0 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .ADDI .x31 .x31 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .SB .x12 .x5 (31 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def slotDecodeU256Function : String :=
  "slot_decode_u256:\n" ++ emitProgram slotDecodeU256_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `slotDecodeU256_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem slotDecodeU256Function_eq_prog :
    slotDecodeU256Function = "slot_decode_u256:\n" ++ emitProgram slotDecodeU256_prog := rfl

#guard slotDecodeU256Function.startsWith "slot_decode_u256:\n"
#guard slotDecodeU256_prog.length = 32
def slotAtIndex_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x15,
    .AUIPC .x15 (laHi GuestAddrs.si_value_scratch (GuestAddrs.slot_at_index + 20)),
    .ADDI .x15 .x15 (laLo GuestAddrs.si_value_scratch (GuestAddrs.slot_at_index + 20)),
    .AUIPC .x16 (laHi GuestAddrs.si_value_len (GuestAddrs.slot_at_index + 28)),
    .ADDI .x16 .x16 (laLo GuestAddrs.si_value_len (GuestAddrs.slot_at_index + 28)),
    .JAL .x1 (jalOff GuestAddrs.mpt_lookup_by_key (GuestAddrs.slot_at_index + 36)),
    .MV .x9 .x10,
    .BEQ .x10 .x0 (28 : BitVec 13),
    .SD .x8 .x0 (0 : BitVec 12),
    .SD .x8 .x0 (8 : BitVec 12),
    .SD .x8 .x0 (16 : BitVec 12),
    .SD .x8 .x0 (24 : BitVec 12),
    .MV .x10 .x9,
    .JAL .x0 (64 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.si_value_scratch (GuestAddrs.slot_at_index + 72)),
    .ADDI .x10 .x10 (laLo GuestAddrs.si_value_scratch (GuestAddrs.slot_at_index + 72)),
    .AUIPC .x5 (laHi GuestAddrs.si_value_len (GuestAddrs.slot_at_index + 80)),
    .ADDI .x5 .x5 (laLo GuestAddrs.si_value_len (GuestAddrs.slot_at_index + 80)),
    .LD .x11 .x5 (0 : BitVec 12),
    .MV .x12 .x8,
    .JAL .x1 (jalOff GuestAddrs.slot_decode_u256 (GuestAddrs.slot_at_index + 96)),
    .BEQ .x10 .x0 (28 : BitVec 13),
    .SD .x8 .x0 (0 : BitVec 12),
    .SD .x8 .x0 (8 : BitVec 12),
    .SD .x8 .x0 (16 : BitVec 12),
    .SD .x8 .x0 (24 : BitVec 12),
    .LI .x10 (3 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `slotAtIndex_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def slotAtIndex_relocs : RelocTable :=
  [ (5, .la .x15 "si_value_scratch"),
    (7, .la .x16 "si_value_len"),
    (9, .jal .x1 "mpt_lookup_by_key"),
    (18, .la .x10 "si_value_scratch"),
    (20, .la .x5 "si_value_len"),
    (24, .jal .x1 "slot_decode_u256") ]

def slotAtIndexFunction : String :=
  "slot_at_index:\n" ++ emitProgramR slotAtIndex_prog slotAtIndex_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `slotAtIndex_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem slotAtIndexFunction_eq_prog :
    slotAtIndexFunction = "slot_at_index:\n" ++ emitProgramR slotAtIndex_prog slotAtIndex_relocs := rfl

#guard slotAtIndexFunction.startsWith "slot_at_index:\n"
#guard slotAtIndex_prog.length = 38
/-- `zisk_slot_at_index`: probe BuildUnit. Reads
    (witness_len, slot_len, storage_root, slot_idx, witness)
    from host input. Writes (status, u256) to OUTPUT. -/
def ziskSlotAtIndexPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # witness_len\n" ++
  "  ld t5, 16(a7)               # slot_len\n" ++
  "  addi a2, a7, 24             # storage_root ptr\n" ++
  "  addi a0, a7, 56             # slot_idx ptr\n" ++
  "  mv a1, t5                   # slot_len\n" ++
  "  add a3, a0, t5              # witness ptr = slot_idx + slot_len\n" ++
  "  mv a4, t6                   # witness_len\n" ++
  "  li a5, 0xa0010008           # u256 out at OUTPUT + 8\n" ++
  "  sd zero, 0(a5); sd zero, 8(a5); sd zero, 16(a5); sd zero, 24(a5)\n" ++
  "  jal ra, slot_at_index\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsi_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  slotDecodeU256Function ++ "\n" ++
  slotAtIndexFunction ++ "\n" ++
  ".Lsi_pdone:"

def ziskSlotAtIndexDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_lookup_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_lookup_offset:\n" ++
  "  .zero 8\n" ++
  "mw_lookup_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_child_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_path_offset:\n" ++
  "  .zero 8\n" ++
  "mw_path_length:\n" ++
  "  .zero 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 32\n" ++
  "mlk_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "mlk_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "si_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "si_value_scratch:\n" ++
  "  .zero 256"

def ziskSlotAtIndexProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSlotAtIndexPrologue
  dataAsm     := ziskSlotAtIndexDataSection
}

/-- `zisk_rlp_encode_uint_be`: probe BuildUnit. Reads
    (src_len, src_bytes) from host input, writes
    (bytes_written, encoded_bytes) to OUTPUT. -/
def ziskRlpEncodeUintBePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # src_len\n" ++
  "  addi a0, a3, 16             # src ptr\n" ++
  "  li a2, 0xa0010008           # output at OUTPUT + 8\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # bytes_written at OUTPUT + 0\n" ++
  "  j .Lreu_pdone\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  ".Lreu_pdone:"

def ziskRlpEncodeUintBeDataSection : String :=
  ".section .data\n" ++
  "reu_pad:\n" ++
  "  .zero 8"

def ziskRlpEncodeUintBeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpEncodeUintBePrologue
  dataAsm     := ziskRlpEncodeUintBeDataSection
}

/-! ## K128 rlp_encode_bytes — moved to `Programs/RlpRead.lean` (file-size hard cap). -/

/-! ## rlp_encode_list_prefix -- PR-K129 — def moved to `Programs/RlpRead.lean`. -/


/-- `zisk_rlp_encode_list_prefix`: probe BuildUnit. Reads
    (payload_length,) from host input, writes (status, out_len,
    prefix_bytes...) to OUTPUT. -/
def ziskRlpEncodeListPrefixPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a0, 8(a3)                # payload_length\n" ++
  "  li a1, 0xa0010010           # out bytes\n" ++
  "  li a2, 0xa0010008           # out_len out\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lrelp_pdone\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  ".Lrelp_pdone:"

def ziskRlpEncodeListPrefixDataSection : String :=
  ".section .data\n" ++
  "relp_scratch:\n" ++
  "  .zero 8"

def ziskRlpEncodeListPrefixProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpEncodeListPrefixPrologue
  dataAsm     := ziskRlpEncodeListPrefixDataSection
}

/-! ## K130 withdrawal_rlp_encode / K132 withdrawal_compute_hash — moved to `Programs/Withdrawal.lean` (file-size hard cap). -/


/-! ## account_encode -- PR-K31 mutating side of account_decode

    Encode (nonce, balance, storage_root, code_hash) into the
    canonical 4-field RLP list bytes used as the value of a
    state-trie leaf node. The inverse of PR-K27 account_decode.

    Composition:
      payload = rlp_encode_uint_be(nonce_be, 8) +
                rlp_encode_uint_be(balance_be, 32) +
                0xa0 + storage_root +
                0xa0 + code_hash
      out = 0xf8 + len(payload) + payload

    The 0xf8 prefix is correct because the payload is always
    > 55 bytes (storage_root + code_hash already total 66 bytes,
    plus at least 2 bytes for nonce/balance encodings).

    Calling convention:
      a0 (input)  : nonce 8-byte BE ptr
      a1 (input)  : balance 32-byte BE ptr
      a2 (input)  : storage_root ptr (32 bytes)
      a3 (input)  : code_hash ptr (32 bytes)
      a4 (input)  : output buffer ptr (≥ 128 bytes)
      a5 (input)  : u64 out ptr (bytes_written)
      ra (input)  : return
      a0 (output) : 0 (always success; cap fixed by caller)

    Scratch: ae_scratch (64 bytes) for staging nonce_rlp +
    balance_rlp before they're copied to the output buffer. -/
def accountEncodeFunction : String :=
  "account_encode:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # nonce_be ptr\n" ++
  "  mv s1, a1                   # balance_be ptr\n" ++
  "  mv s2, a2                   # storage_root ptr\n" ++
  "  mv s3, a3                   # code_hash ptr\n" ++
  "  mv s4, a4                   # output buf\n" ++
  "  mv s5, a5                   # bytes_written out\n" ++
  "  # Step 1: rlp_encode_uint_be(nonce_be, 8) → ae_scratch.\n" ++
  "  mv a0, s0\n" ++
  "  li a1, 8\n" ++
  "  la a2, ae_scratch\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  la t0, ae_nonce_len; sd a0, 0(t0)\n" ++
  "  # Step 2: rlp_encode_uint_be(balance_be, 32) → ae_scratch + nonce_len.\n" ++
  "  la t0, ae_nonce_len; ld t1, 0(t0)\n" ++
  "  la t2, ae_scratch\n" ++
  "  add a2, t2, t1\n" ++
  "  mv a0, s1\n" ++
  "  li a1, 32\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  la t0, ae_balance_len; sd a0, 0(t0)\n" ++
  "  # Step 3: payload_len = nonce_len + balance_len + 33 + 33.\n" ++
  "  la t0, ae_nonce_len; ld t1, 0(t0)\n" ++
  "  la t0, ae_balance_len; ld t2, 0(t0)\n" ++
  "  add t3, t1, t2\n" ++
  "  addi t3, t3, 66            # + 33 + 33 (storage_root + code_hash)\n" ++
  "  # Step 4: write outer prefix 0xf8 + payload_len.\n" ++
  "  mv t4, s4                  # cursor\n" ++
  "  li t5, 0xf8\n" ++
  "  sb t5, 0(t4)\n" ++
  "  sb t3, 1(t4)\n" ++
  "  addi t4, t4, 2\n" ++
  "  # Step 5: copy nonce_rlp (t1 bytes) from ae_scratch to t4.\n" ++
  "  la t5, ae_scratch\n" ++
  "  mv t6, t1                  # remaining\n" ++
  ".Lae_copy_nonce:\n" ++
  "  beqz t6, .Lae_copy_balance_init\n" ++
  "  lbu t1, 0(t5)\n" ++
  "  sb  t1, 0(t4)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t6, t6, -1\n" ++
  "  j .Lae_copy_nonce\n" ++
  ".Lae_copy_balance_init:\n" ++
  "  # Step 6: copy balance_rlp from ae_scratch + nonce_len. t5 is already there.\n" ++
  "  la t0, ae_balance_len; ld t6, 0(t0)\n" ++
  ".Lae_copy_balance:\n" ++
  "  beqz t6, .Lae_copy_storage_root\n" ++
  "  lbu t1, 0(t5)\n" ++
  "  sb  t1, 0(t4)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t6, t6, -1\n" ++
  "  j .Lae_copy_balance\n" ++
  ".Lae_copy_storage_root:\n" ++
  "  # Step 7: write 0xa0 + storage_root (32 bytes).\n" ++
  "  li t5, 0xa0\n" ++
  "  sb t5, 0(t4)\n" ++
  "  addi t4, t4, 1\n" ++
  "  ld t5,  0(s2); sd t5,  0(t4)\n" ++
  "  ld t5,  8(s2); sd t5,  8(t4)\n" ++
  "  ld t5, 16(s2); sd t5, 16(t4)\n" ++
  "  ld t5, 24(s2); sd t5, 24(t4)\n" ++
  "  addi t4, t4, 32\n" ++
  "  # Step 8: write 0xa0 + code_hash.\n" ++
  "  li t5, 0xa0\n" ++
  "  sb t5, 0(t4)\n" ++
  "  addi t4, t4, 1\n" ++
  "  ld t5,  0(s3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(s3); sd t5,  8(t4)\n" ++
  "  ld t5, 16(s3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(s3); sd t5, 24(t4)\n" ++
  "  addi t4, t4, 32\n" ++
  "  # bytes_written = (t4 - s4)\n" ++
  "  sub t4, t4, s4\n" ++
  "  sd t4, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_account_encode`: probe BuildUnit. Reads
    (nonce_be8, balance_be32, storage_root, code_hash) from
    host input (104 bytes total). Writes (bytes_written, RLP)
    to OUTPUT.
    Input layout:
      bytes  0.. 8 : nonce (8-byte BE)
      bytes  8..40 : balance (32-byte BE)
      bytes 40..72 : storage_root (32 B)
      bytes 72..104: code_hash (32 B) -/
def ziskAccountEncodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  addi a0, a6, 8              # nonce_be\n" ++
  "  addi a1, a6, 16             # balance_be\n" ++
  "  addi a2, a6, 48             # storage_root\n" ++
  "  addi a3, a6, 80             # code_hash\n" ++
  "  li a4, 0xa0010008           # output RLP at OUTPUT + 8\n" ++
  "  li a5, 0xa0010000           # bytes_written at OUTPUT + 0\n" ++
  "  jal ra, account_encode\n" ++
  "  j .Lae_pdone\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  accountEncodeFunction ++ "\n" ++
  ".Lae_pdone:"

def ziskAccountEncodeDataSection : String :=
  ".section .data\n" ++
  -- #11522: these three are `.globl` so `scripts/asm_to_program.py` can resolve the
  -- `la` targets in `account_encode`. Without them the mechanical converter refuses
  -- the routine ("symbol not in address table"), which forces a HAND conversion --
  -- and hand conversion is what produced #11518 (reversed SD operands) and #11519
  -- (laLo anchored at the wrong PC). `.globl` on a data label changes the SYMBOL
  -- TABLE only, never `.text`, so the byte-identity gates are unaffected.
  ".globl ae_nonce_len\n" ++
  ".globl ae_balance_len\n" ++
  ".globl ae_scratch\n" ++
  ".balign 8\n" ++
  "ae_nonce_len:\n" ++
  "  .zero 8\n" ++
  "ae_balance_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "ae_scratch:\n" ++
  "  .zero 64"

def ziskAccountEncodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountEncodePrologue
  dataAsm     := ziskAccountEncodeDataSection
}

/-! ## K32 hp_encode_nibbles — moved to `Programs/Mpt.lean` (file-size hard cap). -/

/-! ## state_root_single_account -- PR-K33 end-to-end recompute

    Compute the state-trie root for a trie containing exactly
    one account. Composes every mutating primitive shipped so
    far:

      keccak(address)                       (PR-K3)
      bytes_to_nibbles → 64-nibble path     (PR-K25)
      hp_encode_nibbles(path, leaf=true)    (PR-K32)
      account_encode(nonce, balance,
                     storage_root,
                     code_hash)             (PR-K31)
      leaf_rlp = rlp([hp_bytes, account_rlp_bytes])
      state_root = keccak(leaf_rlp)

    This is the smallest useful "compute state_root from
    fields" operation. Future PRs scale to multi-account tries
    by composing branch / extension node builders on top.

    Calling convention:
      a0 (input)  : address bytes ptr
      a1 (input)  : address byte length (typically 20)
      a2 (input)  : nonce 8-byte BE ptr
      a3 (input)  : balance 32-byte BE ptr
      a4 (input)  : storage_root ptr (32 bytes)
      a5 (input)  : code_hash ptr (32 bytes)
      a6 (input)  : state_root output ptr (32 bytes)
      ra (input)  : return
      a0 (output) : 0 success

    Reuses K-stack primitive functions. New scratches:
      srsa_keccak_buf  (32 B)
      srsa_nibble_buf  (64 B)
      srsa_hp_buf      (33 B)  -- 64-nibble path HP-encodes to 33 bytes
      srsa_acc_buf     (128 B) -- account RLP, typically 70..104 B
      srsa_acc_len     (8 B)
      srsa_leaf_buf    (256 B) -- leaf RLP -/
def stateRootSingleAccountFunction : String :=
  "state_root_single_account:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a2                   # nonce_be ptr\n" ++
  "  mv s1, a3                   # balance_be ptr\n" ++
  "  mv s2, a4                   # storage_root ptr\n" ++
  "  mv s3, a5                   # code_hash ptr\n" ++
  "  mv s4, a6                   # state_root output ptr\n" ++
  "  # Step 1: keccak(address) → srsa_keccak_buf.\n" ++
  "  la a2, srsa_keccak_buf\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Step 2: bytes_to_nibbles → srsa_nibble_buf (64 nibbles).\n" ++
  "  la a0, srsa_keccak_buf\n" ++
  "  li a1, 32\n" ++
  "  la a2, srsa_nibble_buf\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  # Step 3: hp_encode → srsa_hp_buf (33 bytes for 64-nibble leaf).\n" ++
  "  la a0, srsa_nibble_buf\n" ++
  "  li a1, 64\n" ++
  "  li a2, 1\n" ++
  "  la a3, srsa_hp_buf\n" ++
  "  jal ra, hp_encode_nibbles\n" ++
  "  # Step 4: account_encode → srsa_acc_buf.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s2\n" ++
  "  mv a3, s3\n" ++
  "  la a4, srsa_acc_buf\n" ++
  "  la a5, srsa_acc_len\n" ++
  "  jal ra, account_encode\n" ++
  "  # Step 5: build leaf RLP at srsa_leaf_buf.\n" ++
  "  la t0, srsa_acc_len; ld t1, 0(t0)\n" ++
  "  # payload_len = 34 (hp) + (1 or 2) prefix + acc_len\n" ++
  "  # For acc_len ≥ 56: acc prefix = 2 bytes (0xb8 + len). 0xa1 + 33 hp = 34. Total 34 + 2 + acc_len.\n" ++
  "  li t2, 56\n" ++
  "  bltu t1, t2, .Lsrsa_acc_short\n" ++
  "  addi t2, t1, 36              # payload = 34 + 2 + acc_len\n" ++
  "  j .Lsrsa_have_payload\n" ++
  ".Lsrsa_acc_short:\n" ++
  "  addi t2, t1, 35              # payload = 34 + 1 + acc_len\n" ++
  ".Lsrsa_have_payload:\n" ++
  "  # Write outer prefix: 0xf8 + payload_len.\n" ++
  "  la t3, srsa_leaf_buf\n" ++
  "  li t4, 0xf8\n" ++
  "  sb t4, 0(t3)\n" ++
  "  sb t2, 1(t3)\n" ++
  "  addi t3, t3, 2\n" ++
  "  # Write 0xa1 + 33 hp bytes.\n" ++
  "  li t4, 0xa1\n" ++
  "  sb t4, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  la t5, srsa_hp_buf\n" ++
  "  li t6, 33\n" ++
  ".Lsrsa_copy_hp:\n" ++
  "  beqz t6, .Lsrsa_hp_done\n" ++
  "  lbu t4, 0(t5)\n" ++
  "  sb  t4, 0(t3)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t6, t6, -1\n" ++
  "  j .Lsrsa_copy_hp\n" ++
  ".Lsrsa_hp_done:\n" ++
  "  # Write account_rlp prefix.\n" ++
  "  li t4, 56\n" ++
  "  bltu t1, t4, .Lsrsa_acc_short_pfx\n" ++
  "  li t4, 0xb8\n" ++
  "  sb t4, 0(t3)\n" ++
  "  sb t1, 1(t3)\n" ++
  "  addi t3, t3, 2\n" ++
  "  j .Lsrsa_acc_copy\n" ++
  ".Lsrsa_acc_short_pfx:\n" ++
  "  li t4, 0x80\n" ++
  "  add t4, t4, t1\n" ++
  "  sb t4, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  ".Lsrsa_acc_copy:\n" ++
  "  la t5, srsa_acc_buf\n" ++
  "  mv t6, t1\n" ++
  ".Lsrsa_copy_acc:\n" ++
  "  beqz t6, .Lsrsa_acc_done\n" ++
  "  lbu t4, 0(t5)\n" ++
  "  sb  t4, 0(t3)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t6, t6, -1\n" ++
  "  j .Lsrsa_copy_acc\n" ++
  ".Lsrsa_acc_done:\n" ++
  "  # leaf_len = t3 - srsa_leaf_buf; keccak the leaf into s4.\n" ++
  "  la t5, srsa_leaf_buf\n" ++
  "  sub a1, t3, t5\n" ++
  "  mv a0, t5\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_state_root_single_account`: probe BuildUnit. Reads
    (addr_len, address, nonce_be, balance_be, storage_root,
     code_hash) from host input, writes the 32-byte state_root
    to OUTPUT. -/
def ziskStateRootSingleAccountPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # addr_len\n" ++
  "  addi a0, a7, 16             # addr ptr\n" ++
  "  mv a1, t6\n" ++
  "  add a2, a0, t6              # nonce_be at addr + addr_len\n" ++
  "  addi a3, a2, 8              # balance_be at +8\n" ++
  "  addi a4, a3, 32             # storage_root at +32\n" ++
  "  addi a5, a4, 32             # code_hash at +32\n" ++
  "  li a6, 0xa0010000           # state_root out at OUTPUT + 0\n" ++
  "  jal ra, state_root_single_account\n" ++
  "  j .Lsrsa_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  accountEncodeFunction ++ "\n" ++
  stateRootSingleAccountFunction ++ "\n" ++
  ".Lsrsa_pdone:"

def ziskStateRootSingleAccountDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "srsa_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "srsa_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "srsa_hp_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "srsa_acc_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 8\n" ++
  "srsa_acc_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "ae_nonce_len:\n" ++
  "  .zero 8\n" ++
  "ae_balance_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "ae_scratch:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "srsa_leaf_buf:\n" ++
  "  .zero 256"

def ziskStateRootSingleAccountProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStateRootSingleAccountPrologue
  dataAsm     := ziskStateRootSingleAccountDataSection
}

end EvmAsm.Codegen
