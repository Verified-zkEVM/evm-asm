/-
  EvmAsm.Codegen.Programs.MptIndexedTrieRoot

  Build an MPT root from an indexed list of values by inserting keys
  rlp(0), rlp(1), ... from an initially empty trie. The generic path supports
  indices 0..255 and delegates the trie mutation work to the existing
  insert-aware state-root driver.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.MptStateRootIns

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## mpt_indexed_trie_root_small -- indexed trie builder for indices <= 255

    a0 = value descriptor array ptr, entries `{ptr:u64, len:u64}`
    a1 = number of values, must be <= 256
    a2 = out root ptr
    a0 (output) = 0 ok / 1 too many values / sub-status from mpt_state_root_ins.

    Each key is encoded as the nibble path of RLP(index):
      index 0    -> RLP 0x80 -> nibbles [8,0]
      index 1..127 -> single byte -> nibbles [hi,lo]
      index 128..255 -> bytes 0x81 index -> nibbles [8,1,hi,lo]
-/

/-! ## mpt_indexed_trie_root_one_leaf -- streaming one-leaf transaction trie root

    Specialized path for the common EIP-7934 boundary case where the transaction
    trie has exactly one value. The general MPT insertion path materializes the
    whole leaf node in a fixed 16 KiB scratch buffer; this helper only buffers
    the small RLP prefixes and absorbs the large transaction bytes directly into
    keccak.

    a0 = value ptr, a1 = value len, a2 = out root ptr; returns a0 = 0. -/
def mptIndexedTrieRootOneLeafFunction : String :=
  "mpt_indexed_trie_root_one_leaf:\n" ++
  "  addi sp, sp, -120\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s1, a0                   # value ptr\n" ++
  "  mv s2, a1                   # value len\n" ++
  "  mv s3, a2                   # out root\n" ++
  "  la s0, zk3_state\n" ++
  "  mv t0, s0; li t1, 25\n" ++
  ".Litol_zero:\n" ++
  "  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1; bnez t1, .Litol_zero\n" ++
  "  li s4, 0                    # current keccak rate offset\n" ++
  "  # Build the RLP encoding prefixes for leaf([8,0], value).\n" ++
  "  li t0, 1\n" ++
  "  bne s2, t0, .Litol_value_has_prefix\n" ++
  "  lbu t1, 0(s1)\n" ++
  "  li t2, 128\n" ++
  "  bltu t1, t2, .Litol_value_single_byte\n" ++
  ".Litol_value_has_prefix:\n" ++
  "  li a0, 0x80\n" ++
  "  mv a1, s2\n" ++
  "  addi a2, sp, 88             # value prefix scratch\n" ++
  "  jal ra, rlp_prefix_to_buffer\n" ++
  "  mv s5, a0                   # value prefix len\n" ++
  "  add s6, s5, s2              # encoded value item len\n" ++
  "  j .Litol_value_len_done\n" ++
  ".Litol_value_single_byte:\n" ++
  "  li s5, 0                    # no RLP string prefix\n" ++
  "  mv s6, s2                   # encoded value item len = 1\n" ++
  ".Litol_value_len_done:\n" ++
  "  addi a1, s6, 3              # list payload: hp item (3) + value item\n" ++
  "  li a0, 0xc0\n" ++
  "  addi a2, sp, 104            # list prefix scratch\n" ++
  "  jal ra, rlp_prefix_to_buffer\n" ++
  "  mv s7, a0                   # list prefix len\n" ++
  "  addi t0, sp, 112            # hp item scratch\n" ++
  "  li t1, 0x82; sb t1, 0(t0)\n" ++
  "  li t1, 0x20; sb t1, 1(t0)\n" ++
  "  li t1, 0x80; sb t1, 2(t0)\n" ++
  "  addi a0, sp, 104; mv a1, s7; jal ra, .Litol_absorb\n" ++
  "  addi a0, sp, 112; li a1, 3; jal ra, .Litol_absorb\n" ++
  "  beqz s5, .Litol_absorb_value\n" ++
  "  addi a0, sp, 88; mv a1, s5; jal ra, .Litol_absorb\n" ++
  ".Litol_absorb_value:\n" ++
  "  mv a0, s1; mv a1, s2; jal ra, .Litol_absorb\n" ++
  "  # keccak padding at the current rate offset.\n" ++
  "  add t0, s0, s4\n" ++
  "  lbu t1, 0(t0); xori t1, t1, 0x01; sb t1, 0(t0)\n" ++
  "  addi t0, s0, 135\n" ++
  "  lbu t1, 0(t0); xori t1, t1, 0x80; sb t1, 0(t0)\n" ++
  "  mv a0, s0\n" ++
  "  .4byte 0x80052073\n" ++
  "  ld t0,  0(s0); sd t0,  0(s3)\n" ++
  "  ld t0,  8(s0); sd t0,  8(s3)\n" ++
  "  ld t0, 16(s0); sd t0, 16(s3)\n" ++
  "  ld t0, 24(s0); sd t0, 24(s3)\n" ++
  "  li a0, 0\n" ++
  ".Litol_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 120\n" ++
  "  ret\n" ++
  "  # Absorb a0/a1 bytes into zk3_state using LBU so unaligned SSZ values are OK.\n" ++
  ".Litol_absorb:\n" ++
  "  mv s8, a0\n" ++
  "  mv s9, a1\n" ++
  ".Litol_absorb_loop:\n" ++
  "  beqz s9, .Litol_absorb_ret\n" ++
  "  lbu t0, 0(s8)\n" ++
  "  add t1, s0, s4\n" ++
  "  lbu t2, 0(t1)\n" ++
  "  xor t2, t2, t0\n" ++
  "  sb t2, 0(t1)\n" ++
  "  addi s8, s8, 1\n" ++
  "  addi s9, s9, -1\n" ++
  "  addi s4, s4, 1\n" ++
  "  li t3, 136\n" ++
  "  bne s4, t3, .Litol_absorb_loop\n" ++
  "  mv a0, s0\n" ++
  "  .4byte 0x80052073\n" ++
  "  li s4, 0\n" ++
  "  j .Litol_absorb_loop\n" ++
  ".Litol_absorb_ret:\n" ++
  "  ret\n" ++
  "  # rlp_prefix_to_buffer(base, len, out): base is 0x80 or 0xc0.\n" ++
  "rlp_prefix_to_buffer:\n" ++
  "  li t0, 55\n" ++
  "  bgtu a1, t0, .Lrptb_long\n" ++
  "  add t1, a0, a1\n" ++
  "  sb t1, 0(a2)\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lrptb_long:\n" ++
  "  mv t0, a1\n" ++
  "  li t1, 0                    # len(len)\n" ++
  ".Lrptb_count:\n" ++
  "  addi t1, t1, 1\n" ++
  "  srli t0, t0, 8\n" ++
  "  bnez t0, .Lrptb_count\n" ++
  "  addi t2, a0, 55\n" ++
  "  add t2, t2, t1\n" ++
  "  sb t2, 0(a2)\n" ++
  "  li t2, 0                    # output byte index\n" ++
  ".Lrptb_store:\n" ++
  "  beq t2, t1, .Lrptb_done\n" ++
  "  sub t3, t1, t2\n" ++
  "  addi t3, t3, -1\n" ++
  "  slli t3, t3, 3\n" ++
  "  srl t4, a1, t3\n" ++
  "  andi t4, t4, 255\n" ++
  "  add t5, a2, t2\n" ++
  "  sb t4, 1(t5)\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lrptb_store\n" ++
  ".Lrptb_done:\n" ++
  "  addi a0, t1, 1\n" ++
  "  ret"


/-! ## mpt_indexed_large_leaf_hash -- streaming large-value leaf node hash

    Compute `keccak(rlp([hp_path, value]))` for large indexed-trie leaves
    without materializing the full leaf node. This helper is intended for
    branch slots that will use `0xa0 || hash`, so it deliberately accepts only
    values whose RLP item is already large.

    a0 = value ptr, a1 = value len, a2 = path kind (0 empty, 1 one nibble),
    a3 = low nibble when kind=1, a4 = out hash ptr.
    Returns a0 = 0 ok / 1 unsupported small value or bad path kind. -/
def mptIndexedLargeLeafHash_prog : Program :=
  [ .ADDI .x2 .x2 (-144 : BitVec 12),
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
    .SD .x2 .x25 (80 : BitVec 12),
    .SD .x2 .x26 (88 : BitVec 12),
    .SD .x2 .x27 (96 : BitVec 12),
    .MV .x9 .x10,
    .MV .x18 .x11,
    .MV .x19 .x12,
    .MV .x20 .x13,
    .MV .x21 .x14,
    .LI .x5 (56 : Word),
    .BLTU .x18 .x5 (252 : BitVec 13),
    .LI .x5 (1 : Word),
    .BLTU .x5 .x19 (244 : BitVec 13),
    .LI .x5 (15 : Word),
    .BLTU .x5 .x20 (236 : BitVec 13),
    .AUIPC .x8 (laHi GuestAddrs.zk3_state (GuestAddrs.mpt_indexed_large_leaf_hash + 100)),
    .ADDI .x8 .x8 (laLo GuestAddrs.zk3_state (GuestAddrs.mpt_indexed_large_leaf_hash + 100)),
    .MV .x5 .x8,
    .LI .x6 (25 : Word),
    .SD .x5 .x0 (0 : BitVec 12),
    .ADDI .x5 .x5 (8 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .BNE .x6 .x0 (-12 : BitVec 13),
    .LI .x22 (0 : Word),
    .LI .x10 (128 : Word),
    .MV .x11 .x18,
    .ADDI .x12 .x2 (104 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_prefix_to_buffer (GuestAddrs.mpt_indexed_large_leaf_hash + 148)),
    .MV .x23 .x10,
    .ADD .x24 .x23 .x18,
    .ADDI .x11 .x24 (1 : BitVec 12),
    .LI .x10 (192 : Word),
    .ADDI .x12 .x2 (120 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_prefix_to_buffer (GuestAddrs.mpt_indexed_large_leaf_hash + 172)),
    .MV .x25 .x10,
    .ADDI .x5 .x2 (136 : BitVec 12),
    .BEQ .x19 .x0 (12 : BitVec 13),
    .ORI .x6 .x20 (48 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .LI .x6 (32 : Word),
    .SB .x5 .x6 (0 : BitVec 12),
    .ADDI .x10 .x2 (120 : BitVec 12),
    .MV .x11 .x25,
    .JAL .x1 (184 : BitVec 21),
    .ADDI .x10 .x2 (136 : BitVec 12),
    .LI .x11 (1 : Word),
    .JAL .x1 (172 : BitVec 21),
    .ADDI .x10 .x2 (104 : BitVec 12),
    .MV .x11 .x23,
    .JAL .x1 (160 : BitVec 21),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .JAL .x1 (148 : BitVec 21),
    .ADD .x5 .x8 .x22,
    .LBU .x6 .x5 (0 : BitVec 12),
    .XORI .x6 .x6 (1 : BitVec 12),
    .SB .x5 .x6 (0 : BitVec 12),
    .ADDI .x5 .x8 (135 : BitVec 12),
    .LBU .x6 .x5 (0 : BitVec 12),
    .XORI .x6 .x6 (128 : BitVec 12),
    .SB .x5 .x6 (0 : BitVec 12),
    .MV .x10 .x8,
    .CSRS (2048 : BitVec 12) .x10,
    .LD .x5 .x8 (0 : BitVec 12),
    .SD .x21 .x5 (0 : BitVec 12),
    .LD .x5 .x8 (8 : BitVec 12),
    .SD .x21 .x5 (8 : BitVec 12),
    .LD .x5 .x8 (16 : BitVec 12),
    .SD .x21 .x5 (16 : BitVec 12),
    .LD .x5 .x8 (24 : BitVec 12),
    .SD .x21 .x5 (24 : BitVec 12),
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
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .LD .x25 .x2 (80 : BitVec 12),
    .LD .x26 .x2 (88 : BitVec 12),
    .LD .x27 .x2 (96 : BitVec 12),
    .ADDI .x2 .x2 (144 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12),
    .MV .x26 .x10,
    .MV .x27 .x11,
    .BEQ .x27 .x0 (60 : BitVec 13),
    .LBU .x5 .x26 (0 : BitVec 12),
    .ADD .x6 .x8 .x22,
    .LBU .x7 .x6 (0 : BitVec 12),
    .XOR .x7 .x7 .x5,
    .SB .x6 .x7 (0 : BitVec 12),
    .ADDI .x26 .x26 (1 : BitVec 12),
    .ADDI .x27 .x27 (-1 : BitVec 12),
    .ADDI .x22 .x22 (1 : BitVec 12),
    .LI .x28 (136 : Word),
    .BNE .x22 .x28 (-40 : BitVec 13),
    .MV .x10 .x8,
    .CSRS (2048 : BitVec 12) .x10,
    .LI .x22 (0 : Word),
    .JAL .x0 (-56 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `mptIndexedLargeLeafHash_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptIndexedLargeLeafHash_relocs : RelocTable :=
  [ (25, .la .x8 "zk3_state"),
    (37, .jal .x1 "rlp_prefix_to_buffer"),
    (43, .jal .x1 "rlp_prefix_to_buffer") ]

def mptIndexedLargeLeafHashFunction : String :=
  "mpt_indexed_large_leaf_hash:\n" ++ emitProgramR mptIndexedLargeLeafHash_prog mptIndexedLargeLeafHash_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptIndexedLargeLeafHash_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptIndexedLargeLeafHashFunction_eq_prog :
    mptIndexedLargeLeafHashFunction = "mpt_indexed_large_leaf_hash:\n" ++ emitProgramR mptIndexedLargeLeafHash_prog mptIndexedLargeLeafHash_relocs := rfl

#guard mptIndexedLargeLeafHashFunction.startsWith "mpt_indexed_large_leaf_hash:\n"
#guard mptIndexedLargeLeafHash_prog.length = 117
/-! ## mpt_indexed_trie_root_large -- grouped large-value indexed trie root

    Fast path for contiguous indexed keys 0..n-1, n <= 128, when every value is
    large enough to be referenced by hash from a branch slot. It covers the
    two-nibble RLP-index key space used by the transaction and withdrawal tries
    before the 128 boundary.

    a0 = value descriptor array ptr, a1 = number of values, a2 = out root ptr.
    Returns a0 = 0 ok / 1 internal failure / 2 unsupported, use generic path. -/
def mptIndexedTrieRootLarge_prog : Program :=
  [ .ADDI .x2 .x2 (-2016 : BitVec 12),
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
    .SD .x2 .x25 (80 : BitVec 12),
    .SD .x2 .x26 (88 : BitVec 12),
    .SD .x2 .x27 (96 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .ADDI .x22 .x2 (160 : BitVec 12),
    .ADDI .x23 .x2 (760 : BitVec 12),
    .ADDI .x24 .x2 (1360 : BitVec 12),
    .LI .x5 (2 : Word),
    .BLTU .x9 .x5 (280 : BitVec 13),
    .LI .x5 (129 : Word),
    .BGEU .x9 .x5 (272 : BitVec 13),
    .LI .x26 (0 : Word),
    .BEQ .x26 .x9 (32 : BitVec 13),
    .SLLI .x5 .x26 (4 : BitVec 6),
    .ADD .x5 .x8 .x5,
    .LD .x6 .x5 (8 : BitVec 12),
    .LI .x7 (56 : Word),
    .BLTU .x6 .x7 (244 : BitVec 13),
    .ADDI .x26 .x26 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .MV .x25 .x22,
    .LI .x19 (0 : Word),
    .LI .x5 (16 : Word),
    .BEQ .x19 .x5 (184 : BitVec 13),
    .LI .x20 (0 : Word),
    .LI .x21 (0 : Word),
    .LI .x26 (0 : Word),
    .BEQ .x26 .x9 (44 : BitVec 13),
    .BEQ .x26 .x0 (12 : BitVec 13),
    .SRLI .x6 .x26 (4 : BitVec 6),
    .JAL .x0 (8 : BitVec 21),
    .LI .x6 (8 : Word),
    .BNE .x6 .x19 (16 : BitVec 13),
    .BNE .x20 .x0 (8 : BitVec 13),
    .MV .x21 .x26,
    .ADDI .x20 .x20 (1 : BitVec 12),
    .ADDI .x26 .x26 (1 : BitVec 12),
    .JAL .x0 (-40 : BitVec 21),
    .BEQ .x20 .x0 (104 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x20 .x5 (28 : BitVec 13),
    .JAL .x1 (220 : BitVec 21),
    .ADDI .x11 .x2 (1968 : BitVec 12),
    .MV .x10 .x25,
    .JAL .x1 (376 : BitVec 21),
    .MV .x25 .x10,
    .JAL .x0 (84 : BitVec 21),
    .SLLI .x5 .x21 (4 : BitVec 6),
    .ADD .x5 .x8 .x5,
    .LD .x10 .x5 (0 : BitVec 12),
    .LD .x11 .x5 (8 : BitVec 12),
    .LI .x12 (1 : Word),
    .BEQ .x21 .x0 (12 : BitVec 13),
    .ANDI .x13 .x21 (15 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .LI .x13 (0 : Word),
    .ADDI .x14 .x2 (1968 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.mpt_indexed_large_leaf_hash (GuestAddrs.mpt_indexed_trie_root_large + 280)),
    .BNE .x10 .x0 (88 : BitVec 13),
    .MV .x10 .x25,
    .ADDI .x11 .x2 (1968 : BitVec 12),
    .JAL .x1 (308 : BitVec 21),
    .MV .x25 .x10,
    .JAL .x0 (16 : BitVec 21),
    .LI .x5 (128 : Word),
    .SB .x25 .x5 (0 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (-184 : BitVec 21),
    .LI .x5 (128 : Word),
    .SB .x25 .x5 (0 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .SUB .x11 .x25 .x22,
    .MV .x10 .x22,
    .MV .x12 .x18,
    .JAL .x1 (300 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (2 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
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
    .LD .x25 .x2 (80 : BitVec 12),
    .LD .x26 .x2 (88 : BitVec 12),
    .LD .x27 .x2 (96 : BitVec 12),
    .ADDI .x2 .x2 (2016 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12),
    .SD .x2 .x25 (128 : BitVec 12),
    .SD .x2 .x1 (152 : BitVec 12),
    .MV .x25 .x23,
    .LI .x20 (0 : Word),
    .LI .x5 (16 : Word),
    .BEQ .x20 .x5 (96 : BitVec 13),
    .SLLI .x26 .x19 (4 : BitVec 6),
    .ADD .x26 .x26 .x20,
    .BEQ .x26 .x0 (64 : BitVec 13),
    .BGEU .x26 .x9 (60 : BitVec 13),
    .SLLI .x5 .x26 (4 : BitVec 6),
    .ADD .x5 .x8 .x5,
    .LD .x10 .x5 (0 : BitVec 12),
    .LD .x11 .x5 (8 : BitVec 12),
    .LI .x12 (0 : Word),
    .LI .x13 (0 : Word),
    .ADDI .x14 .x2 (1968 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.mpt_indexed_large_leaf_hash (GuestAddrs.mpt_indexed_trie_root_large + 504)),
    .BNE .x10 .x0 (84 : BitVec 13),
    .MV .x10 .x25,
    .ADDI .x11 .x2 (1968 : BitVec 12),
    .JAL .x1 (84 : BitVec 21),
    .MV .x25 .x10,
    .JAL .x0 (16 : BitVec 21),
    .LI .x5 (128 : Word),
    .SB .x25 .x5 (0 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (-96 : BitVec 21),
    .LI .x5 (128 : Word),
    .SB .x25 .x5 (0 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .SUB .x11 .x25 .x23,
    .MV .x10 .x23,
    .ADDI .x12 .x2 (1968 : BitVec 12),
    .JAL .x1 (76 : BitVec 21),
    .LD .x25 .x2 (128 : BitVec 12),
    .LD .x1 .x2 (152 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LD .x25 .x2 (128 : BitVec 12),
    .LD .x1 .x2 (152 : BitVec 12),
    .JAL .x0 (-228 : BitVec 21),
    .LI .x5 (160 : Word),
    .SB .x10 .x5 (0 : BitVec 12),
    .ADDI .x5 .x10 (1 : BitVec 12),
    .LI .x6 (32 : Word),
    .LBU .x7 .x11 (0 : BitVec 12),
    .SB .x5 .x7 (0 : BitVec 12),
    .ADDI .x11 .x11 (1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .BNE .x6 .x0 (-20 : BitVec 13),
    .ADDI .x10 .x10 (33 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12),
    .SD .x2 .x10 (104 : BitVec 12),
    .SD .x2 .x11 (112 : BitVec 12),
    .SD .x2 .x12 (120 : BitVec 12),
    .SD .x2 .x1 (144 : BitVec 12),
    .LI .x10 (192 : Word),
    .LD .x11 .x2 (112 : BitVec 12),
    .MV .x12 .x24,
    .JAL .x1 (jalOff GuestAddrs.rlp_prefix_to_buffer (GuestAddrs.mpt_indexed_trie_root_large + 680)),
    .MV .x5 .x10,
    .ADD .x6 .x24 .x5,
    .LD .x7 .x2 (104 : BitVec 12),
    .LD .x28 .x2 (112 : BitVec 12),
    .BEQ .x28 .x0 (28 : BitVec 13),
    .LBU .x29 .x7 (0 : BitVec 12),
    .SB .x6 .x29 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .LD .x28 .x2 (112 : BitVec 12),
    .ADD .x11 .x5 .x28,
    .MV .x10 .x24,
    .LD .x12 .x2 (120 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.mpt_indexed_trie_root_large + 744)),
    .LD .x1 .x2 (144 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `mptIndexedTrieRootLarge_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptIndexedTrieRootLarge_relocs : RelocTable :=
  [ (70, .jal .x1 "mpt_indexed_large_leaf_hash"),
    (126, .jal .x1 "mpt_indexed_large_leaf_hash"),
    (170, .jal .x1 "rlp_prefix_to_buffer"),
    (186, .jal .x1 "zkvm_keccak256") ]

def mptIndexedTrieRootLargeFunction : String :=
  "mpt_indexed_trie_root_large:\n" ++ emitProgramR mptIndexedTrieRootLarge_prog mptIndexedTrieRootLarge_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptIndexedTrieRootLarge_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptIndexedTrieRootLargeFunction_eq_prog :
    mptIndexedTrieRootLargeFunction = "mpt_indexed_trie_root_large:\n" ++ emitProgramR mptIndexedTrieRootLarge_prog mptIndexedTrieRootLarge_relocs := rfl

#guard mptIndexedTrieRootLargeFunction.startsWith "mpt_indexed_trie_root_large:\n"
#guard mptIndexedTrieRootLarge_prog.length = 189
def mptIndexedTrieRootSmall_prog : Program :=
  [ .ADDI .x2 .x2 (-56 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .LUI .x5 (1 : BitVec 20),
    .ADDIW .x5 .x5 (-2047 : BitVec 12),
    .BGEU .x9 .x5 (420 : BitVec 13),
    .BEQ .x9 .x0 (328 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x9 .x5 (300 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.mpt_indexed_trie_root_large (GuestAddrs.mpt_indexed_trie_root_small + 76)),
    .LI .x5 (2 : Word),
    .BNE .x10 .x5 (388 : BitVec 13),
    .LI .x19 (0 : Word),
    .BEQ .x19 .x9 (332 : BitVec 13),
    .SLLI .x5 .x19 (4 : BitVec 6),
    .ADD .x5 .x8 .x5,
    .LD .x6 .x5 (0 : BitVec 12),
    .LD .x7 .x5 (8 : BitVec 12),
    .SLLI .x28 .x19 (3 : BitVec 6),
    .AUIPC .x29 (laHi GuestAddrs.itr_paths (GuestAddrs.mpt_indexed_trie_root_small + 116)),
    .ADDI .x29 .x29 (laLo GuestAddrs.itr_paths (GuestAddrs.mpt_indexed_trie_root_small + 116)),
    .ADD .x29 .x29 .x28,
    .BEQ .x19 .x0 (152 : BitVec 13),
    .LI .x5 (256 : Word),
    .BGEU .x19 .x5 (76 : BitVec 13),
    .LI .x5 (128 : Word),
    .BGEU .x19 .x5 (28 : BitVec 13),
    .SRLI .x30 .x19 (4 : BitVec 6),
    .ANDI .x31 .x19 (15 : BitVec 12),
    .SB .x29 .x30 (0 : BitVec 12),
    .SB .x29 .x31 (1 : BitVec 12),
    .LI .x5 (2 : Word),
    .JAL .x0 (128 : BitVec 21),
    .LI .x30 (8 : Word),
    .SB .x29 .x30 (0 : BitVec 12),
    .LI .x30 (1 : Word),
    .SB .x29 .x30 (1 : BitVec 12),
    .SRLI .x30 .x19 (4 : BitVec 6),
    .ANDI .x31 .x19 (15 : BitVec 12),
    .SB .x29 .x30 (2 : BitVec 12),
    .SB .x29 .x31 (3 : BitVec 12),
    .LI .x5 (4 : Word),
    .JAL .x0 (88 : BitVec 21),
    .LI .x30 (8 : Word),
    .SB .x29 .x30 (0 : BitVec 12),
    .LI .x30 (2 : Word),
    .SB .x29 .x30 (1 : BitVec 12),
    .SRLI .x30 .x19 (12 : BitVec 6),
    .ANDI .x30 .x30 (15 : BitVec 12),
    .SB .x29 .x30 (2 : BitVec 12),
    .SRLI .x30 .x19 (8 : BitVec 6),
    .ANDI .x30 .x30 (15 : BitVec 12),
    .SB .x29 .x30 (3 : BitVec 12),
    .SRLI .x30 .x19 (4 : BitVec 6),
    .ANDI .x30 .x30 (15 : BitVec 12),
    .SB .x29 .x30 (4 : BitVec 12),
    .ANDI .x31 .x19 (15 : BitVec 12),
    .SB .x29 .x31 (5 : BitVec 12),
    .LI .x5 (6 : Word),
    .JAL .x0 (20 : BitVec 21),
    .LI .x30 (8 : Word),
    .SB .x29 .x30 (0 : BitVec 12),
    .SB .x29 .x0 (1 : BitVec 12),
    .LI .x5 (2 : Word),
    .SD .x2 .x5 (48 : BitVec 12),
    .SLLI .x30 .x19 (5 : BitVec 6),
    .SLLI .x31 .x19 (3 : BitVec 6),
    .ADD .x30 .x30 .x31,
    .AUIPC .x20 (laHi GuestAddrs.itr_changes (GuestAddrs.mpt_indexed_trie_root_small + 312)),
    .ADDI .x20 .x20 (laLo GuestAddrs.itr_changes (GuestAddrs.mpt_indexed_trie_root_small + 312)),
    .ADD .x20 .x20 .x30,
    .SD .x20 .x29 (0 : BitVec 12),
    .LD .x30 .x2 (48 : BitVec 12),
    .SD .x20 .x30 (8 : BitVec 12),
    .SD .x20 .x6 (16 : BitVec 12),
    .SD .x20 .x7 (24 : BitVec 12),
    .LI .x30 (1 : Word),
    .SD .x20 .x30 (32 : BitVec 12),
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (-264 : BitVec 21),
    .LD .x10 .x8 (0 : BitVec 12),
    .LD .x11 .x8 (8 : BitVec 12),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.mpt_indexed_trie_root_one_leaf (GuestAddrs.mpt_indexed_trie_root_small + 372)),
    .JAL .x0 (96 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.iw_empty_trie_root (GuestAddrs.mpt_indexed_trie_root_small + 380)),
    .ADDI .x5 .x5 (laLo GuestAddrs.iw_empty_trie_root (GuestAddrs.mpt_indexed_trie_root_small + 380)),
    .LI .x6 (32 : Word),
    .LBU .x7 .x5 (0 : BitVec 12),
    .SB .x18 .x7 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x18 .x18 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .BNE .x6 .x0 (-20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (52 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.iw_empty_trie_root (GuestAddrs.mpt_indexed_trie_root_small + 424)),
    .ADDI .x10 .x10 (laLo GuestAddrs.iw_empty_trie_root (GuestAddrs.mpt_indexed_trie_root_small + 424)),
    .AUIPC .x11 (laHi GuestAddrs.itr_empty_witness (GuestAddrs.mpt_indexed_trie_root_small + 432)),
    .ADDI .x11 .x11 (laLo GuestAddrs.itr_empty_witness (GuestAddrs.mpt_indexed_trie_root_small + 432)),
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.itr_changes (GuestAddrs.mpt_indexed_trie_root_small + 444)),
    .ADDI .x13 .x13 (laLo GuestAddrs.itr_changes (GuestAddrs.mpt_indexed_trie_root_small + 444)),
    .MV .x14 .x9,
    .MV .x15 .x18,
    .JAL .x1 (jalOff GuestAddrs.mpt_state_root_ins (GuestAddrs.mpt_indexed_trie_root_small + 460)),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (56 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `mptIndexedTrieRootSmall_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptIndexedTrieRootSmall_relocs : RelocTable :=
  [ (19, .jal .x1 "mpt_indexed_trie_root_large"),
    (29, .la .x29 "itr_paths"),
    (78, .la .x20 "itr_changes"),
    (93, .jal .x1 "mpt_indexed_trie_root_one_leaf"),
    (95, .la .x5 "iw_empty_trie_root"),
    (106, .la .x10 "iw_empty_trie_root"),
    (108, .la .x11 "itr_empty_witness"),
    (111, .la .x13 "itr_changes"),
    (115, .jal .x1 "mpt_state_root_ins") ]

def mptIndexedTrieRootSmallFunction : String :=
  "mpt_indexed_trie_root_small:\n" ++ emitProgramR mptIndexedTrieRootSmall_prog mptIndexedTrieRootSmall_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptIndexedTrieRootSmall_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptIndexedTrieRootSmallFunction_eq_prog :
    mptIndexedTrieRootSmallFunction = "mpt_indexed_trie_root_small:\n" ++ emitProgramR mptIndexedTrieRootSmall_prog mptIndexedTrieRootSmall_relocs := rfl

#guard mptIndexedTrieRootSmallFunction.startsWith "mpt_indexed_trie_root_small:\n"
#guard mptIndexedTrieRootSmall_prog.length = 126
def ziskMptIndexedTrieRootSmallPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld s0, 8(t0)                # n values\n" ++
  "  addi s1, t0, 16             # length table\n" ++
  "  slli s2, s0, 3; add s2, s1, s2   # blob cursor\n" ++
  "  la s3, itr_value_descs\n" ++
  "  li s4, 0                    # i\n" ++
  ".Litrp_desc_loop:\n" ++
  "  beq s4, s0, .Litrp_desc_done\n" ++
  "  slli t1, s4, 3; add t2, s1, t1; ld t3, 0(t2)    # len[i]\n" ++
  "  slli t4, s4, 4; add t5, s3, t4\n" ++
  "  sd s2, 0(t5); sd t3, 8(t5)\n" ++
  "  add s2, s2, t3\n" ++
  "  addi s2, s2, 7; andi s2, s2, -8\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Litrp_desc_loop\n" ++
  ".Litrp_desc_done:\n" ++
  "  la a0, itr_value_descs\n" ++
  "  mv a1, s0\n" ++
  "  li a2, 0xa0010000\n" ++
  "  jal ra, mpt_indexed_trie_root_small\n" ++
  "  li t0, 0xa0010020; sd a0, 0(t0)\n" ++
  "  j .Litrp_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  nodeDbAppendFunction ++ "\n" ++
  mptResolveCacheResetFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  mptSetRecordWalkDbFunction ++ "\n" ++
  mptDeleteWalkDbFunction ++ "\n" ++
  mptInsertWalkDbFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  mptLeafExtractFunction ++ "\n" ++
  mptExtensionExtractFunction ++ "\n" ++
  mptExtensionNodeEncodeFunction ++ "\n" ++
  mptSetAccFunction ++ "\n" ++
  mptDeleteAccFunction ++ "\n" ++
  mptInsertAccFunction ++ "\n" ++
  mptStateRootInsFunction ++ "\n" ++
  mptIndexedTrieRootOneLeafFunction ++ "\n" ++
  mptIndexedLargeLeafHashFunction ++ "\n" ++
  mptIndexedTrieRootLargeFunction ++ "\n" ++
  mptIndexedTrieRootSmallFunction ++ "\n" ++
  ".Litrp_done:"

def ziskMptIndexedTrieRootSmallDataSection : String :=
  ziskMptStateRootInsDataSection ++ "\n" ++
  ".balign 8\n" ++
  "itr_empty_witness:\n  .zero 8\n" ++
  "itr_value_descs:\n  .zero 32768\n" ++
  "itr_paths:\n  .zero 16384\n" ++
  "itr_changes:\n  .zero 81920"

def ziskMptIndexedTrieRootSmallProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptIndexedTrieRootSmallPrologue
  dataAsm     := ziskMptIndexedTrieRootSmallDataSection
}


/-! Probe for `mpt_indexed_large_leaf_hash`.

    Input layout (file maps to INPUT+8):
      +8  path kind (0 empty, 1 one nibble)
      +16 nibble
      +24 value_len
      +32 value bytes, padded by the host test script
    Output: +0 hash, +32 status. -/
def ziskMptIndexedLargeLeafHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a2, 8(t0)                # path kind\n" ++
  "  ld a3, 16(t0)               # nibble\n" ++
  "  ld a1, 24(t0)               # value len\n" ++
  "  addi a0, t0, 32             # value ptr\n" ++
  "  li a4, 0xa0010000           # out hash\n" ++
  "  jal ra, mpt_indexed_large_leaf_hash\n" ++
  "  li t0, 0xa0010020; sd a0, 0(t0)\n" ++
  "  j .Lillhp_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  mptIndexedTrieRootOneLeafFunction ++ "\n" ++
  mptIndexedLargeLeafHashFunction ++ "\n" ++
  ".Lillhp_done:"

def ziskMptIndexedLargeLeafHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptIndexedLargeLeafHashPrologue
  dataAsm     := ziskMptStateRootInsDataSection
}

end EvmAsm.Codegen
