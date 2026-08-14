/-
  EvmAsm.Codegen.Programs.MptInsertWalk

  mpt_insert_walk (bead evm-asm-fhsxz.2.4.2.6.1): the divergence-classifying
  descent that is the foundation for inserting a NEW key into a witness-backed
  MPT (account creation for withdrawals to absent/precompile recipients).

  It mirrors `mpt_set_record_walk` (Programs/MptSet.lean), which descends a key
  and jumps to a single `not_found` exit at every divergence. mpt_insert_walk
  instead CLASSIFIES the divergence and records the context a later restructure +
  bubble-up pass (mpt_insert, bead .2.4.2.6.2) needs:

    case 0 BRANCH_EMPTY_SLOT : path reaches a branch whose child slot for the
                               next nibble is empty. The branch is the terminal
                               (un-pushed from the ancestor stack); the new leaf
                               goes at slot path[consumed], key path[consumed+1..].
    case 1 LEAF_SPLIT        : path reaches a leaf whose key diverges. match_len
                               = shared-prefix nibbles; split into branch (+ an
                               extension for the shared prefix).
    case 2 EXTENSION_SPLIT   : path diverges inside an extension's key segment.
                               match_len = matched ext nibbles.
    case 3 EMPTY_TRIE        : root == EMPTY_TRIE_ROOT; the whole trie is a single
                               new leaf.
    case 4 EXISTS            : the key is already present (a value-update, not an
                               insert). Does not occur in the withdrawal path
                               (the caller mpt_walks first), reported defensively.
    case 5 BRANCH_VALUE      : path is exhausted exactly at a branch (value slot
                               16). Does not occur for fixed-length 64-nibble
                               account paths, reported defensively.

  The ancestor stack (`stack_out`, 32 B per branch/extension above the terminal,
  root->leaf order) is recorded identically to mpt_set_record_walk so the same
  bubble-up pass re-roots after the terminal is restructured.

  Reuses mpt_walk's scratch labels (mw_*) from `ziskMptWalkDataSection`; adds
  `iw_empty_trie_root` (the 32-byte EMPTY_TRIE_ROOT = keccak256(rlp(b''))).
  All multi-byte work is on 8-aligned scratch; path/key nibbles are read
  byte-wise (no-misaligned invariant).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## mpt_insert_walk -- classify where an ABSENT key diverges from the trie

    Calling convention (identical inputs to mpt_set_record_walk):
      a0 (input)  : root_hash ptr (32 bytes)
      a1 (input)  : witness section ptr
      a2 (input)  : witness section_len
      a3 (input)  : path_nibbles ptr (one byte per nibble)
      a4 (input)  : path_nibbles_len
      a5 (input)  : stack_out ptr (32 bytes per ancestor node)
      a6 (input)  : meta_out ptr (48 bytes)
      ra (input)  : return
      a0 (output) : 0 (diverged + classified, see case) / 1 (incomplete witness,
                    lookup miss) / 2 (parse error)

    `stack_out` entry layout (32 bytes, one per ancestor BRANCH/EXTENSION on the
    root->terminal path, in root->leaf order) -- same as mpt_set_record_walk:
      +0 node_offset : u64   byte offset within the witness section
      +8 node_len    : u64
      +16 kind       : u64   0 = branch, 1 = extension
      +24 nibble     : u64   branch: child index taken; extension: 0

    `meta_out` layout (48 bytes):
      +0  depth           : u64  number of ancestor stack_out entries
      +8  consumed        : u64  path nibbles consumed by ancestors (NOT incl.
                                 the terminal's own divergence)
      +16 case            : u64  0..5 (see file header)
      +24 terminal_offset : u64  byte offset of the terminal node's RLP (0 if
                                 EMPTY_TRIE)
      +32 terminal_len    : u64  full RLP length of the terminal node
      +40 match_len       : u64  case 1/2: shared-prefix nibbles at the terminal;
                                 else 0 -/
/-! Probe-only local PC placeholder. -/
def mptInsertWalkPc : Nat := 0x80000000

def mptInsertWalk_prog : Program :=
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
    .SD .x2 .x25 (80 : BitVec 12),
    .MV .x8 .x11,
    .MV .x9 .x12,
    .MV .x18 .x13,
    .MV .x19 .x14,
    .MV .x20 .x15,
    .MV .x21 .x16,
    .LI .x25 (0 : Word),
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_hash (mptInsertWalkPc + 76)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_hash (mptInsertWalkPc + 76)),
    .LD .x6 .x10 (0 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x6 .x10 (8 : BitVec 12),
    .SD .x5 .x6 (8 : BitVec 12),
    .LD .x6 .x10 (16 : BitVec 12),
    .SD .x5 .x6 (16 : BitVec 12),
    .LD .x6 .x10 (24 : BitVec 12),
    .SD .x5 .x6 (24 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.iw_empty_trie_root (mptInsertWalkPc + 116)),
    .ADDI .x7 .x7 (laLo GuestAddrs.iw_empty_trie_root (mptInsertWalkPc + 116)),
    .LD .x28 .x5 (0 : BitVec 12),
    .LD .x29 .x7 (0 : BitVec 12),
    .BNE .x28 .x29 (48 : BitVec 13),
    .LD .x28 .x5 (8 : BitVec 12),
    .LD .x29 .x7 (8 : BitVec 12),
    .BNE .x28 .x29 (36 : BitVec 13),
    .LD .x28 .x5 (16 : BitVec 12),
    .LD .x29 .x7 (16 : BitVec 12),
    .BNE .x28 .x29 (24 : BitVec 13),
    .LD .x28 .x5 (24 : BitVec 12),
    .LD .x29 .x7 (24 : BitVec 12),
    .BNE .x28 .x29 (12 : BitVec 13),
    .LI .x30 (3 : Word),
    .JAL .x0 (jalOff (mptInsertWalkPc + 1268) (mptInsertWalkPc + 176)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.mw_lookup_hash (mptInsertWalkPc + 188)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mw_lookup_hash (mptInsertWalkPc + 188)),
    .AUIPC .x13 (laHi GuestAddrs.mw_lookup_offset (mptInsertWalkPc + 196)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_lookup_offset (mptInsertWalkPc + 196)),
    .AUIPC .x14 (laHi GuestAddrs.mw_lookup_length (mptInsertWalkPc + 204)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_lookup_length (mptInsertWalkPc + 204)),
    .JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash (mptInsertWalkPc + 212)),
    .BNE .x10 .x0 (brOff (mptInsertWalkPc + 1300) (mptInsertWalkPc + 216)),
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_offset (mptInsertWalkPc + 220)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_offset (mptInsertWalkPc + 220)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x8 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_length (mptInsertWalkPc + 236)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_length (mptInsertWalkPc + 236)),
    .LD .x24 .x5 (0 : BitVec 12),
    .LI .x22 (0 : Word),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .JAL .x1 (jalOff GuestAddrs.mpt_node_kind (mptInsertWalkPc + 260)),
    .BEQ .x10 .x0 (24 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (brOff (mptInsertWalkPc + 580) (mptInsertWalkPc + 272)),
    .LI .x5 (2 : Word),
    .BEQ .x10 .x5 (brOff (mptInsertWalkPc + 1016) (mptInsertWalkPc + 280)),
    .JAL .x0 (jalOff (mptInsertWalkPc + 1308) (mptInsertWalkPc + 284)),
    .BEQ .x22 .x19 (brOff (mptInsertWalkPc + 568) (mptInsertWalkPc + 288)),
    .ADD .x5 .x18 .x22,
    .LBU .x6 .x5 (0 : BitVec 12),
    .SUB .x7 .x23 .x8,
    .SD .x20 .x7 (0 : BitVec 12),
    .SD .x20 .x24 (8 : BitVec 12),
    .SD .x20 .x0 (16 : BitVec 12),
    .SD .x20 .x6 (24 : BitVec 12),
    .ADDI .x20 .x20 (32 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .MV .x12 .x6,
    .AUIPC .x13 (laHi GuestAddrs.mw_child_offset (mptInsertWalkPc + 340)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_child_offset (mptInsertWalkPc + 340)),
    .AUIPC .x14 (laHi GuestAddrs.mw_child_length (mptInsertWalkPc + 348)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_child_length (mptInsertWalkPc + 348)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (mptInsertWalkPc + 356)),
    .ADDI .x22 .x22 (1 : BitVec 12),
    .BNE .x10 .x0 (brOff (mptInsertWalkPc + 1308) (mptInsertWalkPc + 364)),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_length (mptInsertWalkPc + 368)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_length (mptInsertWalkPc + 368)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (brOff (mptInsertWalkPc + 544) (mptInsertWalkPc + 380)),
    .LI .x7 (32 : Word),
    .BEQ .x6 .x7 (28 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_offset (mptInsertWalkPc + 392)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_offset (mptInsertWalkPc + 392)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x7,
    .MV .x24 .x6,
    .JAL .x0 (jalOff (mptInsertWalkPc + 252) (mptInsertWalkPc + 412)),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_offset (mptInsertWalkPc + 416)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_offset (mptInsertWalkPc + 416)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x7 .x23 .x6,
    .AUIPC .x28 (laHi GuestAddrs.mw_lookup_hash (mptInsertWalkPc + 432)),
    .ADDI .x28 .x28 (laLo GuestAddrs.mw_lookup_hash (mptInsertWalkPc + 432)),
    .LD .x29 .x7 (0 : BitVec 12),
    .SD .x28 .x29 (0 : BitVec 12),
    .LD .x29 .x7 (8 : BitVec 12),
    .SD .x28 .x29 (8 : BitVec 12),
    .LD .x29 .x7 (16 : BitVec 12),
    .SD .x28 .x29 (16 : BitVec 12),
    .LD .x29 .x7 (24 : BitVec 12),
    .SD .x28 .x29 (24 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.mw_lookup_hash (mptInsertWalkPc + 480)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mw_lookup_hash (mptInsertWalkPc + 480)),
    .AUIPC .x13 (laHi GuestAddrs.mw_lookup_offset (mptInsertWalkPc + 488)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_lookup_offset (mptInsertWalkPc + 488)),
    .AUIPC .x14 (laHi GuestAddrs.mw_lookup_length (mptInsertWalkPc + 496)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_lookup_length (mptInsertWalkPc + 496)),
    .JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash (mptInsertWalkPc + 504)),
    .BNE .x10 .x0 (brOff (mptInsertWalkPc + 1300) (mptInsertWalkPc + 508)),
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_offset (mptInsertWalkPc + 512)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_offset (mptInsertWalkPc + 512)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x8 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_length (mptInsertWalkPc + 528)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_length (mptInsertWalkPc + 528)),
    .LD .x24 .x5 (0 : BitVec 12),
    .JAL .x0 (jalOff (mptInsertWalkPc + 252) (mptInsertWalkPc + 540)),
    .ADDI .x20 .x20 (-32 : BitVec 12),
    .ADDI .x25 .x25 (-1 : BitVec 12),
    .LI .x30 (0 : Word),
    .ADDI .x22 .x22 (-1 : BitVec 12),
    .LI .x31 (0 : Word),
    .JAL .x0 (jalOff (mptInsertWalkPc + 1232) (mptInsertWalkPc + 564)),
    .LI .x30 (5 : Word),
    .LI .x31 (0 : Word),
    .JAL .x0 (jalOff (mptInsertWalkPc + 1232) (mptInsertWalkPc + 576)),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mw_path_offset (mptInsertWalkPc + 592)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_path_offset (mptInsertWalkPc + 592)),
    .AUIPC .x14 (laHi GuestAddrs.mw_path_length (mptInsertWalkPc + 600)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_path_length (mptInsertWalkPc + 600)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (mptInsertWalkPc + 608)),
    .BNE .x10 .x0 (brOff (mptInsertWalkPc + 1308) (mptInsertWalkPc + 612)),
    .AUIPC .x5 (laHi GuestAddrs.mw_path_offset (mptInsertWalkPc + 616)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_offset (mptInsertWalkPc + 616)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x10 .x23 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mw_path_length (mptInsertWalkPc + 632)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_length (mptInsertWalkPc + 632)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.mw_nibble_buf (mptInsertWalkPc + 644)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mw_nibble_buf (mptInsertWalkPc + 644)),
    .AUIPC .x13 (laHi GuestAddrs.mw_nibble_count (mptInsertWalkPc + 652)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_nibble_count (mptInsertWalkPc + 652)),
    .AUIPC .x14 (laHi GuestAddrs.mw_is_leaf (mptInsertWalkPc + 660)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_is_leaf (mptInsertWalkPc + 660)),
    .JAL .x1 (jalOff GuestAddrs.hp_decode_nibbles (mptInsertWalkPc + 668)),
    .BNE .x10 .x0 (brOff (mptInsertWalkPc + 1308) (mptInsertWalkPc + 672)),
    .AUIPC .x5 (laHi GuestAddrs.mw_is_leaf (mptInsertWalkPc + 676)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_is_leaf (mptInsertWalkPc + 676)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BNE .x6 .x0 (brOff (mptInsertWalkPc + 1308) (mptInsertWalkPc + 688)),
    .AUIPC .x5 (laHi GuestAddrs.mw_nibble_count (mptInsertWalkPc + 692)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_nibble_count (mptInsertWalkPc + 692)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SUB .x7 .x19 .x22,
    .MV .x28 .x6,
    .BGEU .x7 .x6 (8 : BitVec 13),
    .MV .x28 .x7,
    .AUIPC .x29 (laHi GuestAddrs.mw_nibble_buf (mptInsertWalkPc + 720)),
    .ADDI .x29 .x29 (laLo GuestAddrs.mw_nibble_buf (mptInsertWalkPc + 720)),
    .ADD .x30 .x18 .x22,
    .LI .x31 (0 : Word),
    .BEQ .x31 .x28 (32 : BitVec 13),
    .ADD .x10 .x29 .x31,
    .LBU .x11 .x10 (0 : BitVec 12),
    .ADD .x10 .x30 .x31,
    .LBU .x12 .x10 (0 : BitVec 12),
    .BNE .x11 .x12 (12 : BitVec 13),
    .ADDI .x31 .x31 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .BNE .x31 .x6 (brOff (mptInsertWalkPc + 1008) (mptInsertWalkPc + 768)),
    .BLTU .x7 .x6 (brOff (mptInsertWalkPc + 1008) (mptInsertWalkPc + 772)),
    .SUB .x10 .x23 .x8,
    .SD .x20 .x10 (0 : BitVec 12),
    .SD .x20 .x24 (8 : BitVec 12),
    .LI .x11 (1 : Word),
    .SD .x20 .x11 (16 : BitVec 12),
    .SD .x20 .x0 (24 : BitVec 12),
    .ADDI .x20 .x20 (32 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .ADD .x22 .x22 .x6,
    .MV .x10 .x23,
    .MV .x11 .x24,
    .LI .x12 (1 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mw_child_offset (mptInsertWalkPc + 824)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_child_offset (mptInsertWalkPc + 824)),
    .AUIPC .x14 (laHi GuestAddrs.mw_child_length (mptInsertWalkPc + 832)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_child_length (mptInsertWalkPc + 832)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (mptInsertWalkPc + 840)),
    .BNE .x10 .x0 (brOff (mptInsertWalkPc + 1308) (mptInsertWalkPc + 844)),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_length (mptInsertWalkPc + 848)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_length (mptInsertWalkPc + 848)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_offset (mptInsertWalkPc + 860)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_offset (mptInsertWalkPc + 860)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x28 .x23 .x7,
    .LI .x29 (32 : Word),
    .BEQ .x6 .x29 (16 : BitVec 13),
    .MV .x23 .x28,
    .MV .x24 .x6,
    .JAL .x0 (jalOff (mptInsertWalkPc + 252) (mptInsertWalkPc + 892)),
    .AUIPC .x29 (laHi GuestAddrs.mw_lookup_hash (mptInsertWalkPc + 896)),
    .ADDI .x29 .x29 (laLo GuestAddrs.mw_lookup_hash (mptInsertWalkPc + 896)),
    .LD .x30 .x28 (0 : BitVec 12),
    .SD .x29 .x30 (0 : BitVec 12),
    .LD .x30 .x28 (8 : BitVec 12),
    .SD .x29 .x30 (8 : BitVec 12),
    .LD .x30 .x28 (16 : BitVec 12),
    .SD .x29 .x30 (16 : BitVec 12),
    .LD .x30 .x28 (24 : BitVec 12),
    .SD .x29 .x30 (24 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.mw_lookup_hash (mptInsertWalkPc + 944)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mw_lookup_hash (mptInsertWalkPc + 944)),
    .AUIPC .x13 (laHi GuestAddrs.mw_lookup_offset (mptInsertWalkPc + 952)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_lookup_offset (mptInsertWalkPc + 952)),
    .AUIPC .x14 (laHi GuestAddrs.mw_lookup_length (mptInsertWalkPc + 960)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_lookup_length (mptInsertWalkPc + 960)),
    .JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash (mptInsertWalkPc + 968)),
    .BNE .x10 .x0 (brOff (mptInsertWalkPc + 1300) (mptInsertWalkPc + 972)),
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_offset (mptInsertWalkPc + 976)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_offset (mptInsertWalkPc + 976)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x8 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_length (mptInsertWalkPc + 992)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_length (mptInsertWalkPc + 992)),
    .LD .x24 .x5 (0 : BitVec 12),
    .JAL .x0 (jalOff (mptInsertWalkPc + 252) (mptInsertWalkPc + 1004)),
    .LI .x30 (2 : Word),
    .JAL .x0 (jalOff (mptInsertWalkPc + 1232) (mptInsertWalkPc + 1012)),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mw_path_offset (mptInsertWalkPc + 1028)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_path_offset (mptInsertWalkPc + 1028)),
    .AUIPC .x14 (laHi GuestAddrs.mw_path_length (mptInsertWalkPc + 1036)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_path_length (mptInsertWalkPc + 1036)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (mptInsertWalkPc + 1044)),
    .BNE .x10 .x0 (brOff (mptInsertWalkPc + 1308) (mptInsertWalkPc + 1048)),
    .AUIPC .x5 (laHi GuestAddrs.mw_path_offset (mptInsertWalkPc + 1052)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_offset (mptInsertWalkPc + 1052)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x10 .x23 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mw_path_length (mptInsertWalkPc + 1068)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_length (mptInsertWalkPc + 1068)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.mw_nibble_buf (mptInsertWalkPc + 1080)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mw_nibble_buf (mptInsertWalkPc + 1080)),
    .AUIPC .x13 (laHi GuestAddrs.mw_nibble_count (mptInsertWalkPc + 1088)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_nibble_count (mptInsertWalkPc + 1088)),
    .AUIPC .x14 (laHi GuestAddrs.mw_is_leaf (mptInsertWalkPc + 1096)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_is_leaf (mptInsertWalkPc + 1096)),
    .JAL .x1 (jalOff GuestAddrs.hp_decode_nibbles (mptInsertWalkPc + 1104)),
    .BNE .x10 .x0 (brOff (mptInsertWalkPc + 1308) (mptInsertWalkPc + 1108)),
    .AUIPC .x5 (laHi GuestAddrs.mw_is_leaf (mptInsertWalkPc + 1112)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_is_leaf (mptInsertWalkPc + 1112)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (1 : Word),
    .BNE .x6 .x7 (brOff (mptInsertWalkPc + 1308) (mptInsertWalkPc + 1128)),
    .AUIPC .x5 (laHi GuestAddrs.mw_nibble_count (mptInsertWalkPc + 1132)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_nibble_count (mptInsertWalkPc + 1132)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SUB .x7 .x19 .x22,
    .MV .x28 .x6,
    .BGEU .x7 .x6 (8 : BitVec 13),
    .MV .x28 .x7,
    .AUIPC .x29 (laHi GuestAddrs.mw_nibble_buf (mptInsertWalkPc + 1160)),
    .ADDI .x29 .x29 (laLo GuestAddrs.mw_nibble_buf (mptInsertWalkPc + 1160)),
    .ADD .x30 .x18 .x22,
    .LI .x31 (0 : Word),
    .BEQ .x31 .x28 (32 : BitVec 13),
    .ADD .x10 .x29 .x31,
    .LBU .x11 .x10 (0 : BitVec 12),
    .ADD .x10 .x30 .x31,
    .LBU .x12 .x10 (0 : BitVec 12),
    .BNE .x11 .x12 (12 : BitVec 13),
    .ADDI .x31 .x31 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .BNE .x31 .x6 (16 : BitVec 13),
    .BNE .x6 .x7 (12 : BitVec 13),
    .LI .x30 (4 : Word),
    .JAL .x0 (12 : BitVec 21),
    .LI .x30 (1 : Word),
    .JAL .x0 (4 : BitVec 21),
    .SD .x21 .x25 (0 : BitVec 12),
    .SD .x21 .x22 (8 : BitVec 12),
    .SD .x21 .x30 (16 : BitVec 12),
    .SUB .x5 .x23 .x8,
    .SD .x21 .x5 (24 : BitVec 12),
    .SD .x21 .x24 (32 : BitVec 12),
    .SD .x21 .x31 (40 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (48 : BitVec 21),
    .SD .x21 .x0 (0 : BitVec 12),
    .SD .x21 .x0 (8 : BitVec 12),
    .SD .x21 .x30 (16 : BitVec 12),
    .SD .x21 .x0 (24 : BitVec 12),
    .SD .x21 .x0 (32 : BitVec 12),
    .SD .x21 .x0 (40 : BitVec 12),
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
    .LD .x24 .x2 (72 : BitVec 12),
    .LD .x25 .x2 (80 : BitVec 12),
    .ADDI .x2 .x2 (96 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `mptInsertWalk_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptInsertWalk_relocs : RelocTable :=
  [ (19, .la .x5 "mw_lookup_hash"),
    (29, .la .x7 "iw_empty_trie_root"),
    (47, .la .x12 "mw_lookup_hash"),
    (49, .la .x13 "mw_lookup_offset"),
    (51, .la .x14 "mw_lookup_length"),
    (53, .jal .x1 "witness_lookup_by_hash"),
    (55, .la .x5 "mw_lookup_offset"),
    (59, .la .x5 "mw_lookup_length"),
    (65, .jal .x1 "mpt_node_kind"),
    (85, .la .x13 "mw_child_offset"),
    (87, .la .x14 "mw_child_length"),
    (89, .jal .x1 "rlp_list_nth_item"),
    (92, .la .x5 "mw_child_length"),
    (98, .la .x5 "mw_child_offset"),
    (104, .la .x5 "mw_child_offset"),
    (108, .la .x28 "mw_lookup_hash"),
    (120, .la .x12 "mw_lookup_hash"),
    (122, .la .x13 "mw_lookup_offset"),
    (124, .la .x14 "mw_lookup_length"),
    (126, .jal .x1 "witness_lookup_by_hash"),
    (128, .la .x5 "mw_lookup_offset"),
    (132, .la .x5 "mw_lookup_length"),
    (148, .la .x13 "mw_path_offset"),
    (150, .la .x14 "mw_path_length"),
    (152, .jal .x1 "rlp_list_nth_item"),
    (154, .la .x5 "mw_path_offset"),
    (158, .la .x5 "mw_path_length"),
    (161, .la .x12 "mw_nibble_buf"),
    (163, .la .x13 "mw_nibble_count"),
    (165, .la .x14 "mw_is_leaf"),
    (167, .jal .x1 "hp_decode_nibbles"),
    (169, .la .x5 "mw_is_leaf"),
    (173, .la .x5 "mw_nibble_count"),
    (180, .la .x29 "mw_nibble_buf"),
    (206, .la .x13 "mw_child_offset"),
    (208, .la .x14 "mw_child_length"),
    (210, .jal .x1 "rlp_list_nth_item"),
    (212, .la .x5 "mw_child_length"),
    (215, .la .x5 "mw_child_offset"),
    (224, .la .x29 "mw_lookup_hash"),
    (236, .la .x12 "mw_lookup_hash"),
    (238, .la .x13 "mw_lookup_offset"),
    (240, .la .x14 "mw_lookup_length"),
    (242, .jal .x1 "witness_lookup_by_hash"),
    (244, .la .x5 "mw_lookup_offset"),
    (248, .la .x5 "mw_lookup_length"),
    (257, .la .x13 "mw_path_offset"),
    (259, .la .x14 "mw_path_length"),
    (261, .jal .x1 "rlp_list_nth_item"),
    (263, .la .x5 "mw_path_offset"),
    (267, .la .x5 "mw_path_length"),
    (270, .la .x12 "mw_nibble_buf"),
    (272, .la .x13 "mw_nibble_count"),
    (274, .la .x14 "mw_is_leaf"),
    (276, .jal .x1 "hp_decode_nibbles"),
    (278, .la .x5 "mw_is_leaf"),
    (283, .la .x5 "mw_nibble_count"),
    (290, .la .x29 "mw_nibble_buf") ]

def mptInsertWalkFunction : String :=
  "mpt_insert_walk:\n" ++ emitProgramR mptInsertWalk_prog mptInsertWalk_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptInsertWalk_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptInsertWalkFunction_eq_prog :
    mptInsertWalkFunction = "mpt_insert_walk:\n" ++ emitProgramR mptInsertWalk_prog mptInsertWalk_relocs := rfl

#guard mptInsertWalkFunction.startsWith "mpt_insert_walk:\n"
/-! ## iw_empty_trie_root data + probe data section.
    EMPTY_TRIE_ROOT = keccak256(rlp(b'')) =
      0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421 -/
def iwEmptyTrieRootData : String :=
  "iw_empty_trie_root:\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21"

/-- `zisk_mpt_insert_walk`: probe BuildUnit. Reuses the mpt_set probe input
    layout (scripts/mpt_ref.py `build_probe_input`); the new_value field is
    present but ignored by the walk.
    Input layout (file maps to INPUT+8 at 0x40000000):
      INPUT+8  : witness_len (u64)
      INPUT+16 : path_len (u64)
      INPUT+24 : new_value_len (u64)         [ignored]
      INPUT+32 : root_hash (32 bytes)
      INPUT+64 : path_nibbles (1B each)
      INPUT+64+path_len : new_value
      8-aligned : witness section
    Output layout:
      OUTPUT+0   : status (0 ok / 1 miss / 2 fail)
      OUTPUT+8   : meta (depth, consumed, case, terminal_offset, terminal_len,
                   match_len) -- 48 B
      OUTPUT+128 : ancestor stack records, 32 B each -/
def ziskMptInsertWalkPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # witness_len\n" ++
  "  ld t5, 16(a7)               # path_len\n" ++
  "  ld t4, 24(a7)               # new_value_len\n" ++
  "  addi a0, a7, 32             # root_hash ptr (INPUT+32)\n" ++
  "  addi a3, a7, 64             # path_nibbles ptr (INPUT+64)\n" ++
  "  # witness ptr = path_ptr + roundup8(path_len + new_value_len).\n" ++
  "  add t3, t5, t4\n" ++
  "  addi t3, t3, 7\n" ++
  "  andi t3, t3, -8\n" ++
  "  add a1, a3, t3              # witness ptr\n" ++
  "  mv a2, t6                   # witness_len\n" ++
  "  mv a4, t5                   # path_len\n" ++
  "  li a5, 0xa0010080           # stack_out at OUTPUT + 128\n" ++
  "  li a6, 0xa0010008           # meta_out at OUTPUT + 8\n" ++
  "  jal ra, mpt_insert_walk\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Liw_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  mptInsertWalkFunction ++ "\n" ++
  ".Liw_pdone:"

def ziskMptInsertWalkDataSection : String :=
  ziskMptWalkDataSection ++ "\n" ++
  ".balign 8\n" ++
  iwEmptyTrieRootData


end EvmAsm.Codegen
