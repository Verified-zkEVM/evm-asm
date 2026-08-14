/-
  EvmAsm.Codegen.Programs.MptSet

  MPT post-state-root recompute (bead evm-asm-fhsxz.4): the value-only
  update of an EXISTING key, in two pieces —

    .4.2.1  record-walk    (THIS file, first piece): descend the trie
            exactly like `mpt_walk`, but instead of extracting the value,
            emit the *descent node-stack* (root .. leaf) so the caller can
            re-encode the touched nodes bottom-up.
    .4.2.2  bubble-up       (follow-up): consume the node-stack, re-encode
            the leaf with the new value, then walk back up re-encoding each
            parent's touched slot, hashing as we go, to obtain the new root.

  `mpt_set_record_walk` forks `mpt_walk` (Programs/Mpt.lean): same node-kind
  dispatch, same inline-vs-32-byte-hash child deref, same HP-path compare.
  The only additions are: (a) before descending through a BRANCH or
  EXTENSION, push a 32-byte record to `stack_out`; (b) at the LEAF, write a
  32-byte `meta_out` block instead of copying the value.

  All multi-byte memory accesses are naturally aligned (the project's
  no-misaligned invariant): the records and meta are u64-granular stores to
  8-aligned output cursors; node bodies are read via the same byte-wise
  helpers `mpt_walk` already uses.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.MptEncode

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## mpt_set_record_walk -- record the descent path of an MPT lookup

    Identical descent to `mpt_walk`, but the output is the *node stack*
    along the root→leaf path (so a later bubble-up pass can re-encode the
    touched nodes) rather than the matched value.

    Calling convention:
      a0 (input)  : root_hash ptr (32 bytes)
      a1 (input)  : witness section ptr
      a2 (input)  : witness section_len
      a3 (input)  : path_nibbles ptr (one byte per nibble)
      a4 (input)  : path_nibbles_len
      a5 (input)  : stack_out ptr (32 bytes per descended node)
      a6 (input)  : meta_out ptr (32 bytes)
      ra (input)  : return
      a0 (output) : walk status — see `MptStatusVocab.Walk`

    `stack_out` entry layout (32 bytes, one per BRANCH/EXTENSION descended,
    in root→leaf order):
      +0  node_offset : u64  byte offset of this node's RLP within the
                             witness section (= node_ptr - witness_ptr)
      +8  node_len    : u64  full RLP length of this node
      +16 kind        : u64  0 = branch, 1 = extension
      +24 nibble      : u64  branch: child index taken; extension: 0

    `meta_out` layout (32 bytes), written on a successful (found) walk:
      +0  depth           : u64  number of stack_out entries
      +8  consumed        : u64  path nibbles consumed by branches/extensions
                                 above the leaf (NOT incl. the leaf's HP path)
      +16 leaf_offset     : u64  byte offset of the terminal node's RLP
      +24 leaf_len        : u64  full RLP length of the terminal node

    Registers (callee-saved, mirrors mpt_walk + s9 for depth):
      s0 witness ptr   s1 witness_len   s2 path ptr   s3 path_len
      s4 stack_out cursor   s5 meta_out ptr
      s6 consumed nibbles   s7 current node ptr   s8 current node len
      s9 depth (records pushed)

    Reuses mpt_walk's scratch labels (mw_lookup_hash, mw_*_offset/length,
    mw_nibble_buf, ...) from `ziskMptWalkDataSection`. -/
/-! Probe-only local PC placeholder. -/
def mptSetRecordWalkPc : Nat := 0x80000000

def mptSetRecordWalk_prog : Program :=
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
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_hash (mptSetRecordWalkPc + 76)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_hash (mptSetRecordWalkPc + 76)),
    .LD .x6 .x10 (0 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x6 .x10 (8 : BitVec 12),
    .SD .x5 .x6 (8 : BitVec 12),
    .LD .x6 .x10 (16 : BitVec 12),
    .SD .x5 .x6 (16 : BitVec 12),
    .LD .x6 .x10 (24 : BitVec 12),
    .SD .x5 .x6 (24 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.mw_lookup_hash (mptSetRecordWalkPc + 124)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mw_lookup_hash (mptSetRecordWalkPc + 124)),
    .AUIPC .x13 (laHi GuestAddrs.mw_lookup_offset (mptSetRecordWalkPc + 132)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_lookup_offset (mptSetRecordWalkPc + 132)),
    .AUIPC .x14 (laHi GuestAddrs.mw_lookup_length (mptSetRecordWalkPc + 140)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_lookup_length (mptSetRecordWalkPc + 140)),
    .JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash (mptSetRecordWalkPc + 148)),
    .BNE .x10 .x0 (brOff (mptSetRecordWalkPc + 1132) (mptSetRecordWalkPc + 152)),
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_offset (mptSetRecordWalkPc + 156)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_offset (mptSetRecordWalkPc + 156)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x8 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_length (mptSetRecordWalkPc + 172)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_length (mptSetRecordWalkPc + 172)),
    .LD .x24 .x5 (0 : BitVec 12),
    .LI .x22 (0 : Word),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .JAL .x1 (jalOff GuestAddrs.mpt_node_kind (mptSetRecordWalkPc + 196)),
    .BEQ .x10 .x0 (24 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (brOff (mptSetRecordWalkPc + 508) (mptSetRecordWalkPc + 208)),
    .LI .x5 (2 : Word),
    .BEQ .x10 .x5 (brOff (mptSetRecordWalkPc + 920) (mptSetRecordWalkPc + 216)),
    .JAL .x0 (jalOff (mptSetRecordWalkPc + 1140) (mptSetRecordWalkPc + 220)),
    .BEQ .x22 .x19 (brOff (mptSetRecordWalkPc + 480) (mptSetRecordWalkPc + 224)),
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
    .AUIPC .x13 (laHi GuestAddrs.mw_child_offset (mptSetRecordWalkPc + 276)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_child_offset (mptSetRecordWalkPc + 276)),
    .AUIPC .x14 (laHi GuestAddrs.mw_child_length (mptSetRecordWalkPc + 284)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_child_length (mptSetRecordWalkPc + 284)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (mptSetRecordWalkPc + 292)),
    .ADDI .x22 .x22 (1 : BitVec 12),
    .BNE .x10 .x0 (brOff (mptSetRecordWalkPc + 1140) (mptSetRecordWalkPc + 300)),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_length (mptSetRecordWalkPc + 304)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_length (mptSetRecordWalkPc + 304)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (brOff (mptSetRecordWalkPc + 1132) (mptSetRecordWalkPc + 316)),
    .LI .x7 (32 : Word),
    .BEQ .x6 .x7 (28 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_offset (mptSetRecordWalkPc + 328)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_offset (mptSetRecordWalkPc + 328)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x7,
    .MV .x24 .x6,
    .JAL .x0 (jalOff (mptSetRecordWalkPc + 188) (mptSetRecordWalkPc + 348)),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_offset (mptSetRecordWalkPc + 352)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_offset (mptSetRecordWalkPc + 352)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x7 .x23 .x6,
    .AUIPC .x28 (laHi GuestAddrs.mw_lookup_hash (mptSetRecordWalkPc + 368)),
    .ADDI .x28 .x28 (laLo GuestAddrs.mw_lookup_hash (mptSetRecordWalkPc + 368)),
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
    .AUIPC .x12 (laHi GuestAddrs.mw_lookup_hash (mptSetRecordWalkPc + 416)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mw_lookup_hash (mptSetRecordWalkPc + 416)),
    .AUIPC .x13 (laHi GuestAddrs.mw_lookup_offset (mptSetRecordWalkPc + 424)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_lookup_offset (mptSetRecordWalkPc + 424)),
    .AUIPC .x14 (laHi GuestAddrs.mw_lookup_length (mptSetRecordWalkPc + 432)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_lookup_length (mptSetRecordWalkPc + 432)),
    .JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash (mptSetRecordWalkPc + 440)),
    .BNE .x10 .x0 (brOff (mptSetRecordWalkPc + 1132) (mptSetRecordWalkPc + 444)),
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_offset (mptSetRecordWalkPc + 448)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_offset (mptSetRecordWalkPc + 448)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x8 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_length (mptSetRecordWalkPc + 464)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_length (mptSetRecordWalkPc + 464)),
    .LD .x24 .x5 (0 : BitVec 12),
    .JAL .x0 (jalOff (mptSetRecordWalkPc + 188) (mptSetRecordWalkPc + 476)),
    .SD .x21 .x25 (0 : BitVec 12),
    .SD .x21 .x22 (8 : BitVec 12),
    .SUB .x5 .x23 .x8,
    .SD .x21 .x5 (16 : BitVec 12),
    .SD .x21 .x24 (24 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (jalOff (mptSetRecordWalkPc + 1144) (mptSetRecordWalkPc + 504)),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mw_path_offset (mptSetRecordWalkPc + 520)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_path_offset (mptSetRecordWalkPc + 520)),
    .AUIPC .x14 (laHi GuestAddrs.mw_path_length (mptSetRecordWalkPc + 528)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_path_length (mptSetRecordWalkPc + 528)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (mptSetRecordWalkPc + 536)),
    .BNE .x10 .x0 (brOff (mptSetRecordWalkPc + 1140) (mptSetRecordWalkPc + 540)),
    .AUIPC .x5 (laHi GuestAddrs.mw_path_offset (mptSetRecordWalkPc + 544)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_offset (mptSetRecordWalkPc + 544)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x10 .x23 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mw_path_length (mptSetRecordWalkPc + 560)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_length (mptSetRecordWalkPc + 560)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.mw_nibble_buf (mptSetRecordWalkPc + 572)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mw_nibble_buf (mptSetRecordWalkPc + 572)),
    .AUIPC .x13 (laHi GuestAddrs.mw_nibble_count (mptSetRecordWalkPc + 580)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_nibble_count (mptSetRecordWalkPc + 580)),
    .AUIPC .x14 (laHi GuestAddrs.mw_is_leaf (mptSetRecordWalkPc + 588)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_is_leaf (mptSetRecordWalkPc + 588)),
    .JAL .x1 (jalOff GuestAddrs.hp_decode_nibbles (mptSetRecordWalkPc + 596)),
    .BNE .x10 .x0 (brOff (mptSetRecordWalkPc + 1140) (mptSetRecordWalkPc + 600)),
    .AUIPC .x5 (laHi GuestAddrs.mw_is_leaf (mptSetRecordWalkPc + 604)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_is_leaf (mptSetRecordWalkPc + 604)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BNE .x6 .x0 (brOff (mptSetRecordWalkPc + 1140) (mptSetRecordWalkPc + 616)),
    .AUIPC .x5 (laHi GuestAddrs.mw_nibble_count (mptSetRecordWalkPc + 620)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_nibble_count (mptSetRecordWalkPc + 620)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x7 .x22 .x6,
    .BLTU .x19 .x7 (brOff (mptSetRecordWalkPc + 1132) (mptSetRecordWalkPc + 636)),
    .AUIPC .x7 (laHi GuestAddrs.mw_nibble_buf (mptSetRecordWalkPc + 640)),
    .ADDI .x7 .x7 (laLo GuestAddrs.mw_nibble_buf (mptSetRecordWalkPc + 640)),
    .ADD .x28 .x18 .x22,
    .MV .x29 .x6,
    .BEQ .x29 .x0 (32 : BitVec 13),
    .LBU .x30 .x7 (0 : BitVec 12),
    .LBU .x31 .x28 (0 : BitVec 12),
    .BNE .x30 .x31 (brOff (mptSetRecordWalkPc + 1132) (mptSetRecordWalkPc + 668)),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADD .x22 .x22 .x6,
    .SUB .x7 .x23 .x8,
    .SD .x20 .x7 (0 : BitVec 12),
    .SD .x20 .x24 (8 : BitVec 12),
    .LI .x28 (1 : Word),
    .SD .x20 .x28 (16 : BitVec 12),
    .SD .x20 .x0 (24 : BitVec 12),
    .ADDI .x20 .x20 (32 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .LI .x12 (1 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mw_child_offset (mptSetRecordWalkPc + 736)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_child_offset (mptSetRecordWalkPc + 736)),
    .AUIPC .x14 (laHi GuestAddrs.mw_child_length (mptSetRecordWalkPc + 744)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_child_length (mptSetRecordWalkPc + 744)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (mptSetRecordWalkPc + 752)),
    .BNE .x10 .x0 (brOff (mptSetRecordWalkPc + 1140) (mptSetRecordWalkPc + 756)),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_length (mptSetRecordWalkPc + 760)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_length (mptSetRecordWalkPc + 760)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_offset (mptSetRecordWalkPc + 772)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_offset (mptSetRecordWalkPc + 772)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x28 .x23 .x7,
    .LI .x29 (32 : Word),
    .BEQ .x6 .x29 (16 : BitVec 13),
    .MV .x23 .x28,
    .MV .x24 .x6,
    .JAL .x0 (jalOff (mptSetRecordWalkPc + 188) (mptSetRecordWalkPc + 804)),
    .AUIPC .x29 (laHi GuestAddrs.mw_lookup_hash (mptSetRecordWalkPc + 808)),
    .ADDI .x29 .x29 (laLo GuestAddrs.mw_lookup_hash (mptSetRecordWalkPc + 808)),
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
    .AUIPC .x12 (laHi GuestAddrs.mw_lookup_hash (mptSetRecordWalkPc + 856)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mw_lookup_hash (mptSetRecordWalkPc + 856)),
    .AUIPC .x13 (laHi GuestAddrs.mw_lookup_offset (mptSetRecordWalkPc + 864)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_lookup_offset (mptSetRecordWalkPc + 864)),
    .AUIPC .x14 (laHi GuestAddrs.mw_lookup_length (mptSetRecordWalkPc + 872)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_lookup_length (mptSetRecordWalkPc + 872)),
    .JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash (mptSetRecordWalkPc + 880)),
    .BNE .x10 .x0 (brOff (mptSetRecordWalkPc + 1132) (mptSetRecordWalkPc + 884)),
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_offset (mptSetRecordWalkPc + 888)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_offset (mptSetRecordWalkPc + 888)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x8 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mw_lookup_length (mptSetRecordWalkPc + 904)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_lookup_length (mptSetRecordWalkPc + 904)),
    .LD .x24 .x5 (0 : BitVec 12),
    .JAL .x0 (jalOff (mptSetRecordWalkPc + 188) (mptSetRecordWalkPc + 916)),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mw_path_offset (mptSetRecordWalkPc + 932)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_path_offset (mptSetRecordWalkPc + 932)),
    .AUIPC .x14 (laHi GuestAddrs.mw_path_length (mptSetRecordWalkPc + 940)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_path_length (mptSetRecordWalkPc + 940)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (mptSetRecordWalkPc + 948)),
    .BNE .x10 .x0 (brOff (mptSetRecordWalkPc + 1140) (mptSetRecordWalkPc + 952)),
    .AUIPC .x5 (laHi GuestAddrs.mw_path_offset (mptSetRecordWalkPc + 956)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_offset (mptSetRecordWalkPc + 956)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x10 .x23 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mw_path_length (mptSetRecordWalkPc + 972)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_length (mptSetRecordWalkPc + 972)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.mw_nibble_buf (mptSetRecordWalkPc + 984)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mw_nibble_buf (mptSetRecordWalkPc + 984)),
    .AUIPC .x13 (laHi GuestAddrs.mw_nibble_count (mptSetRecordWalkPc + 992)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_nibble_count (mptSetRecordWalkPc + 992)),
    .AUIPC .x14 (laHi GuestAddrs.mw_is_leaf (mptSetRecordWalkPc + 1000)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_is_leaf (mptSetRecordWalkPc + 1000)),
    .JAL .x1 (jalOff GuestAddrs.hp_decode_nibbles (mptSetRecordWalkPc + 1008)),
    .BNE .x10 .x0 (brOff (mptSetRecordWalkPc + 1140) (mptSetRecordWalkPc + 1012)),
    .AUIPC .x5 (laHi GuestAddrs.mw_is_leaf (mptSetRecordWalkPc + 1016)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_is_leaf (mptSetRecordWalkPc + 1016)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (1 : Word),
    .BNE .x6 .x7 (brOff (mptSetRecordWalkPc + 1140) (mptSetRecordWalkPc + 1032)),
    .AUIPC .x5 (laHi GuestAddrs.mw_nibble_count (mptSetRecordWalkPc + 1036)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_nibble_count (mptSetRecordWalkPc + 1036)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SUB .x7 .x19 .x22,
    .BNE .x6 .x7 (brOff (mptSetRecordWalkPc + 1132) (mptSetRecordWalkPc + 1052)),
    .AUIPC .x7 (laHi GuestAddrs.mw_nibble_buf (mptSetRecordWalkPc + 1056)),
    .ADDI .x7 .x7 (laLo GuestAddrs.mw_nibble_buf (mptSetRecordWalkPc + 1056)),
    .ADD .x28 .x18 .x22,
    .MV .x29 .x6,
    .BEQ .x29 .x0 (32 : BitVec 13),
    .LBU .x30 .x7 (0 : BitVec 12),
    .LBU .x31 .x28 (0 : BitVec 12),
    .BNE .x30 .x31 (48 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .SD .x21 .x25 (0 : BitVec 12),
    .SD .x21 .x22 (8 : BitVec 12),
    .SUB .x5 .x23 .x8,
    .SD .x21 .x5 (16 : BitVec 12),
    .SD .x21 .x24 (24 : BitVec 12),
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

/-- Reloc side-table for `mptSetRecordWalk_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptSetRecordWalk_relocs : RelocTable :=
  [ (19, .la .x5 "mw_lookup_hash"),
    (31, .la .x12 "mw_lookup_hash"),
    (33, .la .x13 "mw_lookup_offset"),
    (35, .la .x14 "mw_lookup_length"),
    (37, .jal .x1 "witness_lookup_by_hash"),
    (39, .la .x5 "mw_lookup_offset"),
    (43, .la .x5 "mw_lookup_length"),
    (49, .jal .x1 "mpt_node_kind"),
    (69, .la .x13 "mw_child_offset"),
    (71, .la .x14 "mw_child_length"),
    (73, .jal .x1 "rlp_list_nth_item"),
    (76, .la .x5 "mw_child_length"),
    (82, .la .x5 "mw_child_offset"),
    (88, .la .x5 "mw_child_offset"),
    (92, .la .x28 "mw_lookup_hash"),
    (104, .la .x12 "mw_lookup_hash"),
    (106, .la .x13 "mw_lookup_offset"),
    (108, .la .x14 "mw_lookup_length"),
    (110, .jal .x1 "witness_lookup_by_hash"),
    (112, .la .x5 "mw_lookup_offset"),
    (116, .la .x5 "mw_lookup_length"),
    (130, .la .x13 "mw_path_offset"),
    (132, .la .x14 "mw_path_length"),
    (134, .jal .x1 "rlp_list_nth_item"),
    (136, .la .x5 "mw_path_offset"),
    (140, .la .x5 "mw_path_length"),
    (143, .la .x12 "mw_nibble_buf"),
    (145, .la .x13 "mw_nibble_count"),
    (147, .la .x14 "mw_is_leaf"),
    (149, .jal .x1 "hp_decode_nibbles"),
    (151, .la .x5 "mw_is_leaf"),
    (155, .la .x5 "mw_nibble_count"),
    (160, .la .x7 "mw_nibble_buf"),
    (184, .la .x13 "mw_child_offset"),
    (186, .la .x14 "mw_child_length"),
    (188, .jal .x1 "rlp_list_nth_item"),
    (190, .la .x5 "mw_child_length"),
    (193, .la .x5 "mw_child_offset"),
    (202, .la .x29 "mw_lookup_hash"),
    (214, .la .x12 "mw_lookup_hash"),
    (216, .la .x13 "mw_lookup_offset"),
    (218, .la .x14 "mw_lookup_length"),
    (220, .jal .x1 "witness_lookup_by_hash"),
    (222, .la .x5 "mw_lookup_offset"),
    (226, .la .x5 "mw_lookup_length"),
    (233, .la .x13 "mw_path_offset"),
    (235, .la .x14 "mw_path_length"),
    (237, .jal .x1 "rlp_list_nth_item"),
    (239, .la .x5 "mw_path_offset"),
    (243, .la .x5 "mw_path_length"),
    (246, .la .x12 "mw_nibble_buf"),
    (248, .la .x13 "mw_nibble_count"),
    (250, .la .x14 "mw_is_leaf"),
    (252, .jal .x1 "hp_decode_nibbles"),
    (254, .la .x5 "mw_is_leaf"),
    (259, .la .x5 "mw_nibble_count"),
    (264, .la .x7 "mw_nibble_buf") ]

def mptSetRecordWalkFunction : String :=
  "mpt_set_record_walk:\n" ++ emitProgramR mptSetRecordWalk_prog mptSetRecordWalk_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptSetRecordWalk_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptSetRecordWalkFunction_eq_prog :
    mptSetRecordWalkFunction = "mpt_set_record_walk:\n" ++ emitProgramR mptSetRecordWalk_prog mptSetRecordWalk_relocs := rfl

#guard mptSetRecordWalkFunction.startsWith "mpt_set_record_walk:\n"
#guard mptSetRecordWalk_prog.length = 299
/-- `zisk_mpt_set_record_walk`: probe BuildUnit. Reuses the `mpt_set` probe
    input layout (scripts/mpt_ref.py `build_probe_input`): the new_value
    field is present but ignored by the record-walk.
    Input layout (file maps to INPUT+8 at 0x40000000):
      INPUT+8  : witness_len (u64)
      INPUT+16 : path_len (u64)
      INPUT+24 : new_value_len (u64)         [ignored here]
      INPUT+32 : root_hash (32 bytes)
      INPUT+64 : path_nibbles (1B each)
      INPUT+64+path_len : new_value
      8-aligned : witness section
    Output layout:
      OUTPUT+0   : status (0 found / 1 not / 2 fail)
      OUTPUT+8   : meta (depth, consumed, leaf_offset, leaf_len) -- 32 B
      OUTPUT+128 : stack records, 32 B each (node_offset, node_len, kind,
                   nibble), in root->leaf order -/
def ziskMptSetRecordWalkPrologue : String :=
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
  "  jal ra, mpt_set_record_walk\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Lmsrw_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  mptSetRecordWalkFunction ++ "\n" ++
  ".Lmsrw_pdone:"


/-! ## mset_memcpy -- byte copy (leaf helper)

    a0 = dst, a1 = src, a2 = len. Advances a0/a1/a2; clobbers t0.
    Leaf-callable (no jal), preserves all s-registers and ra. -/
def msetMemcpy_prog : Program :=
  [ .BEQ .x12 .x0 (28 : BitVec 13),
    .LBU .x5 .x11 (0 : BitVec 12),
    .SB .x10 .x5 (0 : BitVec 12),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x11 .x11 (1 : BitVec 12),
    .ADDI .x12 .x12 (-1 : BitVec 12),
    .BNE .x12 .x0 (-20 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def msetMemcpyFunction : String :=
  "mset_memcpy:\n" ++ emitProgram msetMemcpy_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `msetMemcpy_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem msetMemcpyFunction_eq_prog :
    msetMemcpyFunction = "mset_memcpy:\n" ++ emitProgram msetMemcpy_prog := rfl

#guard msetMemcpyFunction.startsWith "mset_memcpy:\n"
#guard msetMemcpy_prog.length = 8
/-! ## mpt_splice_slot -- replace one list item with a new reference

    Given an RLP list (a branch or extension node) and the byte span of its
    item `k` (found via `rlp_item_span`), produce a new RLP list identical to
    the original except item `k` is replaced by `new_ref`, with a freshly
    computed list prefix. This is the per-level bubble-up step: for a value-
    only update every ancestor node is byte-identical to its original except
    the single child slot on the path, so re-splicing the ORIGINAL node (read
    from the stable witness) with the new child ref yields the new node.

    Calling convention:
      a0 (input)  : src list RLP ptr
      a1 (input)  : src list RLP length
      a2 (input)  : item index k to replace (branch: child nibble; ext: 1)
      a3 (input)  : new_ref ptr (already-encoded slot bytes)
      a4 (input)  : new_ref length
      a5 (input)  : output buffer ptr (caller-supplied, distinct from src)
      a6 (input)  : u64 out length ptr
      ra (input)  : return
      a0 (output) : 0 (ok) / 1 (parse fail / k out of range)

    new_payload = src[payload_start..slot_start] ++ new_ref
                  ++ src[slot_start+slot_size..src_len]
    out         = rlp_encode_list_prefix(len(new_payload)) ++ new_payload -/
def mptSpliceSlot_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mset_span_start (GuestAddrs.mpt_splice_slot + 76)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mset_span_start (GuestAddrs.mpt_splice_slot + 76)),
    .AUIPC .x14 (laHi GuestAddrs.mset_span_size (GuestAddrs.mpt_splice_slot + 84)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mset_span_size (GuestAddrs.mpt_splice_slot + 84)),
    .JAL .x1 (jalOff GuestAddrs.rlp_item_span (GuestAddrs.mpt_splice_slot + 92)),
    .BNE .x10 .x0 (436 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mset_span_start (GuestAddrs.mpt_splice_slot + 100)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_span_start (GuestAddrs.mpt_splice_slot + 100)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_payload_start (GuestAddrs.mpt_splice_slot + 112)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_payload_start (GuestAddrs.mpt_splice_slot + 112)),
    .SD .x5 .x6 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .AUIPC .x13 (laHi GuestAddrs.mset_span_start (GuestAddrs.mpt_splice_slot + 136)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mset_span_start (GuestAddrs.mpt_splice_slot + 136)),
    .AUIPC .x14 (laHi GuestAddrs.mset_span_size (GuestAddrs.mpt_splice_slot + 144)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mset_span_size (GuestAddrs.mpt_splice_slot + 144)),
    .JAL .x1 (jalOff GuestAddrs.rlp_item_span (GuestAddrs.mpt_splice_slot + 152)),
    .BNE .x10 .x0 (376 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mset_span_start (GuestAddrs.mpt_splice_slot + 160)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_span_start (GuestAddrs.mpt_splice_slot + 160)),
    .LD .x7 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_span_size (GuestAddrs.mpt_splice_slot + 172)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_span_size (GuestAddrs.mpt_splice_slot + 172)),
    .LD .x28 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_payload_start (GuestAddrs.mpt_splice_slot + 184)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_payload_start (GuestAddrs.mpt_splice_slot + 184)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SUB .x29 .x7 .x6,
    .ADD .x30 .x7 .x28,
    .SUB .x31 .x9 .x30,
    .AUIPC .x5 (laHi GuestAddrs.mset_head_len (GuestAddrs.mpt_splice_slot + 208)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_head_len (GuestAddrs.mpt_splice_slot + 208)),
    .SD .x5 .x29 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_tail_start (GuestAddrs.mpt_splice_slot + 220)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_tail_start (GuestAddrs.mpt_splice_slot + 220)),
    .SD .x5 .x30 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_tail_len (GuestAddrs.mpt_splice_slot + 232)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_tail_len (GuestAddrs.mpt_splice_slot + 232)),
    .SD .x5 .x31 (0 : BitVec 12),
    .ADD .x6 .x29 .x20,
    .ADD .x6 .x6 .x31,
    .AUIPC .x5 (laHi GuestAddrs.mset_new_payload_len (GuestAddrs.mpt_splice_slot + 252)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_new_payload_len (GuestAddrs.mpt_splice_slot + 252)),
    .SD .x5 .x6 (0 : BitVec 12),
    .MV .x10 .x6,
    .MV .x11 .x21,
    .AUIPC .x12 (laHi GuestAddrs.mset_prefix_len (GuestAddrs.mpt_splice_slot + 272)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mset_prefix_len (GuestAddrs.mpt_splice_slot + 272)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_list_prefix (GuestAddrs.mpt_splice_slot + 280)),
    .AUIPC .x5 (laHi GuestAddrs.mset_prefix_len (GuestAddrs.mpt_splice_slot + 284)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_prefix_len (GuestAddrs.mpt_splice_slot + 284)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x7 .x21 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mset_cursor (GuestAddrs.mpt_splice_slot + 300)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_cursor (GuestAddrs.mpt_splice_slot + 300)),
    .SD .x5 .x7 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_cursor (GuestAddrs.mpt_splice_slot + 312)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_cursor (GuestAddrs.mpt_splice_slot + 312)),
    .LD .x10 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_payload_start (GuestAddrs.mpt_splice_slot + 324)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_payload_start (GuestAddrs.mpt_splice_slot + 324)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x11 .x8 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mset_head_len (GuestAddrs.mpt_splice_slot + 340)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_head_len (GuestAddrs.mpt_splice_slot + 340)),
    .LD .x12 .x5 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.mset_memcpy (GuestAddrs.mpt_splice_slot + 352)),
    .AUIPC .x5 (laHi GuestAddrs.mset_cursor (GuestAddrs.mpt_splice_slot + 356)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_cursor (GuestAddrs.mpt_splice_slot + 356)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_head_len (GuestAddrs.mpt_splice_slot + 368)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_head_len (GuestAddrs.mpt_splice_slot + 368)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x6 .x6 .x7,
    .AUIPC .x5 (laHi GuestAddrs.mset_cursor (GuestAddrs.mpt_splice_slot + 384)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_cursor (GuestAddrs.mpt_splice_slot + 384)),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_cursor (GuestAddrs.mpt_splice_slot + 396)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_cursor (GuestAddrs.mpt_splice_slot + 396)),
    .LD .x10 .x5 (0 : BitVec 12),
    .MV .x11 .x19,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.mset_memcpy (GuestAddrs.mpt_splice_slot + 416)),
    .AUIPC .x5 (laHi GuestAddrs.mset_cursor (GuestAddrs.mpt_splice_slot + 420)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_cursor (GuestAddrs.mpt_splice_slot + 420)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x6 .x6 .x20,
    .AUIPC .x5 (laHi GuestAddrs.mset_cursor (GuestAddrs.mpt_splice_slot + 436)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_cursor (GuestAddrs.mpt_splice_slot + 436)),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_cursor (GuestAddrs.mpt_splice_slot + 448)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_cursor (GuestAddrs.mpt_splice_slot + 448)),
    .LD .x10 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_tail_start (GuestAddrs.mpt_splice_slot + 460)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_tail_start (GuestAddrs.mpt_splice_slot + 460)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x11 .x8 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mset_tail_len (GuestAddrs.mpt_splice_slot + 476)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_tail_len (GuestAddrs.mpt_splice_slot + 476)),
    .LD .x12 .x5 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.mset_memcpy (GuestAddrs.mpt_splice_slot + 488)),
    .AUIPC .x5 (laHi GuestAddrs.mset_prefix_len (GuestAddrs.mpt_splice_slot + 492)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_prefix_len (GuestAddrs.mpt_splice_slot + 492)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_new_payload_len (GuestAddrs.mpt_splice_slot + 504)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_new_payload_len (GuestAddrs.mpt_splice_slot + 504)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x6 .x6 .x7,
    .SD .x22 .x6 (0 : BitVec 12),
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
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `mptSpliceSlot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptSpliceSlot_relocs : RelocTable :=
  [ (19, .la .x13 "mset_span_start"),
    (21, .la .x14 "mset_span_size"),
    (23, .jal .x1 "rlp_item_span"),
    (25, .la .x5 "mset_span_start"),
    (28, .la .x5 "mset_payload_start"),
    (34, .la .x13 "mset_span_start"),
    (36, .la .x14 "mset_span_size"),
    (38, .jal .x1 "rlp_item_span"),
    (40, .la .x5 "mset_span_start"),
    (43, .la .x5 "mset_span_size"),
    (46, .la .x5 "mset_payload_start"),
    (52, .la .x5 "mset_head_len"),
    (55, .la .x5 "mset_tail_start"),
    (58, .la .x5 "mset_tail_len"),
    (63, .la .x5 "mset_new_payload_len"),
    (68, .la .x12 "mset_prefix_len"),
    (70, .jal .x1 "rlp_encode_list_prefix"),
    (71, .la .x5 "mset_prefix_len"),
    (75, .la .x5 "mset_cursor"),
    (78, .la .x5 "mset_cursor"),
    (81, .la .x5 "mset_payload_start"),
    (85, .la .x5 "mset_head_len"),
    (88, .jal .x1 "mset_memcpy"),
    (89, .la .x5 "mset_cursor"),
    (92, .la .x5 "mset_head_len"),
    (96, .la .x5 "mset_cursor"),
    (99, .la .x5 "mset_cursor"),
    (104, .jal .x1 "mset_memcpy"),
    (105, .la .x5 "mset_cursor"),
    (109, .la .x5 "mset_cursor"),
    (112, .la .x5 "mset_cursor"),
    (115, .la .x5 "mset_tail_start"),
    (119, .la .x5 "mset_tail_len"),
    (122, .jal .x1 "mset_memcpy"),
    (123, .la .x5 "mset_prefix_len"),
    (126, .la .x5 "mset_new_payload_len") ]

def mptSpliceSlotFunction : String :=
  "mpt_splice_slot:\n" ++ emitProgramR mptSpliceSlot_prog mptSpliceSlot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptSpliceSlot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptSpliceSlotFunction_eq_prog :
    mptSpliceSlotFunction = "mpt_splice_slot:\n" ++ emitProgramR mptSpliceSlot_prog mptSpliceSlot_relocs := rfl

#guard mptSpliceSlotFunction.startsWith "mpt_splice_slot:\n"
#guard mptSpliceSlot_prog.length = 144
/-! ## mpt_set -- value-only update of an existing key, recompute root

    Compose record-walk + bubble-up: descend to the leaf (recording the
    branch/extension nodes on the path), re-encode the leaf with `new_value`,
    then walk back up re-encoding each ancestor's touched child slot, hashing
    at every >=32-byte boundary, and keccak the final root node.

    Scope: VALUE-ONLY update of an EXISTING key (no insert/delete, no
    structural change) -- covers existing-account and existing-slot updates.

    Calling convention:
      a0 (input)  : root_hash ptr (32 bytes)
      a1 (input)  : witness section ptr
      a2 (input)  : witness section length
      a3 (input)  : path_nibbles ptr (one byte per nibble)
      a4 (input)  : path_nibbles length
      a5 (input)  : new_value ptr
      a6 (input)  : new_value length
      a7 (input)  : out_root ptr (32 bytes, written on success)
      ra (input)  : return
      a0 (output) : 0 (ok) / 1 (key not found) / 2 (parse / splice fail) -/
def mptSetFunction : String :=
  "mpt_set:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a1                   # witness\n" ++
  "  mv s1, a3                   # path\n" ++
  "  mv s2, a4                   # path_len\n" ++
  "  mv s3, a5                   # new_value\n" ++
  "  mv s4, a6                   # new_value_len\n" ++
  "  mv s5, a7                   # out_root\n" ++
  "  # ---- record-walk (a0=root_hash, a2=witness_len unchanged) ----\n" ++
  "  mv a1, s0\n" ++
  "  mv a3, s1\n" ++
  "  mv a4, s2\n" ++
  "  la a5, mset_stack\n" ++
  "  la a6, mset_meta\n" ++
  "  jal ra, mpt_set_record_walk\n" ++
  "  bnez a0, .Lmset_ret         # propagate not-found / parse-fail\n" ++
  "  la t0, mset_meta\n" ++
  "  ld s6, 0(t0)                # depth\n" ++
  "  ld s8, 8(t0)                # consumed nibbles\n" ++
  "  # ---- re-encode leaf from path[consumed:] + new_value ----\n" ++
  "  add a0, s1, s8              # path + consumed\n" ++
  "  sub a1, s2, s8              # path_len - consumed\n" ++
  "  mv a2, s3                   # new_value\n" ++
  "  mv a3, s4                   # new_value_len\n" ++
  "  la a4, mset_node\n" ++
  "  la a5, mset_node_len\n" ++
  "  jal ra, mpt_leaf_node_encode_from_nibbles\n" ++
  "  bnez a0, .Lmset_ret\n" ++
  "  la t0, mset_node_len; ld s9, 0(t0)   # current node len\n" ++
  "  # ---- current_ref = node_slot_encode(node) ----\n" ++
  "  la a0, mset_node\n" ++
  "  mv a1, s9\n" ++
  "  la a2, mset_ref\n" ++
  "  la a3, mset_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  # ---- bubble up: process records depth-1 .. 0 ----\n" ++
  "  mv s7, s6                   # i = depth\n" ++
  ".Lmset_bubble:\n" ++
  "  beqz s7, .Lmset_root\n" ++
  "  addi s7, s7, -1\n" ++
  "  la t0, mset_stack\n" ++
  "  slli t1, s7, 5              # 32 * i\n" ++
  "  add t0, t0, t1              # &record[i]\n" ++
  "  ld t2, 0(t0)                # node_offset\n" ++
  "  ld t3, 8(t0)                # node_len\n" ++
  "  ld t4, 16(t0)               # kind (0 branch / 1 ext)\n" ++
  "  ld t5, 24(t0)               # nibble\n" ++
  "  add a0, s0, t2              # src = witness + node_offset\n" ++
  "  mv a1, t3                   # src_len\n" ++
  "  beqz t4, .Lmset_k_branch\n" ++
  "  li a2, 1                    # extension: replace item 1\n" ++
  "  j .Lmset_k_done\n" ++
  ".Lmset_k_branch:\n" ++
  "  mv a2, t5                   # branch: replace item[nibble]\n" ++
  ".Lmset_k_done:\n" ++
  "  la a3, mset_ref\n" ++
  "  la t0, mset_ref_len; ld a4, 0(t0)\n" ++
  "  la a5, mset_node            # out (overwrite -- src is in witness)\n" ++
  "  la a6, mset_node_len\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  bnez a0, .Lmset_fail\n" ++
  "  la t0, mset_node_len; ld s9, 0(t0)\n" ++
  "  la a0, mset_node\n" ++
  "  mv a1, s9\n" ++
  "  la a2, mset_ref\n" ++
  "  la a3, mset_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  j .Lmset_bubble\n" ++
  ".Lmset_root:\n" ++
  "  # mset_node holds the new root node (len s9); root = keccak256(node).\n" ++
  "  la a0, mset_node\n" ++
  "  mv a1, s9\n" ++
  "  mv a2, s5                   # out_root\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  ".Lmset_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret\n" ++
  ".Lmset_fail:\n" ++
  "  li a0, 2\n" ++
  "  j .Lmset_ret"

/-- `zisk_mpt_set`: probe BuildUnit. Reuses `scripts/mpt_ref.py`
    `build_probe_input` (the layout the record-walk probe also reads), and
    writes the recomputed 32-byte new root to OUTPUT+0 so the existing
    `scripts/codegen-zisk-mpt-set-check.sh` compares it against the reference.
    Input layout (file maps to INPUT+8 at 0x40000000):
      INPUT+8 witness_len, +16 path_len, +24 new_value_len,
      +32 root_hash (32B), +64 path nibbles, then new_value,
      8-aligned witness section.
    Output layout:
      OUTPUT+0  : 32-byte recomputed new root
      OUTPUT+32 : status (0 ok / 1 not-found / 2 fail) -/
def ziskMptSetPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a2, 8(t0)                # witness_len\n" ++
  "  ld a4, 16(t0)               # path_len\n" ++
  "  ld a6, 24(t0)               # new_value_len\n" ++
  "  addi a0, t0, 32             # root_hash ptr (INPUT+32)\n" ++
  "  addi a3, t0, 64             # path ptr (INPUT+64)\n" ++
  "  add a5, a3, a4              # new_value ptr = path + path_len\n" ++
  "  # witness ptr = path_ptr + roundup8(path_len + new_value_len).\n" ++
  "  add t1, a4, a6\n" ++
  "  addi t1, t1, 7\n" ++
  "  andi t1, t1, -8\n" ++
  "  add a1, a3, t1             # witness ptr\n" ++
  "  li a7, 0xa0010000          # out_root at OUTPUT+0 (32 B)\n" ++
  "  jal ra, mpt_set\n" ++
  "  li t0, 0xa0010020\n" ++
  "  sd a0, 0(t0)               # status at OUTPUT+32\n" ++
  "  j .Lmset_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  mptSetRecordWalkFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  mptSetFunction ++ "\n" ++
  ".Lmset_pdone:"

/-- Merged data section for the `zisk_mpt_set` probe: the record-walk +
    helper scratch (`ziskMptWalkDataSection`: zk3_state, wlh_scratch_hash,
    mnk_*, mw_*) plus the leaf-encoder scratch (`mlnen_*`) plus mpt_set's own
    splice scratch and buffers (`mset_*`). All labels are disjoint. -/
def ziskMptSetDataSection : String :=
  ziskMptWalkDataSection ++ "\n" ++
  ".balign 8\n" ++
  "mlnen_field_len:\n  .zero 8\n" ++
  "mlnen_hp_len:\n  .zero 8\n" ++
  "mlnen_cursor:\n  .zero 8\n" ++
  "mlnen_total_payload:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "mlnen_hp_buf:\n  .zero 1024\n" ++
  ".balign 8\n" ++
  "mlnen_payload_buf:\n  .zero 1048576\n" ++
  ".balign 8\n" ++
  "mset_span_start:\n  .zero 8\n" ++
  "mset_span_size:\n  .zero 8\n" ++
  "mset_payload_start:\n  .zero 8\n" ++
  "mset_head_len:\n  .zero 8\n" ++
  "mset_tail_start:\n  .zero 8\n" ++
  "mset_tail_len:\n  .zero 8\n" ++
  "mset_new_payload_len:\n  .zero 8\n" ++
  "mset_prefix_len:\n  .zero 8\n" ++
  "mset_cursor:\n  .zero 8\n" ++
  "mset_node_len:\n  .zero 8\n" ++
  "mset_ref_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "mset_meta:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "mset_stack:\n  .zero 2048\n" ++
  ".balign 8\n" ++
  "mset_ref:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "mset_node:\n  .zero 2048"


end EvmAsm.Codegen
