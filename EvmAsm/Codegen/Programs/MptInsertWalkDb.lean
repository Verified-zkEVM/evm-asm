/-
  EvmAsm.Codegen.Programs.MptInsertWalkDb

  mpt_insert_walk_db (bead evm-asm-fhsxz.2.4.2.6.5): the DB-aware divergence
  walk -- identical classification to mpt_insert_walk (Programs/MptInsertWalk),
  but every node hash is resolved via `mpt_node_resolve` (witness SSZ section
  THEN the appendable node DB) and the recorded node pointers are ABSOLUTE
  (a multi-change ancestor can live in the DB, not the witness).

  This is the insert analogue of mpt_set_record_walk_db (Programs/MptSetAcc),
  and is what mpt_insert_acc descends with so that an insert change in
  mpt_state_root sees the new nodes appended by prior changes.

  meta_out / stack_out layout matches mpt_insert_walk EXCEPT the node pointers
  are absolute (stack record +0 = node_ptr_ABS; meta +24 = terminal_ptr_ABS).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.MptInsertWalk
import EvmAsm.Codegen.Programs.MptSetAcc

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## mpt_insert_walk_db -- classify divergence, resolving via witness+DB.

    ABI matches mpt_insert_walk (a0=root_hash, a1=witness, a2=witness_len,
    a3=path, a4=path_len, a5=stack_out, a6=meta_out -> a0 = 0/1/2), but node
    pointers are ABSOLUTE. The node DB (mset_db_*) must be initialised by the
    caller (mpt_state_root / the probe). -/
def mptInsertWalkDb_prog : Program :=
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
    .AUIPC .x7 (laHi GuestAddrs.iw_empty_trie_root (GuestAddrs.mpt_insert_walk_db + 76)),
    .ADDI .x7 .x7 (laLo GuestAddrs.iw_empty_trie_root (GuestAddrs.mpt_insert_walk_db + 76)),
    .LD .x28 .x10 (0 : BitVec 12),
    .LD .x29 .x7 (0 : BitVec 12),
    .BNE .x28 .x29 (48 : BitVec 13),
    .LD .x28 .x10 (8 : BitVec 12),
    .LD .x29 .x7 (8 : BitVec 12),
    .BNE .x28 .x29 (36 : BitVec 13),
    .LD .x28 .x10 (16 : BitVec 12),
    .LD .x29 .x7 (16 : BitVec 12),
    .BNE .x28 .x29 (24 : BitVec 13),
    .LD .x28 .x10 (24 : BitVec 12),
    .LD .x29 .x7 (24 : BitVec 12),
    .BNE .x28 .x29 (12 : BitVec 13),
    .LI .x30 (3 : Word),
    .JAL .x0 (1064 : BitVec 21),
    .MV .x12 .x10,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x13 (laHi GuestAddrs.iwd_ptr (GuestAddrs.mpt_insert_walk_db + 152)),
    .ADDI .x13 .x13 (laLo GuestAddrs.iwd_ptr (GuestAddrs.mpt_insert_walk_db + 152)),
    .AUIPC .x14 (laHi GuestAddrs.iwd_len (GuestAddrs.mpt_insert_walk_db + 160)),
    .ADDI .x14 .x14 (laLo GuestAddrs.iwd_len (GuestAddrs.mpt_insert_walk_db + 160)),
    .JAL .x1 (jalOff GuestAddrs.mpt_node_resolve (GuestAddrs.mpt_insert_walk_db + 168)),
    .BNE .x10 .x0 (1060 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.iwd_ptr (GuestAddrs.mpt_insert_walk_db + 176)),
    .ADDI .x5 .x5 (laLo GuestAddrs.iwd_ptr (GuestAddrs.mpt_insert_walk_db + 176)),
    .LD .x23 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.iwd_len (GuestAddrs.mpt_insert_walk_db + 188)),
    .ADDI .x5 .x5 (laLo GuestAddrs.iwd_len (GuestAddrs.mpt_insert_walk_db + 188)),
    .LD .x24 .x5 (0 : BitVec 12),
    .LI .x22 (0 : Word),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .JAL .x1 (jalOff GuestAddrs.mpt_node_kind (GuestAddrs.mpt_insert_walk_db + 212)),
    .BEQ .x10 .x0 (24 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (300 : BitVec 13),
    .LI .x5 (2 : Word),
    .BEQ .x10 .x5 (720 : BitVec 13),
    .JAL .x0 (1004 : BitVec 21),
    .BEQ .x22 .x19 (272 : BitVec 13),
    .ADD .x5 .x18 .x22,
    .LBU .x6 .x5 (0 : BitVec 12),
    .SD .x20 .x23 (0 : BitVec 12),
    .SD .x20 .x24 (8 : BitVec 12),
    .SD .x20 .x0 (16 : BitVec 12),
    .SD .x20 .x6 (24 : BitVec 12),
    .ADDI .x20 .x20 (32 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .MV .x12 .x6,
    .AUIPC .x13 (laHi GuestAddrs.mw_child_offset (GuestAddrs.mpt_insert_walk_db + 288)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_child_offset (GuestAddrs.mpt_insert_walk_db + 288)),
    .AUIPC .x14 (laHi GuestAddrs.mw_child_length (GuestAddrs.mpt_insert_walk_db + 296)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_child_length (GuestAddrs.mpt_insert_walk_db + 296)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_insert_walk_db + 304)),
    .ADDI .x22 .x22 (1 : BitVec 12),
    .BNE .x10 .x0 (928 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_length (GuestAddrs.mpt_insert_walk_db + 316)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_length (GuestAddrs.mpt_insert_walk_db + 316)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (160 : BitVec 13),
    .LI .x7 (32 : Word),
    .BEQ .x6 .x7 (28 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_offset (GuestAddrs.mpt_insert_walk_db + 340)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_offset (GuestAddrs.mpt_insert_walk_db + 340)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x7,
    .MV .x24 .x6,
    .JAL .x0 (-156 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_offset (GuestAddrs.mpt_insert_walk_db + 364)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_offset (GuestAddrs.mpt_insert_walk_db + 364)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x7 .x23 .x6,
    .AUIPC .x28 (laHi GuestAddrs.iwd_hash (GuestAddrs.mpt_insert_walk_db + 380)),
    .ADDI .x28 .x28 (laLo GuestAddrs.iwd_hash (GuestAddrs.mpt_insert_walk_db + 380)),
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
    .AUIPC .x12 (laHi GuestAddrs.iwd_hash (GuestAddrs.mpt_insert_walk_db + 428)),
    .ADDI .x12 .x12 (laLo GuestAddrs.iwd_hash (GuestAddrs.mpt_insert_walk_db + 428)),
    .AUIPC .x13 (laHi GuestAddrs.iwd_ptr (GuestAddrs.mpt_insert_walk_db + 436)),
    .ADDI .x13 .x13 (laLo GuestAddrs.iwd_ptr (GuestAddrs.mpt_insert_walk_db + 436)),
    .AUIPC .x14 (laHi GuestAddrs.iwd_len (GuestAddrs.mpt_insert_walk_db + 444)),
    .ADDI .x14 .x14 (laLo GuestAddrs.iwd_len (GuestAddrs.mpt_insert_walk_db + 444)),
    .JAL .x1 (jalOff GuestAddrs.mpt_node_resolve (GuestAddrs.mpt_insert_walk_db + 452)),
    .BNE .x10 .x0 (776 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.iwd_ptr (GuestAddrs.mpt_insert_walk_db + 460)),
    .ADDI .x5 .x5 (laLo GuestAddrs.iwd_ptr (GuestAddrs.mpt_insert_walk_db + 460)),
    .LD .x23 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.iwd_len (GuestAddrs.mpt_insert_walk_db + 472)),
    .ADDI .x5 .x5 (laLo GuestAddrs.iwd_len (GuestAddrs.mpt_insert_walk_db + 472)),
    .LD .x24 .x5 (0 : BitVec 12),
    .JAL .x0 (-280 : BitVec 21),
    .ADDI .x20 .x20 (-32 : BitVec 12),
    .ADDI .x25 .x25 (-1 : BitVec 12),
    .LI .x30 (0 : Word),
    .ADDI .x22 .x22 (-1 : BitVec 12),
    .LI .x31 (0 : Word),
    .JAL .x0 (660 : BitVec 21),
    .LI .x30 (5 : Word),
    .LI .x31 (0 : Word),
    .JAL .x0 (648 : BitVec 21),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mw_path_offset (GuestAddrs.mpt_insert_walk_db + 536)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_path_offset (GuestAddrs.mpt_insert_walk_db + 536)),
    .AUIPC .x14 (laHi GuestAddrs.mw_path_length (GuestAddrs.mpt_insert_walk_db + 544)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_path_length (GuestAddrs.mpt_insert_walk_db + 544)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_insert_walk_db + 552)),
    .BNE .x10 .x0 (684 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_path_offset (GuestAddrs.mpt_insert_walk_db + 560)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_offset (GuestAddrs.mpt_insert_walk_db + 560)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x10 .x23 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mw_path_length (GuestAddrs.mpt_insert_walk_db + 576)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_length (GuestAddrs.mpt_insert_walk_db + 576)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_insert_walk_db + 588)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_insert_walk_db + 588)),
    .AUIPC .x13 (laHi GuestAddrs.mw_nibble_count (GuestAddrs.mpt_insert_walk_db + 596)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_nibble_count (GuestAddrs.mpt_insert_walk_db + 596)),
    .AUIPC .x14 (laHi GuestAddrs.mw_is_leaf (GuestAddrs.mpt_insert_walk_db + 604)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_is_leaf (GuestAddrs.mpt_insert_walk_db + 604)),
    .JAL .x1 (jalOff GuestAddrs.hp_decode_nibbles (GuestAddrs.mpt_insert_walk_db + 612)),
    .BNE .x10 .x0 (624 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_is_leaf (GuestAddrs.mpt_insert_walk_db + 620)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_is_leaf (GuestAddrs.mpt_insert_walk_db + 620)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BNE .x6 .x0 (608 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_nibble_count (GuestAddrs.mpt_insert_walk_db + 636)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_nibble_count (GuestAddrs.mpt_insert_walk_db + 636)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SUB .x7 .x19 .x22,
    .MV .x28 .x6,
    .BGEU .x7 .x6 (8 : BitVec 13),
    .MV .x28 .x7,
    .AUIPC .x29 (laHi GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_insert_walk_db + 664)),
    .ADDI .x29 .x29 (laLo GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_insert_walk_db + 664)),
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
    .BNE .x31 .x6 (232 : BitVec 13),
    .BLTU .x7 .x6 (228 : BitVec 13),
    .SD .x20 .x23 (0 : BitVec 12),
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
    .AUIPC .x13 (laHi GuestAddrs.mw_child_offset (GuestAddrs.mpt_insert_walk_db + 764)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_child_offset (GuestAddrs.mpt_insert_walk_db + 764)),
    .AUIPC .x14 (laHi GuestAddrs.mw_child_length (GuestAddrs.mpt_insert_walk_db + 772)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_child_length (GuestAddrs.mpt_insert_walk_db + 772)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_insert_walk_db + 780)),
    .BNE .x10 .x0 (456 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_length (GuestAddrs.mpt_insert_walk_db + 788)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_length (GuestAddrs.mpt_insert_walk_db + 788)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_offset (GuestAddrs.mpt_insert_walk_db + 800)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_offset (GuestAddrs.mpt_insert_walk_db + 800)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x28 .x23 .x7,
    .LI .x29 (32 : Word),
    .BEQ .x6 .x29 (16 : BitVec 13),
    .MV .x23 .x28,
    .MV .x24 .x6,
    .JAL .x0 (-628 : BitVec 21),
    .AUIPC .x29 (laHi GuestAddrs.iwd_hash (GuestAddrs.mpt_insert_walk_db + 836)),
    .ADDI .x29 .x29 (laLo GuestAddrs.iwd_hash (GuestAddrs.mpt_insert_walk_db + 836)),
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
    .AUIPC .x12 (laHi GuestAddrs.iwd_hash (GuestAddrs.mpt_insert_walk_db + 884)),
    .ADDI .x12 .x12 (laLo GuestAddrs.iwd_hash (GuestAddrs.mpt_insert_walk_db + 884)),
    .AUIPC .x13 (laHi GuestAddrs.iwd_ptr (GuestAddrs.mpt_insert_walk_db + 892)),
    .ADDI .x13 .x13 (laLo GuestAddrs.iwd_ptr (GuestAddrs.mpt_insert_walk_db + 892)),
    .AUIPC .x14 (laHi GuestAddrs.iwd_len (GuestAddrs.mpt_insert_walk_db + 900)),
    .ADDI .x14 .x14 (laLo GuestAddrs.iwd_len (GuestAddrs.mpt_insert_walk_db + 900)),
    .JAL .x1 (jalOff GuestAddrs.mpt_node_resolve (GuestAddrs.mpt_insert_walk_db + 908)),
    .BNE .x10 .x0 (320 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.iwd_ptr (GuestAddrs.mpt_insert_walk_db + 916)),
    .ADDI .x5 .x5 (laLo GuestAddrs.iwd_ptr (GuestAddrs.mpt_insert_walk_db + 916)),
    .LD .x23 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.iwd_len (GuestAddrs.mpt_insert_walk_db + 928)),
    .ADDI .x5 .x5 (laLo GuestAddrs.iwd_len (GuestAddrs.mpt_insert_walk_db + 928)),
    .LD .x24 .x5 (0 : BitVec 12),
    .JAL .x0 (-736 : BitVec 21),
    .LI .x30 (2 : Word),
    .JAL .x0 (220 : BitVec 21),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mw_path_offset (GuestAddrs.mpt_insert_walk_db + 964)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_path_offset (GuestAddrs.mpt_insert_walk_db + 964)),
    .AUIPC .x14 (laHi GuestAddrs.mw_path_length (GuestAddrs.mpt_insert_walk_db + 972)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_path_length (GuestAddrs.mpt_insert_walk_db + 972)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_insert_walk_db + 980)),
    .BNE .x10 .x0 (256 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_path_offset (GuestAddrs.mpt_insert_walk_db + 988)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_offset (GuestAddrs.mpt_insert_walk_db + 988)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x10 .x23 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mw_path_length (GuestAddrs.mpt_insert_walk_db + 1004)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_length (GuestAddrs.mpt_insert_walk_db + 1004)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_insert_walk_db + 1016)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_insert_walk_db + 1016)),
    .AUIPC .x13 (laHi GuestAddrs.mw_nibble_count (GuestAddrs.mpt_insert_walk_db + 1024)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_nibble_count (GuestAddrs.mpt_insert_walk_db + 1024)),
    .AUIPC .x14 (laHi GuestAddrs.mw_is_leaf (GuestAddrs.mpt_insert_walk_db + 1032)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_is_leaf (GuestAddrs.mpt_insert_walk_db + 1032)),
    .JAL .x1 (jalOff GuestAddrs.hp_decode_nibbles (GuestAddrs.mpt_insert_walk_db + 1040)),
    .BNE .x10 .x0 (196 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_is_leaf (GuestAddrs.mpt_insert_walk_db + 1048)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_is_leaf (GuestAddrs.mpt_insert_walk_db + 1048)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (1 : Word),
    .BNE .x6 .x7 (176 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_nibble_count (GuestAddrs.mpt_insert_walk_db + 1068)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_nibble_count (GuestAddrs.mpt_insert_walk_db + 1068)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SUB .x7 .x19 .x22,
    .MV .x28 .x6,
    .BGEU .x7 .x6 (8 : BitVec 13),
    .MV .x28 .x7,
    .AUIPC .x29 (laHi GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_insert_walk_db + 1096)),
    .ADDI .x29 .x29 (laLo GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_insert_walk_db + 1096)),
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
    .SD .x21 .x23 (24 : BitVec 12),
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

/-- Reloc side-table for `mptInsertWalkDb_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptInsertWalkDb_relocs : RelocTable :=
  [ (19, .la .x7 "iw_empty_trie_root"),
    (38, .la .x13 "iwd_ptr"),
    (40, .la .x14 "iwd_len"),
    (42, .jal .x1 "mpt_node_resolve"),
    (44, .la .x5 "iwd_ptr"),
    (47, .la .x5 "iwd_len"),
    (53, .jal .x1 "mpt_node_kind"),
    (72, .la .x13 "mw_child_offset"),
    (74, .la .x14 "mw_child_length"),
    (76, .jal .x1 "rlp_list_nth_item"),
    (79, .la .x5 "mw_child_length"),
    (85, .la .x5 "mw_child_offset"),
    (91, .la .x5 "mw_child_offset"),
    (95, .la .x28 "iwd_hash"),
    (107, .la .x12 "iwd_hash"),
    (109, .la .x13 "iwd_ptr"),
    (111, .la .x14 "iwd_len"),
    (113, .jal .x1 "mpt_node_resolve"),
    (115, .la .x5 "iwd_ptr"),
    (118, .la .x5 "iwd_len"),
    (134, .la .x13 "mw_path_offset"),
    (136, .la .x14 "mw_path_length"),
    (138, .jal .x1 "rlp_list_nth_item"),
    (140, .la .x5 "mw_path_offset"),
    (144, .la .x5 "mw_path_length"),
    (147, .la .x12 "mw_nibble_buf"),
    (149, .la .x13 "mw_nibble_count"),
    (151, .la .x14 "mw_is_leaf"),
    (153, .jal .x1 "hp_decode_nibbles"),
    (155, .la .x5 "mw_is_leaf"),
    (159, .la .x5 "mw_nibble_count"),
    (166, .la .x29 "mw_nibble_buf"),
    (191, .la .x13 "mw_child_offset"),
    (193, .la .x14 "mw_child_length"),
    (195, .jal .x1 "rlp_list_nth_item"),
    (197, .la .x5 "mw_child_length"),
    (200, .la .x5 "mw_child_offset"),
    (209, .la .x29 "iwd_hash"),
    (221, .la .x12 "iwd_hash"),
    (223, .la .x13 "iwd_ptr"),
    (225, .la .x14 "iwd_len"),
    (227, .jal .x1 "mpt_node_resolve"),
    (229, .la .x5 "iwd_ptr"),
    (232, .la .x5 "iwd_len"),
    (241, .la .x13 "mw_path_offset"),
    (243, .la .x14 "mw_path_length"),
    (245, .jal .x1 "rlp_list_nth_item"),
    (247, .la .x5 "mw_path_offset"),
    (251, .la .x5 "mw_path_length"),
    (254, .la .x12 "mw_nibble_buf"),
    (256, .la .x13 "mw_nibble_count"),
    (258, .la .x14 "mw_is_leaf"),
    (260, .jal .x1 "hp_decode_nibbles"),
    (262, .la .x5 "mw_is_leaf"),
    (267, .la .x5 "mw_nibble_count"),
    (274, .la .x29 "mw_nibble_buf") ]

def mptInsertWalkDbFunction : String :=
  "mpt_insert_walk_db:\n" ++ emitProgramR mptInsertWalkDb_prog mptInsertWalkDb_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptInsertWalkDb_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptInsertWalkDbFunction_eq_prog :
    mptInsertWalkDbFunction = "mpt_insert_walk_db:\n" ++ emitProgramR mptInsertWalkDb_prog mptInsertWalkDb_relocs := rfl

#guard mptInsertWalkDbFunction.startsWith "mpt_insert_walk_db:\n"
#guard mptInsertWalkDb_prog.length = 324
/-- `zisk_mpt_insert_walk_db`: probe. Initialises the node DB to empty, then
    runs mpt_insert_walk_db with the same input layout as zisk_mpt_insert_walk
    (so the iw vectors verify the classification fields, which are
    DB/layout-independent; the absolute ptr fields are validated end-to-end by
    mpt_insert_acc). Output: status@0, meta@8 (48 B), stack@128. -/
def ziskMptInsertWalkDbPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  # init node DB empty\n" ++
  "  la t0, mset_db_count; sd zero, 0(t0)\n" ++
  "  la t0, mset_db_data; la t1, mset_db_top; sd t0, 0(t1)\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # witness_len\n" ++
  "  ld t5, 16(a7)               # path_len\n" ++
  "  ld t4, 24(a7)               # new_value_len\n" ++
  "  addi a0, a7, 32             # root_hash ptr\n" ++
  "  addi a3, a7, 64             # path ptr\n" ++
  "  add t3, t5, t4\n" ++
  "  addi t3, t3, 7\n" ++
  "  andi t3, t3, -8\n" ++
  "  add a1, a3, t3              # witness ptr\n" ++
  "  mv a2, t6                   # witness_len\n" ++
  "  mv a4, t5                   # path_len\n" ++
  "  li a5, 0xa0010080           # stack_out at OUTPUT+128\n" ++
  "  li a6, 0xa0010008           # meta_out at OUTPUT+8\n" ++
  "  jal ra, mpt_insert_walk_db\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  j .Liwd_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  mptResolveCacheResetFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  mptInsertWalkDbFunction ++ "\n" ++
  ".Liwd_pdone:"

def ziskMptInsertWalkDbDataSection : String :=
  ziskMptInsertWalkDataSection ++ "\n" ++
  -- mpt_node_resolve scratch + the node DB (mset_res_*, mset_db_*)
  ".balign 8\n" ++
  "mset_res_off:\n  .zero 8\n" ++
  "mset_res_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "iwd_ptr:\n  .zero 8\n" ++
  "iwd_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "iwd_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "mset_db_count:\n  .zero 8\n" ++
  "mset_db_top:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "mset_db_hash:\n  .zero 32\n" ++
  mptResolveCacheDataSection ++ "\n" ++
  ".balign 8\n" ++
  "mset_db_data:\n  .zero 8388608"


end EvmAsm.Codegen
