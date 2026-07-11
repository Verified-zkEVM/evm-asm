/-
  EvmAsm.Codegen.Programs.RuntimeSameBlockCode

  Runtime helper for EIP-7702 same-block code observations. EXTCODESIZE,
  EXTCODEHASH, and EXTCODECOPY observe an account's current code. During a
  set-code transaction, that current code can be the BAL's final
  0xef0100||address delegation marker even though the pre-state trie still has
  empty code.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## runtime_same_block_delegation_code

    Calling convention:
      a0 = 20-byte address ptr
      runtime_current_bal_ptr/runtime_current_bal_len name the current BAL section
    Returns:
      a0 = 0 if the BAL has an authoritative final code change for this account
           and that final code is either empty (a cleared EIP-7702 delegation)
           or exactly a 23-byte EIP-7702 delegation marker; in that case
           rsbd_code_ptr/rsbd_code_len name those final code bytes.
      a0 = 1 otherwise.
-/
def runtimeSameBlockDelegationCode_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .MV .x8 .x10,
    .AUIPC .x5 (laHi GuestAddrs.runtime_current_bal_ptr (GuestAddrs.runtime_same_block_delegation_code + 44)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_current_bal_ptr (GuestAddrs.runtime_same_block_delegation_code + 44)),
    .LD .x9 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.runtime_current_bal_len (GuestAddrs.runtime_same_block_delegation_code + 56)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_current_bal_len (GuestAddrs.runtime_same_block_delegation_code + 56)),
    .LD .x18 .x5 (0 : BitVec 12),
    .BEQ .x9 .x0 (580 : BitVec 13),
    .BEQ .x18 .x0 (580 : BitVec 13),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .AUIPC .x12 (laHi GuestAddrs.rsbd_count (GuestAddrs.runtime_same_block_delegation_code + 84)),
    .ADDI .x12 .x12 (laLo GuestAddrs.rsbd_count (GuestAddrs.runtime_same_block_delegation_code + 84)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.runtime_same_block_delegation_code + 92)),
    .BNE .x10 .x0 (560 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.rsbd_count (GuestAddrs.runtime_same_block_delegation_code + 100)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_count (GuestAddrs.runtime_same_block_delegation_code + 100)),
    .LD .x19 .x5 (0 : BitVec 12),
    .LI .x20 (0 : Word),
    .BEQ .x20 .x19 (544 : BitVec 13),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .MV .x12 .x20,
    .AUIPC .x13 (laHi GuestAddrs.rsbd_acct_off (GuestAddrs.runtime_same_block_delegation_code + 132)),
    .ADDI .x13 .x13 (laLo GuestAddrs.rsbd_acct_off (GuestAddrs.runtime_same_block_delegation_code + 132)),
    .AUIPC .x14 (laHi GuestAddrs.rsbd_acct_len (GuestAddrs.runtime_same_block_delegation_code + 140)),
    .ADDI .x14 .x14 (laLo GuestAddrs.rsbd_acct_len (GuestAddrs.runtime_same_block_delegation_code + 140)),
    .JAL .x1 (jalOff GuestAddrs.rlp_item_span (GuestAddrs.runtime_same_block_delegation_code + 148)),
    .BNE .x10 .x0 (512 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.rsbd_acct_off (GuestAddrs.runtime_same_block_delegation_code + 156)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_acct_off (GuestAddrs.runtime_same_block_delegation_code + 156)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x21 .x9 .x6,
    .AUIPC .x5 (laHi GuestAddrs.rsbd_acct_len (GuestAddrs.runtime_same_block_delegation_code + 172)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_acct_len (GuestAddrs.runtime_same_block_delegation_code + 172)),
    .LD .x22 .x5 (0 : BitVec 12),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.rsbd_field_off (GuestAddrs.runtime_same_block_delegation_code + 196)),
    .ADDI .x13 .x13 (laLo GuestAddrs.rsbd_field_off (GuestAddrs.runtime_same_block_delegation_code + 196)),
    .AUIPC .x14 (laHi GuestAddrs.rsbd_field_len (GuestAddrs.runtime_same_block_delegation_code + 204)),
    .ADDI .x14 .x14 (laLo GuestAddrs.rsbd_field_len (GuestAddrs.runtime_same_block_delegation_code + 204)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.runtime_same_block_delegation_code + 212)),
    .BNE .x10 .x0 (416 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.rsbd_field_len (GuestAddrs.runtime_same_block_delegation_code + 220)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_field_len (GuestAddrs.runtime_same_block_delegation_code + 220)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (20 : Word),
    .BNE .x6 .x7 (396 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.rsbd_field_off (GuestAddrs.runtime_same_block_delegation_code + 240)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_field_off (GuestAddrs.runtime_same_block_delegation_code + 240)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x6 .x21 .x6,
    .MV .x7 .x8,
    .LI .x28 (20 : Word),
    .BEQ .x28 .x0 (32 : BitVec 13),
    .LBU .x29 .x6 (0 : BitVec 12),
    .LBU .x30 .x7 (0 : BitVec 12),
    .BNE .x29 .x30 (356 : BitVec 13),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .LI .x12 (5 : Word),
    .AUIPC .x13 (laHi GuestAddrs.rsbd_field_off (GuestAddrs.runtime_same_block_delegation_code + 308)),
    .ADDI .x13 .x13 (laLo GuestAddrs.rsbd_field_off (GuestAddrs.runtime_same_block_delegation_code + 308)),
    .AUIPC .x14 (laHi GuestAddrs.rsbd_field_len (GuestAddrs.runtime_same_block_delegation_code + 316)),
    .ADDI .x14 .x14 (laLo GuestAddrs.rsbd_field_len (GuestAddrs.runtime_same_block_delegation_code + 316)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.runtime_same_block_delegation_code + 324)),
    .BNE .x10 .x0 (340 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.rsbd_field_off (GuestAddrs.runtime_same_block_delegation_code + 332)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_field_off (GuestAddrs.runtime_same_block_delegation_code + 332)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x23 .x21 .x6,
    .AUIPC .x5 (laHi GuestAddrs.rsbd_field_len (GuestAddrs.runtime_same_block_delegation_code + 348)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_field_len (GuestAddrs.runtime_same_block_delegation_code + 348)),
    .LD .x6 .x5 (0 : BitVec 12),
    .MV .x10 .x23,
    .MV .x11 .x6,
    .AUIPC .x12 (laHi GuestAddrs.rsbd_code_count (GuestAddrs.runtime_same_block_delegation_code + 368)),
    .ADDI .x12 .x12 (laLo GuestAddrs.rsbd_code_count (GuestAddrs.runtime_same_block_delegation_code + 368)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.runtime_same_block_delegation_code + 376)),
    .BNE .x10 .x0 (292 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.rsbd_code_count (GuestAddrs.runtime_same_block_delegation_code + 384)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_code_count (GuestAddrs.runtime_same_block_delegation_code + 384)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (280 : BitVec 13),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.rsbd_field_len (GuestAddrs.runtime_same_block_delegation_code + 404)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_field_len (GuestAddrs.runtime_same_block_delegation_code + 404)),
    .LD .x11 .x5 (0 : BitVec 12),
    .MV .x10 .x23,
    .MV .x12 .x6,
    .AUIPC .x13 (laHi GuestAddrs.rsbd_tuple_off (GuestAddrs.runtime_same_block_delegation_code + 424)),
    .ADDI .x13 .x13 (laLo GuestAddrs.rsbd_tuple_off (GuestAddrs.runtime_same_block_delegation_code + 424)),
    .AUIPC .x14 (laHi GuestAddrs.rsbd_tuple_len (GuestAddrs.runtime_same_block_delegation_code + 432)),
    .ADDI .x14 .x14 (laLo GuestAddrs.rsbd_tuple_len (GuestAddrs.runtime_same_block_delegation_code + 432)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.runtime_same_block_delegation_code + 440)),
    .BNE .x10 .x0 (236 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.rsbd_tuple_off (GuestAddrs.runtime_same_block_delegation_code + 448)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_tuple_off (GuestAddrs.runtime_same_block_delegation_code + 448)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x6 .x23 .x6,
    .AUIPC .x5 (laHi GuestAddrs.rsbd_tuple_len (GuestAddrs.runtime_same_block_delegation_code + 464)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_tuple_len (GuestAddrs.runtime_same_block_delegation_code + 464)),
    .LD .x7 .x5 (0 : BitVec 12),
    .MV .x10 .x6,
    .MV .x11 .x7,
    .LI .x12 (1 : Word),
    .AUIPC .x13 (laHi GuestAddrs.rsbd_code_off (GuestAddrs.runtime_same_block_delegation_code + 488)),
    .ADDI .x13 .x13 (laLo GuestAddrs.rsbd_code_off (GuestAddrs.runtime_same_block_delegation_code + 488)),
    .AUIPC .x14 (laHi GuestAddrs.rsbd_code_len_cell (GuestAddrs.runtime_same_block_delegation_code + 496)),
    .ADDI .x14 .x14 (laLo GuestAddrs.rsbd_code_len_cell (GuestAddrs.runtime_same_block_delegation_code + 496)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.runtime_same_block_delegation_code + 504)),
    .BNE .x10 .x0 (176 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.rsbd_code_len_cell (GuestAddrs.runtime_same_block_delegation_code + 512)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_code_len_cell (GuestAddrs.runtime_same_block_delegation_code + 512)),
    .LD .x22 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.rsbd_tuple_off (GuestAddrs.runtime_same_block_delegation_code + 524)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_tuple_off (GuestAddrs.runtime_same_block_delegation_code + 524)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x6 .x23 .x6,
    .AUIPC .x5 (laHi GuestAddrs.rsbd_code_off (GuestAddrs.runtime_same_block_delegation_code + 540)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_code_off (GuestAddrs.runtime_same_block_delegation_code + 540)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x6 .x6 .x7,
    .BEQ .x22 .x0 (44 : BitVec 13),
    .LI .x28 (23 : Word),
    .BNE .x22 .x28 (124 : BitVec 13),
    .LBU .x28 .x6 (0 : BitVec 12),
    .LI .x29 (239 : Word),
    .BNE .x28 .x29 (116 : BitVec 13),
    .LBU .x28 .x6 (1 : BitVec 12),
    .LI .x29 (1 : Word),
    .BNE .x28 .x29 (108 : BitVec 13),
    .LBU .x28 .x6 (2 : BitVec 12),
    .BNE .x28 .x0 (104 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.rsbd_code_ptr (GuestAddrs.runtime_same_block_delegation_code + 600)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_code_ptr (GuestAddrs.runtime_same_block_delegation_code + 600)),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.rsbd_code_len (GuestAddrs.runtime_same_block_delegation_code + 612)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_code_len (GuestAddrs.runtime_same_block_delegation_code + 612)),
    .SD .x5 .x22 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (76 : BitVec 21),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (-520 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (60 : BitVec 21),
    .JAL .x0 (-8 : BitVec 21),
    .JAL .x0 (-12 : BitVec 21),
    .JAL .x0 (-16 : BitVec 21),
    .JAL .x0 (-20 : BitVec 21),
    .JAL .x0 (-24 : BitVec 21),
    .JAL .x0 (-28 : BitVec 21),
    .JAL .x0 (-32 : BitVec 21),
    .JAL .x0 (-36 : BitVec 21),
    .JAL .x0 (-40 : BitVec 21),
    .JAL .x0 (-44 : BitVec 21),
    .JAL .x0 (-48 : BitVec 21),
    .JAL .x0 (-52 : BitVec 21),
    .JAL .x0 (-56 : BitVec 21),
    .JAL .x0 (-60 : BitVec 21),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `runtimeSameBlockDelegationCode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def runtimeSameBlockDelegationCode_relocs : RelocTable :=
  [ (11, .la .x5 "runtime_current_bal_ptr"),
    (14, .la .x5 "runtime_current_bal_len"),
    (21, .la .x12 "rsbd_count"),
    (23, .jal .x1 "rlp_list_count_items"),
    (25, .la .x5 "rsbd_count"),
    (33, .la .x13 "rsbd_acct_off"),
    (35, .la .x14 "rsbd_acct_len"),
    (37, .jal .x1 "rlp_item_span"),
    (39, .la .x5 "rsbd_acct_off"),
    (43, .la .x5 "rsbd_acct_len"),
    (49, .la .x13 "rsbd_field_off"),
    (51, .la .x14 "rsbd_field_len"),
    (53, .jal .x1 "rlp_list_nth_item"),
    (55, .la .x5 "rsbd_field_len"),
    (60, .la .x5 "rsbd_field_off"),
    (77, .la .x13 "rsbd_field_off"),
    (79, .la .x14 "rsbd_field_len"),
    (81, .jal .x1 "rlp_list_nth_item"),
    (83, .la .x5 "rsbd_field_off"),
    (87, .la .x5 "rsbd_field_len"),
    (92, .la .x12 "rsbd_code_count"),
    (94, .jal .x1 "rlp_list_count_items"),
    (96, .la .x5 "rsbd_code_count"),
    (101, .la .x5 "rsbd_field_len"),
    (106, .la .x13 "rsbd_tuple_off"),
    (108, .la .x14 "rsbd_tuple_len"),
    (110, .jal .x1 "rlp_list_nth_item"),
    (112, .la .x5 "rsbd_tuple_off"),
    (116, .la .x5 "rsbd_tuple_len"),
    (122, .la .x13 "rsbd_code_off"),
    (124, .la .x14 "rsbd_code_len_cell"),
    (126, .jal .x1 "rlp_list_nth_item"),
    (128, .la .x5 "rsbd_code_len_cell"),
    (131, .la .x5 "rsbd_tuple_off"),
    (135, .la .x5 "rsbd_code_off"),
    (150, .la .x5 "rsbd_code_ptr"),
    (153, .la .x5 "rsbd_code_len") ]

def runtimeSameBlockDelegationCodeFunction : String :=
  "runtime_same_block_delegation_code:\n" ++ emitProgramR runtimeSameBlockDelegationCode_prog runtimeSameBlockDelegationCode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `runtimeSameBlockDelegationCode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem runtimeSameBlockDelegationCodeFunction_eq_prog :
    runtimeSameBlockDelegationCodeFunction = "runtime_same_block_delegation_code:\n" ++ emitProgramR runtimeSameBlockDelegationCode_prog runtimeSameBlockDelegationCode_relocs := rfl

#guard runtimeSameBlockDelegationCodeFunction.startsWith "runtime_same_block_delegation_code:\n"
#guard runtimeSameBlockDelegationCode_prog.length = 187
def runtimeSameBlockDelegationCodeData : String :=
  ".balign 8
" ++
  "runtime_current_bal_ptr:
  .zero 8
" ++
  "runtime_current_bal_len:
  .zero 8
" ++
  "rsbd_count:
  .zero 8
" ++
  "rsbd_acct_off:
  .zero 8
" ++
  "rsbd_acct_len:
  .zero 8
" ++
  "rsbd_field_off:
  .zero 8
" ++
  "rsbd_field_len:
  .zero 8
" ++
  "rsbd_code_count:
  .zero 8
" ++
  "rsbd_tuple_off:
  .zero 8
" ++
  "rsbd_tuple_len:
  .zero 8
" ++
  "rsbd_code_off:
  .zero 8
" ++
  "rsbd_code_len_cell:
  .zero 8
" ++
  "rsbd_code_ptr:
  .zero 8
" ++
  "rsbd_code_len:
  .zero 8
" ++
  "rsbd_hash:
  .zero 32
" ++
  "eahsr_same_tx_empty_flag:
  .zero 8
" ++
  "ecc_old_active:
  .zero 8
" ++
  "ecc_same_block_hit:
  .zero 8
"

end EvmAsm.Codegen
