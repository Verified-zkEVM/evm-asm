/-
  EvmAsm.Codegen.Programs.BalRecipientFieldEmpty

  Probe for bead bmvmx.1.6.3 (nonce/code slice). The verdict's contract-dispatch tail
  asserts that a self-contained CALL recipient's BAL `nonce_changes` (AccountChanges item 4)
  and `code_changes` (item 5) are EMPTY RLP lists — a pre-existing contract executing no
  CREATE/CREATE2 changes neither field, so a non-empty list claims a change execution did
  not make.

  This probe locks the cursor-walk version of that contract: it hand-builds two
  AccountChanges (all-empty trailing fields; and one with a non-empty nonce_changes) and
  checks that walking an empty list immediately returns end-of-list, while walking a
  non-empty nonce_changes list exposes its first element.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- `zisk_bal_recipient_field_empty`: validate the empty-list walk semantics the verdict uses.
    Output (at 0xa0010000):
      +0  first walk status for empty nonce_changes (item 4)         -> 2
      +8  first walk status for empty code_changes  (item 5)         -> 2
      +16 first walk status for non-empty nonce_changes              -> 0
      +24 len of first non-empty nonce_changes element               -> 1 -/
def ziskBalRecipientFieldEmptyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- Empty AccountChanges at brfe_empty: 0xda | addr(0x94 + 20*0) | c0 c0 c0 c0(nonce) c0(code).
  -- content = 21 (addr) + 5 (empty lists) = 26 = 0x1a, outer prefix 0xc0+26 = 0xda; total 27 B.
  "  la t0, brfe_empty\n" ++
  "  li t1, 0xda; sb t1, 0(t0)\n" ++
  "  li t1, 0x94; sb t1, 1(t0)\n" ++
  "  li t2, 20; addi t3, t0, 2\n" ++
  "1:\n  beqz t2, 2f\n  sb zero, 0(t3); addi t3, t3, 1; addi t2, t2, -1; j 1b\n" ++
  "2:\n" ++
  "  li t1, 0xc0\n" ++
  "  sb t1, 22(t0); sb t1, 23(t0); sb t1, 24(t0); sb t1, 25(t0); sb t1, 26(t0)\n" ++
  -- Non-empty AccountChanges at brfe_nonempty: nonce_changes = 0xc1 0x05 (list[byte 5]).
  -- content = 21 + 3*1 + 2 (nonce) + 1 (code) = 27 = 0x1b, outer prefix 0xdb; total 28 B.
  "  la t0, brfe_nonempty\n" ++
  "  li t1, 0xdb; sb t1, 0(t0)\n" ++
  "  li t1, 0x94; sb t1, 1(t0)\n" ++
  "  li t2, 20; addi t3, t0, 2\n" ++
  "3:\n  beqz t2, 4f\n  sb zero, 0(t3); addi t3, t3, 1; addi t2, t2, -1; j 3b\n" ++
  "4:\n" ++
  "  li t1, 0xc0; sb t1, 22(t0); sb t1, 23(t0); sb t1, 24(t0)\n" ++
  "  li t1, 0xc1; sb t1, 25(t0); li t1, 0x05; sb t1, 26(t0)\n" ++
  "  li t1, 0xc0; sb t1, 27(t0)\n" ++
  -- empty nonce_changes item 4: first inner walk status -> +0.
  "  la a0, brfe_empty; li a1, 27; jal ra, rlp_walk_init\n" ++
  "  la t0, brfe_off; sd a0, 0(t0); la t0, brfe_len; sd a1, 0(t0)\n" ++
  "  li s1, 5\n" ++
  "5:\n  la t0, brfe_off; ld a0, 0(t0); la t0, brfe_len; ld a1, 0(t0); jal ra, rlp_walk_next\n" ++
  "  la t0, brfe_off; sd a0, 0(t0); addi s1, s1, -1; bnez s1, 5b\n" ++
  "  sub a0, a0, a2; mv a1, a2; jal ra, rlp_walk_init; jal ra, rlp_walk_next; sd a1, 0(s0)\n" ++
  -- empty code_changes item 5: first inner walk status -> +8.
  "  la a0, brfe_empty; li a1, 27; jal ra, rlp_walk_init\n" ++
  "  la t0, brfe_off; sd a0, 0(t0); la t0, brfe_len; sd a1, 0(t0)\n" ++
  "  li s1, 6\n" ++
  "6:\n  la t0, brfe_off; ld a0, 0(t0); la t0, brfe_len; ld a1, 0(t0); jal ra, rlp_walk_next\n" ++
  "  la t0, brfe_off; sd a0, 0(t0); addi s1, s1, -1; bnez s1, 6b\n" ++
  "  sub a0, a0, a2; mv a1, a2; jal ra, rlp_walk_init; jal ra, rlp_walk_next; sd a1, 8(s0)\n" ++
  -- non-empty nonce_changes item 4: first inner walk status/len -> +16/+24.
  "  la a0, brfe_nonempty; li a1, 28; jal ra, rlp_walk_init\n" ++
  "  la t0, brfe_off; sd a0, 0(t0); la t0, brfe_len; sd a1, 0(t0)\n" ++
  "  li s1, 5\n" ++
  "7:\n  la t0, brfe_off; ld a0, 0(t0); la t0, brfe_len; ld a1, 0(t0); jal ra, rlp_walk_next\n" ++
  "  la t0, brfe_off; sd a0, 0(t0); addi s1, s1, -1; bnez s1, 7b\n" ++
  "  sub a0, a0, a2; mv a1, a2; jal ra, rlp_walk_init; jal ra, rlp_walk_next; sd a1, 16(s0); sd a2, 24(s0)\n" ++
  "  j .Lbrfe_done\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  ".Lbrfe_done:"

def ziskBalRecipientFieldEmptyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "brfe_empty:\n  .zero 64\n" ++
  "brfe_nonempty:\n  .zero 64\n" ++
  "brfe_off:\n  .zero 8\n" ++
  "brfe_len:\n  .zero 8\n"


end EvmAsm.Codegen
