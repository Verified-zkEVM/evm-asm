/-
  EvmAsm.Codegen.Programs.BalRecipientFieldEmpty

  Probe for bead bmvmx.1.6.3 (nonce/code slice). The verdict's contract-dispatch tail
  asserts that a self-contained CALL recipient's BAL `nonce_changes` (AccountChanges item 4)
  and `code_changes` (item 5) are EMPTY RLP lists — a pre-existing contract executing no
  CREATE/CREATE2 changes neither field, so a non-empty list claims a change execution did
  not make. The emptiness test relies on a soundness-critical detail of `rlp_list_nth_item`:
  for a *list* item it returns the FULL encoded size (including the 1-byte prefix), so an
  empty list `0xc0` yields len==1 (NOT 0). The verdict therefore rejects only when len>1.

  This probe locks that contract in: it hand-builds two AccountChanges (all-empty trailing
  fields; and one with a non-empty nonce_changes) and asserts the len `rlp_list_nth_item`
  returns for items 4 and 5. A regression here (e.g. content-length semantics) would either
  mass-false-reject every contract recipient or silently accept fabricated nonce/code claims.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.RlpRead

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- `zisk_bal_recipient_field_empty`: validate the empty-list len semantics the verdict relies on.
    Output (at 0xa0010000):
      +0  status of rlp_list_nth_item(empty AccountChanges, item 4)  -> 0
      +8  len  of nonce_changes (item 4) when empty (0xc0)           -> 1
      +16 len  of code_changes  (item 5) when empty (0xc0)           -> 1
      +24 len  of nonce_changes (item 4) when non-empty (0xc1 0x05)  -> 2  (>1 => verdict rejects) -/
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
  -- nth(empty, 4): status -> +0, len -> +8.
  "  la a0, brfe_empty; li a1, 27; li a2, 4; la a3, brfe_off; la a4, brfe_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  sd a0, 0(s0)\n" ++
  "  la t0, brfe_len; ld t0, 0(t0); sd t0, 8(s0)\n" ++
  -- nth(empty, 5): len -> +16.
  "  la a0, brfe_empty; li a1, 27; li a2, 5; la a3, brfe_off; la a4, brfe_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  la t0, brfe_len; ld t0, 0(t0); sd t0, 16(s0)\n" ++
  -- nth(nonempty, 4): len -> +24.
  "  la a0, brfe_nonempty; li a1, 28; li a2, 4; la a3, brfe_off; la a4, brfe_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  la t0, brfe_len; ld t0, 0(t0); sd t0, 24(s0)\n" ++
  "  j .Lbrfe_done\n" ++
  rlpListNthItemFunction ++ "\n" ++
  ".Lbrfe_done:"

def ziskBalRecipientFieldEmptyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "brfe_empty:\n  .zero 64\n" ++
  "brfe_nonempty:\n  .zero 64\n" ++
  "brfe_off:\n  .zero 8\n" ++
  "brfe_len:\n  .zero 8\n"

def ziskBalRecipientFieldEmptyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalRecipientFieldEmptyPrologue
  dataAsm     := ziskBalRecipientFieldEmptyDataSection
}

end EvmAsm.Codegen
