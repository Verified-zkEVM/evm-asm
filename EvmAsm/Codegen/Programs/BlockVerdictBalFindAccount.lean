/-
  EvmAsm.Codegen.Programs.BlockVerdictBalFindAccount

  Locate a recipient's BAL AccountChanges entry by address, for contract-recipient
  runtime execution (evm-asm-fhsxz.2.4.2.57.11.6.4.3). The BAL section is an RLP
  list of AccountChanges, each [address, storage_changes, storage_reads, ...];
  block_state_root iterates them by index but never matches by address. The
  contract-dispatch wiring needs the recipient's specific AccountChanges entry
  (to enumerate its storage_changes via bal_recipient_storage_keys), so this
  helper scans the list and returns the entry whose item-0 address (20 bytes)
  matches the target.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_find_account_by_address

    Calling convention:
      a0 = BAL section RLP ptr   a1 = BAL section RLP length
      a2 = target address ptr (20 bytes)
      a3 = out account ptr cell (8 bytes; matched AccountChanges RLP ptr)
      a4 = out account len cell (8 bytes; matched AccountChanges RLP length)
    Returns:
      a0 = 0 found / 1 not found / 2 parse error.

    Scans the BAL list; for each AccountChanges entry reads item 0 (the 20-byte
    address) and compares to the target. Entries whose address field is not
    exactly 20 bytes are skipped. -/
def balFindAccountByAddressFunction : String :=
  "bal_find_account_by_address:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                    # BAL section ptr\n" ++
  "  mv s1, a1                    # BAL section len\n" ++
  "  mv s2, a2                    # target address ptr\n" ++
  "  mv s3, a3                    # out account ptr cell\n" ++
  "  mv s4, a4                    # out account len cell\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbfa_parse_err\n" ++
  "  mv s5, a0                    # cursor\n" ++
  "  mv s6, a1                    # end\n" ++
  "  mv s7, zero                  # i\n" ++
  ".Lbfa_loop:\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next\n" ++
  "  li t0, 2; beq a1, t0, .Lbfa_notfound\n" ++
  "  bnez a1, .Lbfa_parse_err\n" ++
  "  mv s5, a0\n" ++
  "  sub s8, a0, a2                # account ptr\n" ++
  "  mv s9, a2                     # account len\n" ++
  "  mv a0, s8; mv a1, s9; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbfa_next\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbfa_next\n" ++
  "  li t4, 20; bne a2, t4, .Lbfa_next\n" ++
  "  sub t1, a0, a2                # address bytes ptr\n" ++
  "  mv t3, s2; li t4, 20\n" ++
  ".Lbfa_cmp:\n" ++
  "  beqz t4, .Lbfa_match\n" ++
  "  lbu t5, 0(t1); lbu t6, 0(t3); bne t5, t6, .Lbfa_next\n" ++
  "  addi t1, t1, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lbfa_cmp\n" ++
  ".Lbfa_match:\n" ++
  "  la t6, bfa_index; sd s7, 0(t6)\n" ++
  "  sd s8, 0(s3)\n" ++
  "  sd s9, 0(s4)\n" ++
  "  li a0, 0; j .Lbfa_ret\n" ++
  ".Lbfa_next:\n" ++
  "  addi s7, s7, 1; j .Lbfa_loop\n" ++
  ".Lbfa_notfound:\n" ++
  "  li a0, 1; j .Lbfa_ret\n" ++
  ".Lbfa_parse_err:\n" ++
  "  li a0, 2\n" ++
  ".Lbfa_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_bal_find_account_by_address`: probe over a hand-encoded BAL with one
    AccountChanges (address byte0 = 0xAA, 63-byte account). Output:
      +0  status finding 0xAA.. (expect 0 found)
      +8  matched account length (expect 63)
      +16 status finding 0xCC.. (expect 1 not found) -/
def ziskBalFindAccountByAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la t0, bfa_addr_hit; li t1, 0xAA; sb t1, 0(t0)\n" ++
  "  la t0, bfa_addr_miss; li t1, 0xCC; sb t1, 0(t0)\n" ++
  "  li s0, 0xa0010000\n" ++
  -- find 0xAA.. (present).
  "  la a0, bfa_bal; li a1, 65; la a2, bfa_addr_hit; la a3, bfa_out_ptr; la a4, bfa_out_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  sd a0, 0(s0)\n" ++
  "  la t0, bfa_out_len; ld t1, 0(t0); sd t1, 8(s0)\n" ++
  -- find 0xCC.. (absent).
  "  la a0, bfa_bal; li a1, 65; la a2, bfa_addr_miss; la a3, bfa_out_ptr; la a4, bfa_out_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  sd a0, 16(s0)\n" ++
  "  j .Lbfap_done\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  balFindAccountByAddressFunction ++ "\n" ++
  ".Lbfap_done:"

def ziskBalFindAccountByAddressDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bfa_index:\n  .zero 8\n" ++
  "bfa_out_ptr:\n  .zero 8\n" ++
  "bfa_out_len:\n  .zero 8\n" ++
  "bfa_addr_hit:\n  .zero 20\n" ++
  "bfa_addr_miss:\n  .zero 20\n" ++
  ".balign 8\n" ++
  -- BAL = list[account]; account = f8 3d 94 [20B addr, byte0=0xAA] e3 e2 a0 [31*00] 07 c0 c0 c0 c0 c0.
  -- BAL list payload = 63 bytes -> f8 3f.
  "bfa_bal:\n" ++
  "  .byte 0xf8, 0x3f\n" ++
  "  .byte 0xf8, 0x3d\n" ++
  "  .byte 0x94\n" ++
  "  .byte 0xAA\n" ++
  "  .zero 19\n" ++
  "  .byte 0xe3, 0xe2, 0xa0\n" ++
  "  .zero 31\n" ++
  "  .byte 0x07\n" ++
  "  .byte 0xc0\n" ++
  "  .byte 0xc0, 0xc0, 0xc0, 0xc0\n"

def ziskBalFindAccountByAddressProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalFindAccountByAddressPrologue
  dataAsm     := ziskBalFindAccountByAddressDataSection
}

end EvmAsm.Codegen
