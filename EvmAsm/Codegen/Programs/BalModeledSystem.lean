/-
  EvmAsm.Codegen.Programs.BalModeledSystem

  Classifier for BAL AccountChanges rows whose effects are already modeled by
  the verdict's explicit system-write replay.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_is_modeled_system

    a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length
    a0 (output) = 1 EIP-2935 row / 2 EIP-4788 row / 0 other row / 3 parse failure.

    The verdict already replays EIP-2935 and EIP-4788 system writes before BAL
    post-state replay, so those BAL rows can be skipped in that verdict path. -/
def balAccountIsModeledSystemFunction : String :=
  "bal_account_is_modeled_system:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp)\n" ++
  "  mv s0, a0\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbams_parse_fail\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbams_parse_fail\n" ++
  "  li t1, 20; bne a2, t1, .Lbams_no\n" ++
  "  sub t0, a0, a2; la t5, bams_addr_ptr; sd t0, 0(t5)\n" ++
  "  la t1, bams_addr_2935; li t2, 20\n" ++
  ".Lbams_cmp_2935:\n" ++
  "  beqz t2, .Lbams_yes_2935\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbams_try_4788\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbams_cmp_2935\n" ++
  ".Lbams_try_4788:\n" ++
  "  la t5, bams_addr_ptr; ld t0, 0(t5); la t1, bams_addr_4788; li t2, 20\n" ++
  ".Lbams_cmp_4788:\n" ++
  "  beqz t2, .Lbams_yes_4788\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbams_no\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbams_cmp_4788\n" ++
  ".Lbams_yes_2935:\n" ++
  "  li a0, 1; j .Lbams_ret\n" ++
  ".Lbams_yes_4788:\n" ++
  "  li a0, 2; j .Lbams_ret\n" ++
  ".Lbams_no:\n" ++
  "  li a0, 0; j .Lbams_ret\n" ++
  ".Lbams_parse_fail:\n" ++
  "  li a0, 3\n" ++
  ".Lbams_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

def ziskBalAccountIsModeledSystemDataSection : String :=
  ".balign 8\n" ++
  "bams_addr_ptr:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bams_addr_2935:\n" ++
  "  .byte 0x00, 0x00, 0xF9, 0x08, 0x27, 0xF1, 0xC5, 0x3a\n" ++
  "  .byte 0x10, 0xcb, 0x7A, 0x02, 0x33, 0x5B, 0x17, 0x53\n" ++
  "  .byte 0x20, 0x00, 0x29, 0x35\n" ++
  ".balign 32\n" ++
  "bams_addr_4788:\n" ++
  "  .byte 0x00, 0x0F, 0x3d, 0xf6, 0xD7, 0x32, 0x80, 0x7E\n" ++
  "  .byte 0xf1, 0x31, 0x9f, 0xB7, 0xB8, 0xbB, 0x85, 0x22\n" ++
  "  .byte 0xd0, 0xBe, 0xac, 0x02\n"

end EvmAsm.Codegen
