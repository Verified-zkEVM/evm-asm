/-
  EvmAsm.Codegen.Programs.BalAccountAccessDescriptors

  Convert runtime account-access outcome records into read-only account-trie
  descriptors for BAL/post-state replay. The descriptor shape matches
  `mpt_state_root_ins`: path_ptr, path_len, value_ptr, value_len, mode.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.Mpt

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_access_outcome_descriptors

    a0 = account outcome table ptr       a1 = outcome count
    a2 = state-changing account table    a3 = state-changing account count
    a4 = descriptors out ptr             a5 = path arena out ptr
    a6 = out_count ptr                   a0 output = 0 ok / 1 malformed

    Outcome rows use the runtime access record layout:
      +0  address[20] BE, padded to 32
      +32 status: 0 warm, 1 cold, 2 active precompile
      +40 gas delta, ignored here
      +48/+56 reserved

    State-changing rows are 32-byte stride, first 20 bytes canonical address.
    Duplicate outcome addresses and state-changing addresses are skipped. Rows
    that remain are emitted as mode=3 no-op account descriptors with the
    canonical empty-account RLP as value. -/
def balAccountAccessOutcomeDescriptorsFunction : String :=
  "bal_account_access_outcome_descriptors:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                   # outcome table\n" ++
  "  mv s1, a1                   # outcome count\n" ++
  "  mv s2, a2                   # changed account table\n" ++
  "  mv s3, a3                   # changed account count\n" ++
  "  mv s4, a4                   # descriptor out base\n" ++
  "  mv s5, a5                   # path cursor\n" ++
  "  mv s6, a6                   # out_count ptr\n" ++
  "  sd zero, 0(s6)\n" ++
  "  li s7, 0                    # outcome index\n" ++
  "  li s8, 0                    # emitted descriptor count\n" ++
  ".Lbaaod_loop:\n" ++
  "  beq s7, s1, .Lbaaod_ok\n" ++
  "  slli t0, s7, 6\n" ++
  "  add s9, s0, t0              # current outcome ptr\n" ++
  "  ld t1, 32(s9)               # status\n" ++
  "  li t2, 2\n" ++
  "  bgtu t1, t2, .Lbaaod_fail\n" ++
  "  # Skip if this address already has a state-changing BAL descriptor.\n" ++
  "  li s10, 0\n" ++
  ".Lbaaod_changed_scan:\n" ++
  "  beq s10, s3, .Lbaaod_dup_scan_start\n" ++
  "  slli t0, s10, 5\n" ++
  "  add t0, s2, t0\n" ++
  "  mv t1, s9\n" ++
  "  li t2, 0\n" ++
  ".Lbaaod_changed_cmp:\n" ++
  "  li t3, 20\n" ++
  "  beq t2, t3, .Lbaaod_next\n" ++
  "  add t4, t0, t2\n" ++
  "  add t5, t1, t2\n" ++
  "  lbu t4, 0(t4)\n" ++
  "  lbu t5, 0(t5)\n" ++
  "  bne t4, t5, .Lbaaod_changed_next\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lbaaod_changed_cmp\n" ++
  ".Lbaaod_changed_next:\n" ++
  "  addi s10, s10, 1\n" ++
  "  j .Lbaaod_changed_scan\n" ++
  "  # Skip duplicate outcome addresses; the first read observation is enough.\n" ++
  ".Lbaaod_dup_scan_start:\n" ++
  "  li s10, 0\n" ++
  ".Lbaaod_dup_scan:\n" ++
  "  beq s10, s7, .Lbaaod_emit\n" ++
  "  slli t0, s10, 6\n" ++
  "  add t0, s0, t0\n" ++
  "  mv t1, s9\n" ++
  "  li t2, 0\n" ++
  ".Lbaaod_dup_cmp:\n" ++
  "  li t3, 20\n" ++
  "  beq t2, t3, .Lbaaod_next\n" ++
  "  add t4, t0, t2\n" ++
  "  add t5, t1, t2\n" ++
  "  lbu t4, 0(t4)\n" ++
  "  lbu t5, 0(t5)\n" ++
  "  bne t4, t5, .Lbaaod_dup_next\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lbaaod_dup_cmp\n" ++
  ".Lbaaod_dup_next:\n" ++
  "  addi s10, s10, 1\n" ++
  "  j .Lbaaod_dup_scan\n" ++
  ".Lbaaod_emit:\n" ++
  "  mv a0, s9\n" ++
  "  li a1, 20\n" ++
  "  la a2, baaod_hash\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  la a0, baaod_hash\n" ++
  "  li a1, 32\n" ++
  "  mv a2, s5\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  slli t0, s8, 5\n" ++
  "  slli t1, s8, 3\n" ++
  "  add t0, t0, t1\n" ++
  "  add t0, s4, t0              # descriptor[out]\n" ++
  "  sd s5, 0(t0)\n" ++
  "  li t1, 64\n" ++
  "  sd t1, 8(t0)\n" ++
  "  la t1, baaod_empty_account\n" ++
  "  sd t1, 16(t0)\n" ++
  "  li t1, 70\n" ++
  "  sd t1, 24(t0)\n" ++
  "  li t1, 3\n" ++
  "  sd t1, 32(t0)\n" ++
  "  addi s5, s5, 64\n" ++
  "  addi s8, s8, 1\n" ++
  "  sd s8, 0(s6)\n" ++
  ".Lbaaod_next:\n" ++
  "  addi s7, s7, 1\n" ++
  "  j .Lbaaod_loop\n" ++
  ".Lbaaod_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lbaaod_ret\n" ++
  ".Lbaaod_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbaaod_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- `zisk_bal_account_access_outcome_descriptors`: synthetic probe.
    Output:
      +0 status
      +8 descriptor count
      +16 descriptors
      +96 path arena for the two emitted rows. -/
def ziskBalAccountAccessOutcomeDescriptorsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la a0, baaod_probe_outcomes\n" ++
  "  li a1, 4\n" ++
  "  la a2, baaod_probe_changed\n" ++
  "  li a3, 1\n" ++
  "  li a4, 0xa0010010\n" ++
  "  li a5, 0xa0010060\n" ++
  "  li a6, 0xa0010008\n" ++
  "  jal ra, bal_account_access_outcome_descriptors\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbaaod_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  balAccountAccessOutcomeDescriptorsFunction ++ "\n" ++
  ".Lbaaod_pdone:"

def ziskBalAccountAccessOutcomeDescriptorsDataSection : String :=
  ziskMptWalkDataSection ++ "\n" ++
  ".balign 32\n" ++
  "baaod_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "baaod_empty_account:\n" ++
  "  .byte 0xf8,0x44,0x80,0x80,0xa0\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21\n" ++
  "  .byte 0xa0\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70\n" ++
  ".balign 32\n" ++
  "baaod_probe_changed:\n" ++
  "  .byte 0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb\n" ++
  "  .byte 0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb\n" ++
  "  .zero 12\n" ++
  ".balign 64\n" ++
  "baaod_probe_outcomes:\n" ++
  "  # cold account A\n" ++
  "  .byte 0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa\n" ++
  "  .byte 0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa\n" ++
  "  .zero 12\n" ++
  "  .quad 1,2500,0,0\n" ++
  "  # duplicate warm account A, skipped\n" ++
  "  .byte 0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa\n" ++
  "  .byte 0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa\n" ++
  "  .zero 12\n" ++
  "  .quad 0,0,0,0\n" ++
  "  # account B already has a state-changing descriptor, skipped\n" ++
  "  .byte 0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb\n" ++
  "  .byte 0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb\n" ++
  "  .zero 12\n" ++
  "  .quad 1,2500,0,0\n" ++
  "  # active precompile 0x04, emitted explicitly as read-only\n" ++
  "  .zero 19\n" ++
  "  .byte 0x04\n" ++
  "  .zero 12\n" ++
  "  .quad 2,0,0,0\n"

def ziskBalAccountAccessOutcomeDescriptorsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountAccessOutcomeDescriptorsPrologue
  dataAsm     := ziskBalAccountAccessOutcomeDescriptorsDataSection
}

end EvmAsm.Codegen
