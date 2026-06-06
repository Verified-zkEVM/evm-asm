/-
  EvmAsm.Codegen.Programs.BalStorageAccessDescriptors

  Convert committed runtime storage-access outcome records for one account into
  read-only storage-trie descriptors. The descriptor shape matches
  `mpt_state_root_ins`: path_ptr, path_len, value_ptr, value_len, mode.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.EvmStorageAccessGas
import EvmAsm.Codegen.Programs.Mpt

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_storage_access_outcome_descriptors

    a0 = storage outcome table ptr      a1 = outcome count
    a2 = committed window table ptr     a3 = committed window count
    a4 = account token ptr (32 bytes)   a5 = descriptors out ptr
    a6 = path arena out ptr             a7 = out_count ptr
    a0 output = 0 ok / 1 malformed

    Storage outcome rows use the runtime access record layout:
      +0  account token[32]
      +32 storage slot[32]
      +64 status: 0 warm, 1 cold, 2 out-of-gas, 3 warmth-table full
      +72 gas delta, ignored here
      +80/+88 reserved

    Window rows follow `storage_effect_records` shape:
      +0 execution status (1 = success, 0 = reverted/failed)
      +8 committed outcome start index
      +16 committed outcome count
      +24 reserved

    Only successful windows and status 0/1 storage reads are materialized.
    Repeated reads of the same account/slot are compacted to the first
    descriptor. Paths are storage-trie paths: nibbles(keccak256(slot)). -/
def balStorageAccessOutcomeDescriptorsFunction : String :=
  "bal_storage_access_outcome_descriptors:\n" ++
  "  addi sp, sp, -128\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # outcome table\n" ++
  "  mv s1, a1                   # outcome count\n" ++
  "  mv s2, a2                   # committed window table\n" ++
  "  mv s3, a3                   # committed window count\n" ++
  "  mv s4, a4                   # account token\n" ++
  "  mv s5, a5                   # descriptor out base\n" ++
  "  mv s6, a6                   # path cursor\n" ++
  "  mv s7, a7                   # out_count ptr\n" ++
  "  sd zero, 0(s7)\n" ++
  "  li s8, 0                    # window index\n" ++
  "  li s9, 0                    # emitted descriptor count\n" ++
  ".Lbsaod_window_loop:\n" ++
  "  beq s8, s3, .Lbsaod_ok\n" ++
  "  slli t0, s8, 5\n" ++
  "  add s10, s2, t0             # current window\n" ++
  "  ld t1, 0(s10)               # window status\n" ++
  "  beqz t1, .Lbsaod_next_window\n" ++
  "  li t2, 1\n" ++
  "  bne t1, t2, .Lbsaod_fail\n" ++
  "  ld t3, 8(s10)               # start index\n" ++
  "  ld t4, 16(s10)              # count\n" ++
  "  add t5, t3, t4              # exclusive end\n" ++
  "  bltu t5, t3, .Lbsaod_fail\n" ++
  "  bgtu t5, s1, .Lbsaod_fail\n" ++
  "  sd t5, 104(sp)              # caller-saved across hash helpers\n" ++
  "  mv s11, t3                  # outcome index\n" ++
  ".Lbsaod_outcome_loop:\n" ++
  "  ld t5, 104(sp)\n" ++
  "  beq s11, t5, .Lbsaod_next_window\n" ++
  "  slli t0, s11, 6\n" ++
  "  slli t1, s11, 5\n" ++
  "  add t0, t0, t1\n" ++
  "  add s10, s0, t0             # current outcome\n" ++
  "  ld t1, 64(s10)              # status\n" ++
  "  li t2, 1\n" ++
  "  bgtu t1, t2, .Lbsaod_next_outcome\n" ++
  "  # Keep only rows for the requested account token.\n" ++
  "  mv t0, s10\n" ++
  "  mv t1, s4\n" ++
  "  li t2, 0\n" ++
  ".Lbsaod_account_cmp:\n" ++
  "  li t3, 32\n" ++
  "  beq t2, t3, .Lbsaod_emit\n" ++
  "  add t4, t0, t2\n" ++
  "  add t6, t1, t2\n" ++
  "  lbu t4, 0(t4)\n" ++
  "  lbu t6, 0(t6)\n" ++
  "  bne t4, t6, .Lbsaod_next_outcome\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lbsaod_account_cmp\n" ++
  ".Lbsaod_emit:\n" ++
  "  addi a0, s10, 32\n" ++
  "  li a1, 32\n" ++
  "  la a2, bsaod_hash\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  la a0, bsaod_hash\n" ++
  "  li a1, 32\n" ++
  "  mv a2, s6\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  # Skip duplicate committed observations by comparing against emitted paths.\n" ++
  "  li t0, 0\n" ++
  ".Lbsaod_emitted_dup_scan:\n" ++
  "  beq t0, s9, .Lbsaod_write_descriptor\n" ++
  "  sub t1, s9, t0\n" ++
  "  slli t1, t1, 6\n" ++
  "  sub t2, s6, t1             # path for emitted row t0\n" ++
  "  li t3, 0\n" ++
  ".Lbsaod_emitted_dup_cmp:\n" ++
  "  li t4, 64\n" ++
  "  beq t3, t4, .Lbsaod_next_outcome\n" ++
  "  add t5, t2, t3\n" ++
  "  add t6, s6, t3\n" ++
  "  lbu t5, 0(t5)\n" ++
  "  lbu t6, 0(t6)\n" ++
  "  bne t5, t6, .Lbsaod_emitted_dup_next\n" ++
  "  addi t3, t3, 1\n" ++
  "  j .Lbsaod_emitted_dup_cmp\n" ++
  ".Lbsaod_emitted_dup_next:\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lbsaod_emitted_dup_scan\n" ++
  ".Lbsaod_write_descriptor:\n" ++
  "  slli t0, s9, 5\n" ++
  "  slli t1, s9, 3\n" ++
  "  add t0, t0, t1\n" ++
  "  add t0, s5, t0              # descriptor[out]\n" ++
  "  sd s6, 0(t0)\n" ++
  "  li t1, 64\n" ++
  "  sd t1, 8(t0)\n" ++
  "  la t1, bsaod_empty_value\n" ++
  "  sd t1, 16(t0)\n" ++
  "  sd zero, 24(t0)\n" ++
  "  li t1, 3\n" ++
  "  sd t1, 32(t0)\n" ++
  "  addi s6, s6, 64\n" ++
  "  addi s9, s9, 1\n" ++
  "  sd s9, 0(s7)\n" ++
  ".Lbsaod_next_outcome:\n" ++
  "  addi s11, s11, 1\n" ++
  "  j .Lbsaod_outcome_loop\n" ++
  ".Lbsaod_next_window:\n" ++
  "  addi s8, s8, 1\n" ++
  "  j .Lbsaod_window_loop\n" ++
  ".Lbsaod_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lbsaod_ret\n" ++
  ".Lbsaod_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbsaod_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 128\n" ++
  "  ret"

/-- `zisk_bal_storage_access_outcome_descriptors`: synthetic probe.
    Output:
      +0  status
      +8  descriptor count
      +16 descriptors
      +96 path arena for the two emitted rows. -/
def ziskBalStorageAccessOutcomeDescriptorsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la a0, bsaod_probe_outcomes\n" ++
  "  li a1, 5\n" ++
  "  la a2, bsaod_probe_windows\n" ++
  "  li a3, 2\n" ++
  "  la a4, bsaod_probe_account\n" ++
  "  li a5, 0xa0010010\n" ++
  "  li a6, 0xa0010060\n" ++
  "  li a7, 0xa0010008\n" ++
  "  jal ra, bal_storage_access_outcome_descriptors\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbsaod_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  balStorageAccessOutcomeDescriptorsFunction ++ "\n" ++
  ".Lbsaod_pdone:"

def ziskBalStorageAccessOutcomeDescriptorsDataSection : String :=
  ziskMptWalkDataSection ++ "\n" ++
  ".balign 32\n" ++
  "bsaod_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bsaod_empty_value:\n  .zero 1\n" ++
  ".balign 32\n" ++
  "bsaod_probe_account:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "bsaod_probe_windows:\n" ++
  "  .quad 1,0,4,0              # committed rows 0..3\n" ++
  "  .quad 0,4,1,0              # reverted row 4, skipped\n" ++
  ".balign 64\n" ++
  "bsaod_probe_outcomes:\n" ++
  "  # cold slot A for the selected account\n" ++
  "  .zero 32\n" ++
  "  .rept 32\n  .byte 0x11\n  .endr\n" ++
  "  .quad 1,2000,0,0\n" ++
  "  # duplicate warm slot A, skipped\n" ++
  "  .zero 32\n" ++
  "  .rept 32\n  .byte 0x11\n  .endr\n" ++
  "  .quad 0,0,0,0\n" ++
  "  # other account slot, skipped by account token\n" ++
  "  .rept 32\n  .byte 0xcc\n  .endr\n" ++
  "  .rept 32\n  .byte 0x33\n  .endr\n" ++
  "  .quad 1,2000,0,0\n" ++
  "  # cold slot B for the selected account\n" ++
  "  .zero 32\n" ++
  "  .rept 32\n  .byte 0x22\n  .endr\n" ++
  "  .quad 1,2000,0,0\n" ++
  "  # reverted slot C for selected account, skipped by failed window\n" ++
  "  .zero 32\n" ++
  "  .rept 32\n  .byte 0x44\n  .endr\n" ++
  "  .quad 1,2000,0,0\n"

def ziskBalStorageAccessOutcomeDescriptorsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalStorageAccessOutcomeDescriptorsPrologue
  dataAsm     := ziskBalStorageAccessOutcomeDescriptorsDataSection
}

end EvmAsm.Codegen
