/-
  EvmAsm.Codegen.Programs.StorageEffectRecords

  Small arena ABI for committed storage-effect windows. Runtime SSTORE appends
  to the persistent storage log, but post-state descriptor emission must only
  consume the window that belongs to a successful frame/transaction. Reverted or
  failing executions expose no committed storage effects.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## storage effect record arena

    Control block layout:
      +0  : count (u64)
      +8  : capacity (u64)
      +16 : record base pointer (u64)

    Record stride is 32 bytes:
      +0  : execution status (1 = success, 0 = revert/failure)
      +8  : committed persistent-storage-log start index
      +16 : committed persistent-storage-log count
      +24 : reserved

    `storage_effect_records_append_runtime_result` accepts a captured
    checkpoint/final log length pair. On success it records `final-checkpoint`
    entries; on revert/failure it records zero committed storage effects. -/
def storageEffectRecordsFunction : String :=
  "storage_effect_records_init:\n" ++
  "  sd zero, 0(a0)\n" ++
  "  sd a1, 8(a0)\n" ++
  "  sd a2, 16(a0)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  "storage_effect_records_clear:\n" ++
  "  sd zero, 0(a0)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  "storage_effect_records_append:\n" ++
  "  ld t0, 0(a0)\n" ++
  "  ld t1, 8(a0)\n" ++
  "  bgeu t0, t1, .Lser_full\n" ++
  "  ld t2, 16(a0)\n" ++
  "  slli t3, t0, 5\n" ++
  "  add t2, t2, t3\n" ++
  "  sd a1, 0(t2)                # status\n" ++
  "  sd a2, 8(t2)                # committed start\n" ++
  "  sd a3, 16(t2)               # committed count\n" ++
  "  sd zero, 24(t2)\n" ++
  "  addi t0, t0, 1\n" ++
  "  sd t0, 0(a0)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lser_full:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  "storage_effect_records_append_runtime_result:\n" ++
  "  # a1=status, a2=checkpoint/start, a3=final log length\n" ++
  "  beqz a1, .Lser_runtime_revert\n" ++
  "  bltu a3, a2, .Lser_runtime_revert\n" ++
  "  sub a3, a3, a2\n" ++
  "  j storage_effect_records_append\n" ++
  ".Lser_runtime_revert:\n" ++
  "  li a3, 0\n" ++
  "  j storage_effect_records_append\n" ++
  "storage_effect_record_nth:\n" ++
  "  ld t0, 0(a0)\n" ++
  "  bgeu a1, t0, .Lsernth_oob\n" ++
  "  ld t1, 16(a0)\n" ++
  "  slli t2, a1, 5\n" ++
  "  add t1, t1, t2\n" ++
  "  ld t3, 0(t1); sd t3, 0(a2)\n" ++
  "  ld t3, 8(t1); sd t3, 8(a2)\n" ++
  "  ld t3, 16(t1); sd t3, 16(a2)\n" ++
  "  ld t3, 24(t1); sd t3, 24(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lsernth_oob:\n" ++
  "  li a0, 1\n" ++
  "  ret"

/-- `zisk_storage_effect_records_probe`: exercise the committed storage-effect
    arena. Input layout (file maps to INPUT+8):
      +8  capacity
      +16 synthetic append attempts
      +24 runtime-result case:
          0 = none
          1 = success checkpoint 0 final 1
          2 = success checkpoint 2 final 5
          3 = revert checkpoint 4 final 6

    Output layout:
      +0   final append status
      +8   final count
      +16  capacity
      +24  nth(0) status
      +32  first record
      +64  nth(count-1) status
      +72  last record -/
def ziskStorageEffectRecordsProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  li s1, 0xa0010000\n" ++
  "  li t0, 20\n" ++
  "  mv t1, s1\n" ++
  ".Lserp_zero_out:\n" ++
  "  beqz t0, .Lserp_zero_done\n" ++
  "  sd zero, 0(t1)\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lserp_zero_out\n" ++
  ".Lserp_zero_done:\n" ++
  "  ld s2, 8(s0)                # capacity\n" ++
  "  ld s3, 16(s0)               # synthetic append attempts\n" ++
  "  ld s7, 24(s0)               # runtime case\n" ++
  "  la a0, ser_control\n" ++
  "  mv a1, s2\n" ++
  "  la a2, ser_records\n" ++
  "  jal ra, storage_effect_records_init\n" ++
  "  li s4, 0\n" ++
  "  li s5, 0\n" ++
  ".Lserp_append_loop:\n" ++
  "  beq s4, s3, .Lserp_append_done\n" ++
  "  la a0, ser_control\n" ++
  "  li a1, 1\n" ++
  "  slli a2, s4, 1\n" ++
  "  addi a3, s4, 1\n" ++
  "  jal ra, storage_effect_records_append\n" ++
  "  mv s5, a0\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lserp_append_loop\n" ++
  ".Lserp_append_done:\n" ++
  "  beqz s7, .Lserp_output\n" ++
  "  li t0, 1; beq s7, t0, .Lserp_runtime_success0\n" ++
  "  li t0, 2; beq s7, t0, .Lserp_runtime_success2\n" ++
  "  li t0, 3; beq s7, t0, .Lserp_runtime_revert\n" ++
  "  j .Lserp_output\n" ++
  ".Lserp_runtime_success0:\n" ++
  "  li a1, 1; li a2, 0; li a3, 1\n" ++
  "  j .Lserp_runtime_append\n" ++
  ".Lserp_runtime_success2:\n" ++
  "  li a1, 1; li a2, 2; li a3, 5\n" ++
  "  j .Lserp_runtime_append\n" ++
  ".Lserp_runtime_revert:\n" ++
  "  li a1, 0; li a2, 4; li a3, 6\n" ++
  ".Lserp_runtime_append:\n" ++
  "  la a0, ser_control\n" ++
  "  jal ra, storage_effect_records_append_runtime_result\n" ++
  "  mv s5, a0\n" ++
  ".Lserp_output:\n" ++
  "  sd s5, 0(s1)\n" ++
  "  la t0, ser_control\n" ++
  "  ld s6, 0(t0); ld t1, 8(t0)\n" ++
  "  sd s6, 8(s1); sd t1, 16(s1)\n" ++
  "  la a0, ser_control; li a1, 0; addi a2, s1, 32\n" ++
  "  jal ra, storage_effect_record_nth\n" ++
  "  sd a0, 24(s1)\n" ++
  "  beqz s6, .Lserp_no_last\n" ++
  "  la a0, ser_control; addi a1, s6, -1; addi a2, s1, 72\n" ++
  "  jal ra, storage_effect_record_nth\n" ++
  "  sd a0, 64(s1)\n" ++
  "  j .Lserp_done\n" ++
  ".Lserp_no_last:\n" ++
  "  li t0, 1; sd t0, 64(s1)\n" ++
  ".Lserp_done:\n" ++
  "  j .Lserp_exit\n" ++
  storageEffectRecordsFunction ++ "\n" ++
  ".Lserp_exit:"

def ziskStorageEffectRecordsProbeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ser_control:\n" ++
  "  .zero 24\n" ++
  ".balign 8\n" ++
  "ser_records:\n" ++
  "  .zero 512"

def ziskStorageEffectRecordsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStorageEffectRecordsProbePrologue
  dataAsm     := ziskStorageEffectRecordsProbeDataSection
}

end EvmAsm.Codegen
