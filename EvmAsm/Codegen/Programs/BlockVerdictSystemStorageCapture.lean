/-
  EvmAsm.Codegen.Programs.BlockVerdictSystemStorageCapture

  Capture system-call SSTORE rows into a side arena without changing the
  regular persistent storage-log count. This is the first substrate for
  validating EIP-7928 block_access_index=0 tuple sequences precisely.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.BlockVerdictParams

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## capture_system_storage_exec_rows
    a0 = start row index in the regular storage log
    a1 = end row index in the regular storage log
    a2 = regular storage log base (128-byte rows, usually 0xa0630000)
    a3 = side storage log base
    a4 = side txindex base
    a5 = side count ptr
    a0 (output) = 0 copied / 1 malformed end<start / 2 side arena overflow.

    Copies rows in [start,end) into the side arena and writes txindex=0 for
    every copied row. The caller keeps restoring the regular log count, so this
    side arena is the only durable record of system-call storage writes.

    Debug globals record the last attempted range and count calculation so
    non-fatal request-derivation callers can expose why side capture was
    incomplete without conflating dispatcher log-count reset with capacity
    exhaustion. -/
def captureSystemStorageExecRowsFunction : String :=
  "capture_system_storage_exec_rows:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                    # start\n" ++
  "  mv s1, a1                    # end\n" ++
  "  mv s2, a2                    # src log base\n" ++
  "  mv s3, a3                    # side log base\n" ++
  "  mv s4, a4                    # side txindex base\n" ++
  "  mv s5, a5                    # side count ptr\n" ++
  "  la t0, bv_system_storage_capture_start; sd s0, 0(t0)\n" ++
  "  la t0, bv_system_storage_capture_end; sd s1, 0(t0)\n" ++
  "  la t0, bv_system_storage_capture_status; sd zero, 0(t0)\n" ++
  "  bltu s1, s0, .Lcssc_malformed\n" ++
  "  sub s6, s1, s0               # rows to copy\n" ++
  "  la t0, bv_system_storage_capture_rows; sd s6, 0(t0)\n" ++
  "  ld t0, 0(s5)                 # old side count\n" ++
  "  la t1, bv_system_storage_capture_old_count; sd t0, 0(t1)\n" ++
  "  add t1, t0, s6\n" ++
  "  la t3, bv_system_storage_capture_new_count; sd t1, 0(t3)\n" ++
  "  bltu t1, t0, .Lcssc_overflow\n" ++
  "  li t2, " ++ toString bvSystemStorageLogCapacity ++ "\n" ++
  "  bgtu t0, t2, .Lcssc_overflow\n" ++
  "  bgtu t1, t2, .Lcssc_overflow\n" ++
  "  li t3, 0                     # i\n" ++
  ".Lcssc_loop:\n" ++
  "  beq t3, s6, .Lcssc_done\n" ++
  "  add t4, s0, t3; slli t4, t4, 7; add t4, s2, t4   # src row\n" ++
  "  ld t0, 0(s5); add t0, t0, t3\n" ++
  "  slli t5, t0, 7; add t5, s3, t5                   # dst row\n" ++
  "  slli t6, t0, 3; add t6, s4, t6; sd zero, 0(t6)    # side txindex = 0\n" ++
  "  ld t6, 0(t4); sd t6, 0(t5); ld t6, 8(t4); sd t6, 8(t5)\n" ++
  "  ld t6, 16(t4); sd t6, 16(t5); ld t6, 24(t4); sd t6, 24(t5)\n" ++
  "  ld t6, 32(t4); sd t6, 32(t5); ld t6, 40(t4); sd t6, 40(t5)\n" ++
  "  ld t6, 48(t4); sd t6, 48(t5); ld t6, 56(t4); sd t6, 56(t5)\n" ++
  "  ld t6, 64(t4); sd t6, 64(t5); ld t6, 72(t4); sd t6, 72(t5)\n" ++
  "  ld t6, 80(t4); sd t6, 80(t5); ld t6, 88(t4); sd t6, 88(t5)\n" ++
  "  ld t6, 96(t4); sd t6, 96(t5); ld t6, 104(t4); sd t6, 104(t5)\n" ++
  "  ld t6, 112(t4); sd t6, 112(t5); ld t6, 120(t4); sd t6, 120(t5)\n" ++
  "  addi t3, t3, 1; j .Lcssc_loop\n" ++
  ".Lcssc_done:\n" ++
  "  ld t0, 0(s5); add t0, t0, s6; sd t0, 0(s5)\n" ++
  "  li a0, 0; j .Lcssc_ret\n" ++
  ".Lcssc_malformed:\n" ++
  "  li a0, 1\n" ++
  "  la t0, bv_system_storage_capture_status; sd a0, 0(t0)\n" ++
  "  la t0, bv_system_storage_capture_rows; sd zero, 0(t0)\n" ++
  "  la t0, bv_system_storage_capture_old_count; sd zero, 0(t0)\n" ++
  "  la t0, bv_system_storage_capture_new_count; sd zero, 0(t0)\n" ++
  "  j .Lcssc_ret\n" ++
  ".Lcssc_overflow:\n" ++
  "  li a0, 2\n" ++
  "  la t0, bv_system_storage_capture_status; sd a0, 0(t0)\n" ++
  ".Lcssc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_capture_system_storage_exec_rows`: focused side-arena copy probe.
    Copies source rows [1,3), so output checks that two rows were appended,
    both side txindex entries are 0, and the first/last copied dwords match
    source row 1 and source row 2 respectively. Then it checks malformed,
    exact-capacity, and cap+1 overflow status codes. -/
def ziskCaptureSystemStorageExecRowsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la t0, cssc_src\n" ++
  "  li t1, 0x1111; sd t1, 0(t0)\n" ++
  "  addi t0, t0, 128; li t1, 0x2222; sd t1, 0(t0); li t1, 0x222f; sd t1, 120(t0)\n" ++
  "  addi t0, t0, 128; li t1, 0x3333; sd t1, 0(t0); li t1, 0x333f; sd t1, 120(t0)\n" ++
  "  li a0, 1; li a1, 3; la a2, cssc_src; la a3, cssc_side_log; la a4, cssc_side_txindex; la a5, cssc_side_count\n" ++
  "  jal ra, capture_system_storage_exec_rows\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, cssc_side_count; ld t2, 0(t1); sd t2, 8(t0)\n" ++
  "  la t1, cssc_side_txindex; ld t2, 0(t1); sd t2, 16(t0); ld t2, 8(t1); sd t2, 24(t0)\n" ++
  "  la t1, cssc_side_log; ld t2, 0(t1); sd t2, 32(t0); ld t2, 248(t1); sd t2, 40(t0)\n" ++
  "  li a0, 3; li a1, 1; la a2, cssc_src; la a3, cssc_side_log; la a4, cssc_side_txindex; la a5, cssc_side_count\n" ++
  "  jal ra, capture_system_storage_exec_rows\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 48(t0)\n" ++
  "  li t1, " ++ toString (bvSystemStorageLogCapacity - 1) ++ "; la t2, cssc_side_count; sd t1, 0(t2)\n" ++
  "  li a0, 1; li a1, 2; la a2, cssc_src; li a3, 0xa1000000; li a4, 0xa0800000; la a5, cssc_side_count\n" ++
  "  jal ra, capture_system_storage_exec_rows\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 56(t0)\n" ++
  "  la t1, cssc_side_count; ld t2, 0(t1); sd t2, 64(t0)\n" ++
  "  li t3, 0xa1000000; li t4, " ++ toString ((bvSystemStorageLogCapacity - 1) * 128) ++ "; add t3, t3, t4; ld t5, 0(t3); sd t5, 72(t0)\n" ++
  "  li t1, " ++ toString bvSystemStorageLogCapacity ++ "; la t2, cssc_side_count; sd t1, 0(t2)\n" ++
  "  li a0, 1; li a1, 2; la a2, cssc_src; li a3, 0xa1000000; li a4, 0xa0800000; la a5, cssc_side_count\n" ++
  "  jal ra, capture_system_storage_exec_rows\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 80(t0)\n" ++
  "  la t1, bv_system_storage_capture_start; ld t2, 0(t1); sd t2, 88(t0)\n" ++
  "  la t1, bv_system_storage_capture_end; ld t2, 0(t1); sd t2, 96(t0)\n" ++
  "  la t1, bv_system_storage_capture_old_count; ld t2, 0(t1); sd t2, 104(t0)\n" ++
  "  la t1, bv_system_storage_capture_rows; ld t2, 0(t1); sd t2, 112(t0)\n" ++
  "  la t1, bv_system_storage_capture_new_count; ld t2, 0(t1); sd t2, 120(t0)\n" ++
  "  la t1, bv_system_storage_capture_status; ld t2, 0(t1); sd t2, 128(t0)\n" ++
  "  li t2, " ++ toString bvSystemStorageLogCapacity ++ "; sd t2, 136(t0)\n" ++
  "  j .Lcssc_pdone\n" ++
  captureSystemStorageExecRowsFunction ++ "\n" ++
  ".Lcssc_pdone:"

def ziskCaptureSystemStorageExecRowsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "cssc_src:\n  .zero 384\n" ++
  "cssc_side_count:\n  .zero 8\n" ++
  "cssc_side_txindex:\n  .zero 16\n" ++
  ".balign 32\n" ++
  "cssc_side_log:\n  .zero 256\n" ++
  "bv_system_storage_capture_status:\n  .zero 8\n" ++
  "bv_system_storage_capture_start:\n  .zero 8\n" ++
  "bv_system_storage_capture_end:\n  .zero 8\n" ++
  "bv_system_storage_capture_rows:\n  .zero 8\n" ++
  "bv_system_storage_capture_old_count:\n  .zero 8\n" ++
  "bv_system_storage_capture_new_count:\n  .zero 8\n"

def ziskCaptureSystemStorageExecRowsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCaptureSystemStorageExecRowsPrologue
  dataAsm     := ziskCaptureSystemStorageExecRowsDataSection
}

end EvmAsm.Codegen
