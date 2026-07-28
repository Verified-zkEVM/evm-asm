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
    a6 = block_access_index to stamp into the side txindex for every copied row
    a7 = side arena capacity (row count; bmvmx.5.5.10 PR-2: generalized from the
         hardcoded bvSystemStorageLogCapacity so the per-tx user-write arena can
         reuse this helper with its own capacity).
    a0 (output) = 0 copied / 1 malformed end<start / 2 side arena overflow.

    Copies the unseeded rows in [start,end) into the side arena and writes
    txindex=a6 for every copied row. `exec_log_seed_flag` is parallel to the
    live log: preloads/reads set it, while runtime SSTORE appends clear it.
    This makes capture independent of any positional seed prefix. The caller
    keeps restoring the regular log count, so this side arena is the only
    durable record of system-call storage writes.
    lv44p.2.2: end-of-block system calls (EIP-7002/7251) run at block_access_index
    N+1, so the caller passes N+1 here; the tuple comparator then orders these
    end-of-block rows AFTER the user transactions instead of mis-stamping them 0.

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
  "  la t0, cssc_stamp_txindex; sd a6, 0(t0)   # lv44p.2.2: block_access_index to stamp\n" ++
  "  la t0, bv_system_storage_capture_start; sd s0, 0(t0)\n" ++
  "  la t0, bv_system_storage_capture_end; sd s1, 0(t0)\n" ++
  "  la t0, bv_system_storage_capture_status; sd zero, 0(t0)\n" ++
  "  bltu s1, s0, .Lcssc_malformed\n" ++
  "  sub s6, s1, s0               # rows to copy\n" ++
  "  la t0, bv_system_storage_capture_rows; sd s6, 0(t0)\n" ++
  "  ld t0, 0(s5)                 # old side count\n" ++
  "  la t1, bv_system_storage_capture_old_count; sd t0, 0(t1)\n" ++
  "  li t3, 0                     # i\n" ++
  ".Lcssc_loop:\n" ++
  "  beq t3, s6, .Lcssc_done\n" ++
  "  add t4, s0, t3               # source row index\n" ++
  "  la t1, exec_log_seed_flag; add t1, t1, t4; lbu t1, 0(t1); bnez t1, .Lcssc_next\n" ++
  "  ld t0, 0(s5); bgeu t0, a7, .Lcssc_overflow\n" ++
  "  slli t4, t4, 7; add t4, s2, t4                   # src row\n" ++
  "  slli t5, t0, 7; add t5, s3, t5                   # dst row\n" ++
  "  slli t6, t0, 3; add t6, s4, t6; la t1, cssc_stamp_txindex; ld t1, 0(t1); sd t1, 0(t6)   # side txindex = a6 (block_access_index)\n" ++
  "  ld t6, 0(t4); sd t6, 0(t5); ld t6, 8(t4); sd t6, 8(t5)\n" ++
  "  ld t6, 16(t4); sd t6, 16(t5); ld t6, 24(t4); sd t6, 24(t5)\n" ++
  "  ld t6, 32(t4); sd t6, 32(t5); ld t6, 40(t4); sd t6, 40(t5)\n" ++
  "  ld t6, 48(t4); sd t6, 48(t5); ld t6, 56(t4); sd t6, 56(t5)\n" ++
  "  ld t6, 64(t4); sd t6, 64(t5); ld t6, 72(t4); sd t6, 72(t5)\n" ++
  "  ld t6, 80(t4); sd t6, 80(t5); ld t6, 88(t4); sd t6, 88(t5)\n" ++
  "  ld t6, 96(t4); sd t6, 96(t5); ld t6, 104(t4); sd t6, 104(t5)\n" ++
  "  ld t6, 112(t4); sd t6, 112(t5); ld t6, 120(t4); sd t6, 120(t5)\n" ++
  "  addi t0, t0, 1; sd t0, 0(s5)\n" ++
  ".Lcssc_next:\n" ++
  "  addi t3, t3, 1; j .Lcssc_loop\n" ++
  ".Lcssc_done:\n" ++
  "  ld t0, 0(s5); la t1, bv_system_storage_capture_new_count; sd t0, 0(t1)\n" ++
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


/-! ## append_modeled_system_storage_tuple_rows
    Append the explicit EIP-2935/EIP-4788 startup storage descriptors into the
    system side log consumed by the BAL tuple comparator. These writes are not
    produced by dispatcher execution, but execution-specs still exposes them as
    block_access_index=0 storage tuple rows.

    The side log uses the runtime exec-log layout:
      addr key @0  = 20-byte address reversed into a 32-byte LE stack word
      slot key @32 = 32-byte storage key reversed to LE
      original @64 = zero (covered startup descriptor rows are insert-like)
      current @96 = minimal BE descriptor value expanded/reversed to 32-byte LE

    The same expanded LE32 current field is also passed directly to the BAL
    storage-event builder at BAI 0.  Keeping the conversion here gives the
    tuple comparator and future rebuilt BAL one byte-order authority.

    a0 (output) = 0 appended / 2 side arena overflow. -/
def appendModeledSystemStorageTupleRowsFunction : String :=
  "append_modeled_system_storage_tuple_rows:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  la s0, bv_system_storage_log_count; ld s1, 0(s0)\n" ++
  "  la a0, bsr_addr_2935; la a1, swd_2935_slot; la a2, swd_2935_val; la t0, swd_2935_vlen; ld a3, 0(t0)\n" ++
  "  jal ra, .Lamsr_append_one; bnez a0, .Lamsr_ret\n" ++
  "  la a0, bsr_addr_4788; la a1, swd_4788_slot; la a2, swd_4788_val; la t0, swd_4788_vlen; ld a3, 0(t0)\n" ++
  "  jal ra, .Lamsr_append_one; bnez a0, .Lamsr_ret\n" ++
  "  la a0, bsr_addr_4788; la a1, swd_4788_root_slot; la a2, swd_4788_root_val; la t0, swd_4788_root_vlen; ld a3, 0(t0)\n" ++
  "  jal ra, .Lamsr_append_one\n" ++
  "  j .Lamsr_ret\n" ++
  "  # a0=addr20 BE, a1=slot32 BE, a2=minimal value BE, a3=value length\n" ++
  ".Lamsr_append_one:\n" ++
  "  beqz a3, .Lamsr_one_ok\n" ++
  "  li t0, " ++ toString bvSystemStorageLogCapacity ++ "; bgeu s1, t0, .Lamsr_one_overflow\n" ++
  "  slli t0, s1, 7; la s2, bv_system_storage_log; add s2, s2, t0\n" ++
  "  slli t0, s1, 3; la s3, bv_system_storage_txindex; add s3, s3, t0; sd zero, 0(s3)\n" ++
  "  mv s4, a0; mv s5, a2\n" ++
  "  # addr key: reverse 20-byte canonical address, then zero-pad the high 12 bytes\n" ++
  "  li t0, 0\n" ++
  ".Lamsr_addr_rev:\n" ++
  "  li t1, 20; beq t0, t1, .Lamsr_addr_zero\n" ++
  "  li t2, 19; sub t2, t2, t0; add t2, s4, t2; lbu t3, 0(t2); add t4, s2, t0; sb t3, 0(t4)\n" ++
  "  addi t0, t0, 1; j .Lamsr_addr_rev\n" ++
  ".Lamsr_addr_zero:\n" ++
  "  li t0, 20\n" ++
  ".Lamsr_addr_zero_loop:\n" ++
  "  li t1, 32; beq t0, t1, .Lamsr_slot_rev_start\n" ++
  "  add t2, s2, t0; sb zero, 0(t2); addi t0, t0, 1; j .Lamsr_addr_zero_loop\n" ++
  "  # slot key: reverse 32-byte canonical key to runtime LE\n" ++
  ".Lamsr_slot_rev_start:\n" ++
  "  li t0, 0\n" ++
  ".Lamsr_slot_rev:\n" ++
  "  li t1, 32; beq t0, t1, .Lamsr_original_zero\n" ++
  "  li t2, 31; sub t2, t2, t0; add t2, a1, t2; lbu t3, 0(t2); addi t4, s2, 32; add t4, t4, t0; sb t3, 0(t4)\n" ++
  "  addi t0, t0, 1; j .Lamsr_slot_rev\n" ++
  "  # original value: zero for covered startup insert-like descriptor rows\n" ++
  ".Lamsr_original_zero:\n" ++
  "  sd zero, 64(s2); sd zero, 72(s2); sd zero, 80(s2); sd zero, 88(s2)\n" ++
  "  sd zero, 96(s2); sd zero, 104(s2); sd zero, 112(s2); sd zero, 120(s2)\n" ++
  "  li t0, 0\n" ++
  ".Lamsr_value_rev:\n" ++
  "  beq t0, a3, .Lamsr_finish_one\n" ++
  "  addi t1, a3, -1; sub t1, t1, t0; add t1, s5, t1; lbu t2, 0(t1); addi t3, s2, 96; add t3, t3, t0; sb t2, 0(t3)\n" ++
  "  addi t0, t0, 1; j .Lamsr_value_rev\n" ++
  ".Lamsr_finish_one:\n" ++
  "  # Reuse current@96: the sole minimal-BE -> LE32 conversion for BAI-0 rows.\n" ++
  "  # a0=addr BE20, a1=0 BAI, a2=slot BE32, a3=current LE32.\n" ++
  "  # .Lamsr_append_one is a local call: preserve its return PC over the builder JAL.\n" ++
  "  sd ra, 56(sp); mv a2, a1; mv a0, s4; li a1, 0; addi a3, s2, 96\n" ++
  "  jal ra, bal_builder_record_storage_change\n" ++
  "  ld ra, 56(sp)\n" ++
  "  addi s1, s1, 1; sd s1, 0(s0)\n" ++
  ".Lamsr_one_ok:\n" ++
  "  li a0, 0; ret\n" ++
  ".Lamsr_one_overflow:\n" ++
  "  li a0, 2; ret\n" ++
  ".Lamsr_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

-- The one shared builder call runs through three conversion-helper invocations:
-- EIP-2935 once and EIP-4788 twice (timestamp and parent-root slots).  Dropping
-- either EIP-4788 invocation would silently omit a distinct BAI-0 BAL row.
#guard (appendModeledSystemStorageTupleRowsFunction.splitOn "jal ra, .Lamsr_append_one").length == 4
#guard (appendModeledSystemStorageTupleRowsFunction.splitOn "la a0, bsr_addr_4788").length == 3

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
  "  li a6, 0\n" ++   -- lv44p.2.2 probe: stamp txindex 0 (probe asserts side txindex==0)
  "  li a7, " ++ toString bvSystemStorageLogCapacity ++ "\n" ++
  "  jal ra, capture_system_storage_exec_rows\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, cssc_side_count; ld t2, 0(t1); sd t2, 8(t0)\n" ++
  "  la t1, cssc_side_txindex; ld t2, 0(t1); sd t2, 16(t0); ld t2, 8(t1); sd t2, 24(t0)\n" ++
  "  la t1, cssc_side_log; ld t2, 0(t1); sd t2, 32(t0); ld t2, 248(t1); sd t2, 40(t0)\n" ++
  "  li a0, 3; li a1, 1; la a2, cssc_src; la a3, cssc_side_log; la a4, cssc_side_txindex; la a5, cssc_side_count\n" ++
  "  li a6, 0\n" ++   -- lv44p.2.2 probe: stamp txindex 0 (probe asserts side txindex==0)
  "  li a7, " ++ toString bvSystemStorageLogCapacity ++ "\n" ++
  "  jal ra, capture_system_storage_exec_rows\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 48(t0)\n" ++
  "  li t1, " ++ toString (bvSystemStorageLogCapacity - 1) ++ "; la t2, cssc_side_count; sd t1, 0(t2)\n" ++
  "  li a0, 1; li a1, 2; la a2, cssc_src; li a3, 0xa1000000; li a4, 0xa0800000; la a5, cssc_side_count\n" ++
  "  li a6, 0\n" ++   -- lv44p.2.2 probe: stamp txindex 0 (probe asserts side txindex==0)
  "  li a7, " ++ toString bvSystemStorageLogCapacity ++ "\n" ++
  "  jal ra, capture_system_storage_exec_rows\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 56(t0)\n" ++
  "  la t1, cssc_side_count; ld t2, 0(t1); sd t2, 64(t0)\n" ++
  "  li t3, 0xa1000000; li t4, " ++ toString ((bvSystemStorageLogCapacity - 1) * 128) ++ "; add t3, t3, t4; ld t5, 0(t3); sd t5, 72(t0)\n" ++
  "  li t1, " ++ toString bvSystemStorageLogCapacity ++ "; la t2, cssc_side_count; sd t1, 0(t2)\n" ++
  "  li a0, 1; li a1, 2; la a2, cssc_src; li a3, 0xa1000000; li a4, 0xa0800000; la a5, cssc_side_count\n" ++
  "  li a6, 0\n" ++   -- lv44p.2.2 probe: stamp txindex 0 (probe asserts side txindex==0)
  "  li a7, " ++ toString bvSystemStorageLogCapacity ++ "\n" ++
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
  "bv_system_storage_capture_new_count:\n  .zero 8\n" ++
  "cssc_stamp_txindex:\n  .zero 8\n"

def ziskCaptureSystemStorageExecRowsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCaptureSystemStorageExecRowsPrologue
  dataAsm     := ziskCaptureSystemStorageExecRowsDataSection
}

end EvmAsm.Codegen
