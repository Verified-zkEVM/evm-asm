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
      original @64 = the authenticated parent-state value for this address/slot
      current @96 = minimal BE descriptor value expanded/reversed to 32-byte LE

    The same expanded LE32 current field is also passed directly to the BAL
    storage-event builder at BAI 0 and to the block-level storage map consumed
    by h_SLOAD.  Keeping the conversion here gives the tuple comparator, the
    execution resolver, and the rebuilt BAL one byte-order authority.  The
    terminal BAI-0 path resolves `original` from the parent header before the
    inequality test; it must not use the block map because the pre-user seed
    is deliberately already present there for h_SLOAD.  The pre-user MTx setup
    reuses this row builder in seed-only mode: it populates the map without
    publishing a duplicate side-log row or BAL event.

    a0 (output) = 0 appended / 2 side arena or block-map overflow. -/
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
  "  mv s4, a0; mv s5, a2; mv s3, a3\n" ++
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
  "  li t1, 32; beq t0, t1, .Lamsr_value_rev_start\n" ++
  "  li t2, 31; sub t2, t2, t0; add t2, a1, t2; lbu t3, 0(t2); addi t4, s2, 32; add t4, t4, t0; sb t3, 0(t4)\n" ++
  "  addi t0, t0, 1; j .Lamsr_slot_rev\n" ++
  ".Lamsr_value_rev_start:\n" ++
  "  li t0, 0\n" ++
  ".Lamsr_value_rev:\n" ++
  "  beq t0, s3, .Lamsr_finish_one\n" ++
  "  addi t1, s3, -1; sub t1, t1, t0; add t1, s5, t1; lbu t2, 0(t1); addi t3, s2, 96; add t3, t3, t0; sb t2, 0(t3)\n" ++
  "  addi t0, t0, 1; j .Lamsr_value_rev\n" ++
  "  # Resolve the transaction-start value from the authenticated parent state.\n" ++
  "  # The block map is intentionally not consulted here: MTx seed rows are\n" ++
  "  # already in that map for later SLOADs, but they are not pre-state writes\n" ++
  "  # preceding the BAI-0 system transaction.\n" ++
  ".Lamsr_original_resolve:\n" ++
  "  sd ra, 56(sp)\n" ++
  "  mv s5, a1\n" ++
  "  la t0, sv_pre_rlp_ptr; ld a0, 0(t0)\n" ++
  "  la t0, sv_pre_rlp_len; ld a1, 0(t0)\n" ++
  "  mv a2, s4; mv a3, s5\n" ++
  "  la t0, bv_witness_state_ptr; ld a4, 0(t0); ld a6, 0(t0)\n" ++
  "  la t0, bv_witness_state_len; ld a5, 0(t0); ld a7, 0(t0)\n" ++
  "  jal ra, slot_at_header_state_root\n" ++
  "  bnez a0, .Lamsr_original_zero\n" ++
  "  li t0, 0\n" ++
  ".Lamsr_original_rev:\n" ++
  "  li t1, 32; beq t0, t1, .Lamsr_original_ready\n" ++
  "  la t2, sahsr_u256; add t2, t2, t0; lbu t3, 0(t2); li t4, 31; sub t4, t4, t0; addi t5, s2, 64; add t4, t5, t4; sb t3, 0(t4)\n" ++
  "  addi t0, t0, 1; j .Lamsr_original_rev\n" ++
  ".Lamsr_original_zero:\n" ++
  "  # A missing authenticated slot proves a zero pre-state value; preserve\n" ++
  "  # the already materialized descriptor post-value for the comparison.\n" ++
  "  sd zero, 64(s2); sd zero, 72(s2); sd zero, 80(s2); sd zero, 88(s2)\n" ++
  ".Lamsr_original_ready:\n" ++
  "  # Match the ordinary storage emitter's pre!=post rule.  Equal parent/current\n" ++
  "  # values still update the execution map, but publish no BAI-0 change row.\n" ++
  "  ld t0, 64(s2); ld t1, 96(s2); bne t0, t1, .Lamsr_emit_change\n" ++
  "  ld t0, 72(s2); ld t1, 104(s2); bne t0, t1, .Lamsr_emit_change\n" ++
  "  ld t0, 80(s2); ld t1, 112(s2); bne t0, t1, .Lamsr_emit_change\n" ++
  "  ld t0, 88(s2); ld t1, 120(s2); beq t0, t1, .Lamsr_map_equal\n" ++
  ".Lamsr_emit_change:\n" ++
  "  # a0=addr BE20, a1=0 BAI, a2=slot BE32, a3=current LE32.\n" ++
  "  mv a2, s5; mv a0, s4; li a1, 0; addi a3, s2, 96\n" ++
  "  jal ra, bal_builder_record_storage_change\n" ++
  "  j .Lamsr_map_changed\n" ++
  ".Lamsr_map_equal:\n" ++
  "  # Net-zero descriptor: no BAL change row and no side-log count bump.\n" ++
  "  mv a0, s2; addi a1, s2, 32; addi a2, s2, 96\n" ++
  "  jal ra, storage_writes_block_upsert\n" ++
  "  la t0, storage_writes_overflow; ld t0, 0(t0); bnez t0, .Lamsr_map_overflow\n" ++
  "  ld ra, 56(sp)\n" ++
  "  j .Lamsr_one_ok\n" ++
  ".Lamsr_map_changed:\n" ++
  "  # The modeled startup write must be visible to later h_SLOAD resolution.\n" ++
  "  mv a0, s2; addi a1, s2, 32; addi a2, s2, 96\n" ++
  "  jal ra, storage_writes_block_upsert\n" ++
  "  la t0, storage_writes_overflow; ld t0, 0(t0); bnez t0, .Lamsr_map_overflow\n" ++
  "  ld ra, 56(sp)\n" ++
  "  addi s1, s1, 1; sd s1, 0(s0)\n" ++
  "  j .Lamsr_one_ok\n" ++
  ".Lamsr_finish_one:\n" ++
  "  la t0, bv_system_storage_map_seed_only; ld t0, 0(t0); bnez t0, .Lamsr_seed_prepare\n" ++
  "  j .Lamsr_original_resolve\n" ++
  ".Lamsr_seed_prepare:\n" ++
  "  sd ra, 56(sp)\n" ++
  ".Lamsr_seed_map:\n" ++
  "  # Pre-user mode publishes only the canonical map row; the terminal call\n" ++
  "  # remains responsible for the side log and BAI-0 BAL builder event.\n" ++
  "  mv a0, s2; addi a1, s2, 32; addi a2, s2, 96\n" ++
  "  jal ra, storage_writes_block_upsert\n" ++
  "  la t0, storage_writes_overflow; ld t0, 0(t0); bnez t0, .Lamsr_map_overflow\n" ++
  "  ld ra, 56(sp)\n" ++
  "  j .Lamsr_one_ok\n" ++
  ".Lamsr_one_ok:\n" ++
  "  li a0, 0; ret\n" ++
  ".Lamsr_one_overflow:\n" ++
  "  li a0, 2; ret\n" ++
  ".Lamsr_map_overflow:\n" ++
  "  li a0, 2; j .Lamsr_ret\n" ++
  ".Lamsr_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

-- The one shared builder call runs through three conversion-helper invocations:
-- EIP-2935 once and EIP-4788 twice (timestamp and parent-root slots).  Dropping
-- either EIP-4788 invocation would silently omit a distinct BAI-0 BAL row.
#guard (appendModeledSystemStorageTupleRowsFunction.splitOn "jal ra, .Lamsr_append_one").length == 4
#guard (appendModeledSystemStorageTupleRowsFunction.splitOn "jal ra, storage_writes_block_upsert").length == 4
#guard (appendModeledSystemStorageTupleRowsFunction.splitOn "la t0, storage_writes_overflow; ld t0, 0(t0); bnez t0, .Lamsr_map_overflow").length == 4
#guard (appendModeledSystemStorageTupleRowsFunction.splitOn "la a0, bsr_addr_4788").length == 3

/-! The former post-loop replay helper was retired with the request-phase move.
    System calls now write and incorporate their own transaction-level maps at
    the real N+1 boundary; the side arena remains only execution evidence. -/
/-! ## record_modeled_eip4788_storage_reads

    The EIP-4788 system transaction is a real `TransactionState` in
    execution-specs: each SSTORE reads its slot before deciding whether its
    write changes state, then `incorporate_tx_into_block` promotes those reads.
    Thus a zero-over-zero parent-root write has no `storage_changes` row but
    still has a `storage_reads` row.

    This runs only after the modeled beacon call completed. It writes both
    SSTORE keys directly to the existing block-level recorder, avoiding a
    transaction-boundary clear from this post-transaction phase. The timestamp
    read is normally filtered later by its storage change; the parent-root read
    survives when net-equal.
    `bsr_kbuf` and `bsr_delta` are dead after `bsr_beacon_change` returns, so
    they supply the two LE32 recorder keys without a new data allocation. -/
def recordModeledEip4788StorageReadsFunction : String :=
  "record_modeled_eip4788_storage_reads:\n" ++
  "  addi sp, sp, -16; sd ra, 0(sp)\n" ++
  "  la a0, bsr_addr_4788; la a1, bsr_kbuf; jal ra, bal_addr_to_exec_log_key\n" ++
  "  la t0, swd_4788_slot; addi t0, t0, 31; la t1, bsr_delta; li t2, 32\n" ++
  ".Lrmesr_timestamp_slot:\n" ++
  "  beqz t2, .Lrmesr_timestamp_done\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; j .Lrmesr_timestamp_slot\n" ++
  ".Lrmesr_timestamp_done:\n" ++
  "  la a0, bsr_kbuf; la a1, bsr_delta; jal ra, storage_read_record_block\n" ++
  "  la t0, swd_4788_root_slot; addi t0, t0, 31; la t1, bsr_delta; li t2, 32\n" ++
  ".Lrmesr_root_slot:\n" ++
  "  beqz t2, .Lrmesr_root_done\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; j .Lrmesr_root_slot\n" ++
  ".Lrmesr_root_done:\n" ++
  "  la a0, bsr_kbuf; la a1, bsr_delta; jal ra, storage_read_record_block\n" ++
  "  ld ra, 0(sp); addi sp, sp, 16; ret\n"

#guard (recordModeledEip4788StorageReadsFunction.splitOn "jal ra, storage_read_record_block").length == 3

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
