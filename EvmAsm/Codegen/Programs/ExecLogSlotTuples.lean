/-
  EvmAsm.Codegen.Programs.ExecLogSlotTuples

  `exec_log_slot_tuples` (bead bmvmx.1.6.9 — exec-side foundation for the bmvmx.1.6.6
  tuple comparator) — reconstruct a slot's per-tx net-change `(block_access_index,
  new_value)` tuple SEQUENCE from the execution storage log.

  The storage exec-log is append-per-write: one 128-byte entry per SSTORE,
  `addrHash@0 / slotKey@32 / original@64 / current@96`, with a parallel
  `exec_log_txindex[i]` u64 array (#8585) giving the block_access_index of the tx that
  produced entry `i`. Transactions execute in order, so a given slot's matching entries
  appear in non-decreasing txindex order.

  Reconstruction (matching the spec's per-tx net-zero filter, block_access_lists.py):
    - running := the slot's block-pre value (entry `original`, identical on all matches);
    - walk matching entries in order, grouping by txindex (the LAST matching entry in a
      txindex group is that tx's end-of-tx value);
    - when a txindex group closes, emit `(txindex, end_value)` iff `end_value != running`
      (the tx net-changed the slot vs its pre-tx start), then `running := end_value`.

  This yields exactly the sequence the spec hashes into `header.block_access_list_hash`,
  directly comparable to the BAL side (`bal_slot_tuple_sequence`, #8593).

  Output: `count` × 40-byte records, in order:
    +0  block_access_index (u64)   +8  new_value (32-byte big-endian)
  Returns a0 = net-change tuple count (0 if the slot was never net-changed).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BlockVerdictParams

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## exec_log_slot_tuples
    a0 = addrHash ptr (32B)   a1 = slotKey ptr (32B)
    a2 = exec-log base (128B entries)   a3 = entry count
    a4 = exec_log_txindex array base (u64 per entry)   a5 = out buffer ptr
    a0 (output) = net-change tuple count. -/
def execLogSlotTuplesFunction : String :=
  "exec_log_slot_tuples:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                    # addrHash ptr\n" ++
  "  mv s1, a1                    # slotKey ptr\n" ++
  "  mv s2, a2                    # exec-log base\n" ++
  "  mv s3, a3                    # entry count\n" ++
  "  mv s4, a4                    # txindex array base\n" ++
  "  mv s5, a5                    # out buffer ptr\n" ++
  "  la t0, els_haverun; sd zero, 0(t0)\n" ++
  "  la t0, els_havegrp; sd zero, 0(t0)\n" ++
  "  li s7, 0                     # out_count\n" ++
  "  li s6, 0                     # entry index i\n" ++
  ".Lels_loop:\n" ++
  "  beq s6, s3, .Lels_finalize\n" ++
  -- lv44p.2.2 txindex window filter: when els_txfilter_hi != 0, process entry i only
  -- if els_txfilter_lo <= txindex[i] < els_txfilter_hi (else skip). Default 0/0 leaves
  -- every entry in (backward-compatible with all existing callers). Used by
  -- system_user_exec_log_slot_tuples to split begin-of-block (block_access_index 0)
  -- from end-of-block (N+1) system rows so each lands in the correct ordered segment.\n" ++
  "  la t0, els_txfilter_hi; ld t0, 0(t0); beqz t0, .Lels_nofilter\n" ++
  "  slli t6, s6, 3; add t6, s4, t6; ld t6, 0(t6)        # txindex[i]\n" ++
  "  la t0, els_txfilter_lo; ld t0, 0(t0); bltu t6, t0, .Lels_next   # txindex < lo -> skip\n" ++
  "  la t0, els_txfilter_hi; ld t0, 0(t0); bgeu t6, t0, .Lels_next   # txindex >= hi -> skip\n" ++
  ".Lels_nofilter:\n" ++
  "  slli t0, s6, 7; add t1, s2, t0   # entry ptr\n" ++
  "  # match addrHash (entry@0 vs s0)\n" ++
  "  ld t2, 0(t1);  ld t3, 0(s0);  bne t2, t3, .Lels_next\n" ++
  "  ld t2, 8(t1);  ld t3, 8(s0);  bne t2, t3, .Lels_next\n" ++
  "  ld t2, 16(t1); ld t3, 16(s0); bne t2, t3, .Lels_next\n" ++
  "  ld t2, 24(t1); ld t3, 24(s0); bne t2, t3, .Lels_next\n" ++
  "  # match slotKey (entry@32 vs s1)\n" ++
  "  ld t2, 32(t1); ld t3, 0(s1);  bne t2, t3, .Lels_next\n" ++
  "  ld t2, 40(t1); ld t3, 8(s1);  bne t2, t3, .Lels_next\n" ++
  "  ld t2, 48(t1); ld t3, 16(s1); bne t2, t3, .Lels_next\n" ++
  "  ld t2, 56(t1); ld t3, 24(s1); bne t2, t3, .Lels_next\n" ++
  "  # matching entry. set running = original (entry@64) on first match\n" ++
  "  la t0, els_haverun; ld t2, 0(t0); bnez t2, .Lels_runset\n" ++
  "  la t4, els_running\n" ++
  "  ld t2, 64(t1); sd t2, 0(t4); ld t2, 72(t1); sd t2, 8(t4)\n" ++
  "  ld t2, 80(t1); sd t2, 16(t4); ld t2, 88(t1); sd t2, 24(t4)\n" ++
  "  li t2, 1; la t0, els_haverun; sd t2, 0(t0)\n" ++
  ".Lels_runset:\n" ++
  "  slli t0, s6, 3; add t0, s4, t0; ld t5, 0(t0)   # tx_i = txindex[i]\n" ++
  "  la t0, els_havegrp; ld t2, 0(t0); beqz t2, .Lels_setgroup\n" ++
  "  la t0, els_grouptx; ld t3, 0(t0)\n" ++
  "  beq t5, t3, .Lels_setgroup            # same tx -> just update group end-value\n" ++
  "  jal ra, .Lels_finalize_group          # tx changed -> close previous group\n" ++
  ".Lels_setgroup:\n" ++
  "  slli t0, s6, 7; add t1, s2, t0        # recompute entry ptr (finalize clobbers t-regs)\n" ++
  "  slli t0, s6, 3; add t0, s4, t0; ld t5, 0(t0)   # recompute tx_i\n" ++
  "  la t0, els_grouptx; sd t5, 0(t0)      # group_tx = tx_i\n" ++
  "  la t4, els_groupval                   # group_val = current (entry@96)\n" ++
  "  ld t2, 96(t1);  sd t2, 0(t4);  ld t2, 104(t1); sd t2, 8(t4)\n" ++
  "  ld t2, 112(t1); sd t2, 16(t4); ld t2, 120(t1); sd t2, 24(t4)\n" ++
  "  li t2, 1; la t0, els_havegrp; sd t2, 0(t0)\n" ++
  ".Lels_next:\n" ++
  "  addi s6, s6, 1; j .Lels_loop\n" ++
  ".Lels_finalize:\n" ++
  "  la t0, els_havegrp; ld t2, 0(t0); beqz t2, .Lels_done\n" ++
  "  jal ra, .Lels_finalize_group\n" ++
  ".Lels_done:\n" ++
  "  mv a0, s7\n" ++
  ".Lels_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret\n" ++
  "  # --- local helper: close the current txindex group; emit if net-changed vs running ---\n" ++
  "  # (reached only via jal; clobbers t-regs; the real ra is restored at .Lels_ret)\n" ++
  ".Lels_finalize_group:\n" ++
  "  la t0, els_groupval; la t1, els_running\n" ++
  "  ld t2, 0(t0);  ld t3, 0(t1);  bne t2, t3, .Lels_emit\n" ++
  "  ld t2, 8(t0);  ld t3, 8(t1);  bne t2, t3, .Lels_emit\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lels_emit\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lels_emit\n" ++
  "  ret                                   # net-zero this tx -> no tuple\n" ++
  ".Lels_emit:\n" ++
  -- fhsxz.2.4.2.66.1.1: bound the output write. The caller's out buffer holds exactly
  -- bsrMaxTuplesPerSlot 40-byte records (atsc_execbuf, the symmetric counterpart of the
  -- BAL-side bal_slot_tuple_sequence cap). out_count is execution-bounded (one net-change
  -- group per distinct tx, so <= block tx count) and never reaches the cap in practice, but
  -- this LOCAL guard makes the no-overflow invariant explicit (out[j] is written only for
  -- j < cap) instead of relying on a whole-program tx-count argument: at/above the cap we
  -- skip the OOB 40-byte store while still tracking the true count + running value, so the
  -- helper returns the true count and the caller bails conservatively (count > cap).
  "  li t0, " ++ toString bsrMaxTuplesPerSlot ++ "; bgeu s7, t0, .Lels_emit_capped\n" ++
  "  slli t0, s7, 5; slli t1, s7, 3; add t0, t0, t1; add t6, s5, t0   # out[out_count] base\n" ++
  "  la t0, els_grouptx; ld t2, 0(t0); sd t2, 0(t6)                   # txindex -> +0\n" ++
  "  la t0, els_groupval; addi t1, t6, 8                              # value -> +8 (32B copy)\n" ++
  "  ld t2, 0(t0);  sd t2, 0(t1);  ld t2, 8(t0);  sd t2, 8(t1)\n" ++
  "  ld t2, 16(t0); sd t2, 16(t1); ld t2, 24(t0); sd t2, 24(t1)\n" ++
  ".Lels_emit_capped:\n" ++
  "  la t0, els_groupval; la t1, els_running                          # running = group_val\n" ++
  "  ld t2, 0(t0);  sd t2, 0(t1);  ld t2, 8(t0);  sd t2, 8(t1)\n" ++
  "  ld t2, 16(t0); sd t2, 16(t1); ld t2, 24(t0); sd t2, 24(t1)\n" ++
  "  addi s7, s7, 1                         # out_count++\n" ++
  "  ret"

/-- Scratch for `exec_log_slot_tuples`. -/
def execLogSlotTuplesData : String :=
  ".balign 8\n" ++
  "els_running:\n  .zero 32\n" ++
  "els_groupval:\n  .zero 32\n" ++
  "els_grouptx:\n  .zero 8\n" ++
  "els_haverun:\n  .zero 8\n" ++
  "els_havegrp:\n  .zero 8\n" ++
  -- lv44p.2.2: txindex window [lo, hi) filter. Default 0/0 (hi==0) = no filter.
  "els_txfilter_lo:\n  .zero 8\n" ++
  "els_txfilter_hi:\n  .zero 8\n"

/-- `zisk_exec_log_slot_tuples`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : entry count
      bytes 16..48 : addrHash (32B)
      bytes 48..80 : slotKey (32B)
      bytes 80..    : exec_log_txindex (count × 8B), then exec-log (count × 128B)
    Output: bytes 0..8 = tuple count; then count × 40-byte records at 0xa0010008. -/
def ziskExecLogSlotTuplesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000\n" ++
  "  ld a3, 8(t6)                # entry count\n" ++
  "  addi a0, t6, 16             # addrHash ptr\n" ++
  "  addi a1, t6, 48             # slotKey ptr\n" ++
  "  addi a4, t6, 80             # txindex array base\n" ++
  "  slli t0, a3, 3; add a2, a4, t0   # exec-log base = txindex_base + count*8\n" ++
  "  li a5, 0xa0010008           # out buffer = OUTPUT + 8\n" ++
  "  jal ra, exec_log_slot_tuples\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # tuple count\n" ++
  "  j .Lels_pdone\n" ++
  execLogSlotTuplesFunction ++ "\n" ++
  ".Lels_pdone:"

def ziskExecLogSlotTuplesDataSection : String :=
  ".section .data\n" ++
  execLogSlotTuplesData

def ziskExecLogSlotTuplesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskExecLogSlotTuplesPrologue
  dataAsm     := ziskExecLogSlotTuplesDataSection
}

end EvmAsm.Codegen
