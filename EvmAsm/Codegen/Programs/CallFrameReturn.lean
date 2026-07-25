/-
  EvmAsm.Codegen.Programs.CallFrameReturn

  `frame_return` — the call-frame RETURN mechanic for the iterative (non-recursive)
  CALL descent (bead fhsxz.2.4.2.61.6.6). When a child frame halts (STOP / RETURN
  / REVERT / exceptional), instead of halting the whole guest the dispatcher pops
  one frame and RESUMES the parent's dispatch loop:

    1. read the saved call-context for the current (child) depth;
    2. copy `min(outsize, retlen)` returndata bytes into the parent's output region;
    3. pop `evm_call_depth` (child depth d → parent depth d-1);
    4. restore the parent PC / code-base (x10 / x21) from `frame_save_area`;
    5. restore the exact parent register bases x13 (memory) / x20 (env) from
       `frame_parent_bases[d]`;
    6. restore the parent stack top x12 to `parent_x12 + netPopBytes` (pop the CALL
       args) and write the success word (1 = STOP/RETURN, 0 = REVERT/exceptional);
    7. advance the parent PC one byte past the CALL opcode;
    8. `ret` — the caller (the depth-aware halt handler) then `j .dispatch_loop`.

  This helper does NOT itself jump to `.dispatch_loop`, so it can be unit-probed in
  isolation (no MPT / no dispatch loop) — the probe drives it with a synthesized
  call-context + save-area + depth and inspects the restored registers. The descent
  side (CALL handler) and the depth-aware halt branches are wired in a following
  slice; this slice lands the return mechanic + its data area + the unit probe.

  Layout it depends on (CallFrameLayout / CallFrameSwitch):
    `evm_call_depth`   u64 current depth (0 = top-level frame[0]).
    `frame_save_area`  1025 × 16 B (saved pc, codebase) indexed by depth.
    `frame_call_ctx`   1025 × 32 B (parent_x12, outoff_abs, outsize, netPopBytes)
                       indexed by the CHILD depth — saved by the descent, consumed
                       here on the matching return.
    `frame_parent_bases` 1025 × 16 B (parent memory base, parent env base) indexed
                       by the CHILD depth.
    `call_frame_arena` base for frames 1..1024 (FRAME_STRIDE 0x19000);
    `evm_memory`/`evm_env` the depth-0 register bases.
  Child-frame sub-offsets: frameMemOff=0, frameEnvOff=0x18400.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Codegen.Programs.CreateCreatorNonce

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- `frame_return(a0 = success word, a1 = child returndata ptr, a2 = returndata len)`:
    pop one call frame and restore the parent's dispatcher registers, leaving the
    parent ready to resume at `.dispatch_loop` (the caller performs that jump).

    Writes the parent stack: `success` (a0) at the post-pop stack top. For
    RETURN/REVERT, `a1`/`a2` describe the child's returndata so up to `outsize`
    bytes are copied into the caller's output memory window (`outoff_abs` from the
    saved call-context); pass `a1 = a2 = 0` for STOP / exceptional halts. The FULL
    returndata is ALSO staged into `evm_precompile_frame` (size@+8, data@+16) so
    the parent's RETURNDATASIZE/RETURNDATACOPY observe this sub-call's return
    (`retlen ≤ runtimeMemoryArenaLimitBytes < precompileFrameReturndataCapBytes`,
    so the clamp below never truncates).

    On return the live dispatcher registers are repointed to the parent frame:
      x10 = parent PC + 1 (past the CALL), x21 = parent code base,
      x13 = parent memory base, x20 = parent env base,
      x12 = parent stack top with the success word pushed.
    Clobbers t0-t4 (and the dispatcher regs it intentionally repoints). -/
def frameReturnFunction : String :=
  "frame_return:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s6, 40(sp); sd s7, 48(sp)\n" ++
  "  sd s8, 56(sp); sd s9, 64(sp); sd s10, 72(sp)\n" ++
  "  mv s0, a0                      # success word\n" ++
  "  mv s1, a1                      # child returndata ptr\n" ++
  "  mv s2, a2                      # returndata len\n" ++
  -- Capture the child frame's committed log cursors. On success these become
  -- the parent's live cursors; on REVERT/exceptional failure the parent keeps
  -- its pre-child checkpoint values.
  "  ld s8, 448(x20)                 # child persistentLogLength\n" ++
  "  ld s9, 464(x20)                 # child transientLogLength\n" ++
  "  ld s10, 472(x20)                # child eventLogLength\n" ++
  -- nxio8.4.1: on a child REVERT / exceptional halt (success word s0 == 0) restore
  -- the parent's pre-child EIP-8037 state gas, snapshotted into the child env
  -- (env+624/632) by call_frame_descend. incorporate_child_on_error returns the
  -- reverted child's entire state-gas allocation (used + left) to the parent and
  -- does NOT accumulate its state_gas_used; the guest's globals (evm_state_gas_left /
  -- evm_state_gas_used) were mutated in place by the child's SSTOREs, so we roll them back
  -- to the snapshot. On success (s0 != 0) leave them — the child's state gas stays
  -- accumulated (incorporate_child_on_success). x20 = child env here (pre-repoint).
  "  bnez s0, .Lfr_sgas_done\n" ++
  -- Revert every CREATE nonce-table mutation made since this child frame's
  -- entry checkpoint.  This is a journal replay, not a count truncation: it
  -- restores in-place advances of an existing creator as well as new entries.
  "  la t0, evm_call_depth; ld t1, 0(t0); slli t1, t1, 3\n" ++
  "  la t0, create_nonce_undo_checkpoint; add t0, t0, t1; ld a0, 0(t0)\n" ++
  "  jal ra, create_creator_nonce_undo_to\n" ++
  -- On child error, execution-specs `refill_frame_state_gas` returns the
  -- child state-gas allocation in LIFO order: the portion that spilled into
  -- `gas_left` is credited back to the child frame gas first, and only the
  -- non-spilled remainder returns to the state reservoir.
  "  ld t0, 632(x20)                 # used0
" ++
  "  la t1, evm_state_gas_used; ld t2, 0(t1)  # used
" ++
  "  la t1, evm_state_gas_left; ld t3, 0(t1)  # left, including child refunds
" ++
  "  la t1, evm_state_gas_spilled; ld t4, 0(t1)
" ++
  "  ld t5, 760(x20)                 # spilled0
" ++
  "  bleu t4, t5, .Lfr_sgas_no_spill_delta
" ++
  "  sub t4, t4, t5                 # child spilled allocation
" ++
  "  ld t6, 568(x20); add t6, t6, t4; sd t6, 568(x20)
" ++
  "  j .Lfr_sgas_have_spill_delta
" ++
  ".Lfr_sgas_no_spill_delta:
" ++
  "  li t4, 0
" ++
  ".Lfr_sgas_have_spill_delta:
" ++
  "  bleu t0, t2, .Lfr_sgas_used_ge_snapshot
" ++
  "  sub t2, t0, t2                 # child net state-gas credit
" ++
  "  bleu t3, t2, .Lfr_sgas_credit_zero_left
" ++
  "  sub t3, t3, t2                 # discard reverted child credit
" ++
  "  j .Lfr_sgas_restore_left
" ++
  ".Lfr_sgas_credit_zero_left:
" ++
  "  li t3, 0
" ++
  "  j .Lfr_sgas_restore_left
" ++
  ".Lfr_sgas_used_ge_snapshot:
" ++
  "  sub t2, t2, t0                 # child used allocation
" ++
  "  bleu t2, t4, .Lfr_sgas_restore_left
" ++
  "  sub t2, t2, t4                 # non-spilled remainder rolls back into left
" ++
  "  add t3, t3, t2
" ++
  ".Lfr_sgas_restore_left:
" ++
  "  la t1, evm_state_gas_left; sd t3, 0(t1)
" ++
  "  ld t0, 632(x20); la t1, evm_state_gas_used; sd t0, 0(t1)
" ++
  "  ld t0, 760(x20); la t1, evm_state_gas_spilled; sd t0, 0(t1)
" ++
  ".Lfr_create_credit_done:
" ++
  -- nxio8.4.2: discard the reverted child's EIP-3529 refund additions by restoring
  -- evm_refund_acc to the pre-child snapshot (incorporate_child_on_error does not
  -- add child.refund_counter). Success leaves it (the SSTORE refunds stay).
  "  ld t0, 640(x20); la t1, evm_refund_acc; sd t0, 0(t1)\n" ++
  -- nxio8.4.3: truncate the EIP-2929 storage-warmth set to the pre-child count,
  -- discarding keys the reverted child warmed (incorporate_child_on_error rolls
  -- back accessed_storage_keys). The keys array beyond the count is stale but a
  -- future cold access overwrites slot[count]. Success leaves it (warmth
  -- propagates up per incorporate_child_on_success).
  "  ld t0, 648(x20); la t1, evm_storage_access_count; sd t0, 0(t1)\n" ++
  -- EIP-2929 accessed_addresses has the same rollback rule as accessed_storage_keys:
  -- a reverted child does not propagate accounts it warmed to the parent.
  "  ld t0, 720(x20); la t1, evm_access_account_count; sd t0, 0(t1)\n" ++
  -- i3djw/reverted-CREATE rollback: truncate global effect logs to the
  -- pre-child snapshots captured by call_frame_descend. Successful child frames
  -- keep their CREATE/CALL value effects; reverted child frames discard them.
  "  ld t0, 656(x20); la t1, exec_nonstorage_effect_count; sd t0, 0(t1)\n" ++
  "  ld t0, 664(x20); la t1, exec_nonstorage_effect_overflow; sd t0, 0(t1)\n" ++
  "  ld t0, 672(x20); la t1, exec_code_effect_count; sd t0, 0(t1)\n" ++
  "  ld t0, 680(x20); la t1, exec_code_effect_next; sd t0, 0(t1)\n" ++
  "  ld t0, 688(x20); la t1, exec_code_effect_overflow; sd t0, 0(t1)\n" ++
  -- Restore this child's CodeState high-water marks on REVERT/exceptional
  -- return.  The current depth still names the child at this point.
  "  la t0, evm_call_depth; ld t2, 0(t0); slli t2, t2, 3\n" ++
  "  la t0, account_state_pending_checkpoint; add t0, t0, t2; ld t3, 0(t0); la t1, account_state_pending_count; sd t3, 0(t1)\n" ++
  "  la t0, account_state_created_checkpoint; add t0, t0, t2; ld t3, 0(t0); la t1, account_state_created_count; sd t3, 0(t1)\n" ++
  "  la t0, account_state_delete_checkpoint; add t0, t0, t2; ld t3, 0(t0); la t1, account_state_delete_count; sd t3, 0(t1)\n" ++
  "  la t0, evm_call_depth; ld t2, 0(t0); slli t2, t2, 3\n" ++
  "  la t0, evm_selfdestruct_seen_count_by_depth; add t0, t0, t2; ld t3, 0(t0); la t1, evm_selfdestruct_seen_count; sd t3, 0(t1)\n" ++
  "  la t0, evm_selfdestruct_seen_overflow_by_depth; add t0, t0, t2; ld t3, 0(t0); la t1, evm_selfdestruct_seen_overflow; sd t3, 0(t1)\n" ++
  "  ld t0, 728(x20); la t1, evm_selfdestruct_destroyed_count; sd t0, 0(t1)\n" ++
  -- 3hlnt.2.2: failed child frames restore the hot running block bloom from the
  -- child-depth checkpoint captured by call_frame_descend. Success leaves the
  -- child-updated hot bloom intact.
  "  la t0, evm_call_depth\n" ++
  "  ld t0, 0(t0)\n" ++
  "  addi t0, t0, -1\n" ++
  "  slli t0, t0, 8\n" ++
  "  la t1, rb_bloom_checkpoints\n" ++
  "  add t1, t1, t0                 # src = checkpoint[child_depth - 1]\n" ++
  "  la t2, rb_running_block_bloom  # dst = hot running block bloom\n" ++
  "  li t3, 32\n" ++
  ".Lfr_bloom_restore_loop:\n" ++
  "  beqz t3, .Lfr_bloom_restore_done\n" ++
  "  ld t4, 0(t1)\n" ++
  "  sd t4, 0(t2)\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lfr_bloom_restore_loop\n" ++
  ".Lfr_bloom_restore_done:\n" ++
  ".Lfr_sgas_done:\n" ++
  -- Capture child leftover gas after possible state-gas LIFO refill; held in
  -- s7 across the x20 repoint for the EIP-150 merge below.
  "  ld s7, 568(x20)\n" ++
  -- Load the saved call-context for the CURRENT (child) depth.
  "  la t0, evm_call_depth\n" ++
  "  ld t1, 0(t0)                   # t1 = child depth d\n" ++
  "  la t0, frame_call_ctx\n" ++
  "  slli t2, t1, 5                 # d * 32\n" ++
  "  add t0, t0, t2\n" ++
  "  ld s3, 0(t0)                   # parent_x12 (stack top at the CALL)\n" ++
  "  ld a3, 8(t0)                   # outoff_abs (parent output mem ptr)\n" ++
  "  ld a4, 16(t0)                  # outsize (output cap)\n" ++
  "  ld s6, 24(t0)                  # netPopBytes (CALL 192 / STATICCALL 160)\n" ++
  "                                 # NB: s4/s5 ARE x20/x21 (env/code base) — never use as scratch\n" ++
  -- Copy min(outsize, retlen) bytes of returndata into the caller output window.
  "  mv t2, s2                      # n = retlen\n" ++
  "  bgeu a4, t2, 1f                # if outsize >= retlen keep retlen\n" ++
  "  mv t2, a4                      # else n = outsize\n" ++
  "1:\n" ++
  "  beqz t2, 3f                    # nothing to copy\n" ++
  "  mv t3, s1                      # src = child returndata\n" ++
  "  mv t4, a3                      # dst = outoff_abs\n" ++
  "2:\n" ++
  "  lbu t0, 0(t3)\n" ++
  "  sb t0, 0(t4)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, 2b\n" ++
  "3:\n" ++
  -- Stage the child's returndata into `evm_precompile_frame` so the parent's
  -- RETURNDATASIZE(0x3d)/RETURNDATACOPY(0x3e) see the LAST sub-call's return
  -- (NoopReturnData reads size@+8, data@+16). This is independent of the
  -- output-window copy above (which is bounded by the CALL's `outsize`): the
  -- returndata buffer holds the FULL child return. `+8` keeps the TRUE retlen;
  -- the clamp against precompileFrameReturndataCapBytes is defense-in-depth
  -- only — retlen ≤ runtimeMemoryArenaLimitBytes (returnRevertMemoryGasAsm
  -- OOG-guards child RETURN/REVERT at the frame arena), which is below the
  -- cap, so all retlen bytes are staged and RETURNDATACOPY's
  -- `start+size ≤ retlen` guard alone keeps reads inside staged bytes.
  -- STOP / exceptional (s1=s2=0) -> size 0, no copy. Runs before x13 is
  -- repointed, so s1 still points into the (live) child memory.
  "  la t0, evm_precompile_frame\n" ++
  "  sd s2, 8(t0)                   # returndata size = retlen (true)\n" ++
  "  mv t2, s2                      # n = retlen\n" ++
  "  li t1, " ++ toString precompileFrameReturndataCapBytes ++ "\n" ++
  "  bgeu t1, t2, 7f                # if cap >= retlen keep retlen\n" ++
  "  mv t2, t1                      # else n = cap (never taken; see above)\n" ++
  "7:\n" ++
  "  beqz t2, 9f                    # nothing to copy\n" ++
  "  mv t3, s1                      # src = child returndata\n" ++
  "  addi t4, t0, 16                # dst = evm_precompile_frame + 16\n" ++
  "8:\n" ++
  "  lbu t1, 0(t3)\n" ++
  "  sb t1, 0(t4)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, 8b\n" ++
  "9:\n" ++
  -- Pop the depth: child d -> parent d-1.
  "  la t0, evm_call_depth\n" ++
  "  ld t1, 0(t0)                   # t1 = child depth d\n" ++
  "  la t3, frame_parent_bases\n" ++
  "  slli t4, t1, 4                 # d * 16\n" ++
  "  add t3, t3, t4\n" ++
  "  ld x13, 0(t3)                  # exact parent memory base\n" ++
  "  ld x20, 8(t3)                  # exact parent env base\n" ++
  "  addi t1, t1, -1                # t1 = parent depth\n" ++
  "  sd t1, 0(t0)\n" ++
  -- Restore parent PC (x10) and code base (x21).
  "  la t0, frame_save_area\n" ++
  "  slli t2, t1, 4                 # parent_depth * 16\n" ++
  "  add t0, t0, t2\n" ++
  "  ld x10, 0(t0)                  # parent pc (points AT the CALL opcode)\n" ++
  "  ld x21, 8(t0)                  # parent code base\n" ++
  -- x13/x20 already hold the exact parent memory/env bases.
  "  bnez t1, 4f\n" ++

  -- Frame-relative stack bounds: restore the guards to the depth-0 global arena.
  "  la t0, evm_cur_stack_top; la t2, evm_stack_top; sd t2, 0(t0)\n" ++
  "  la t0, evm_cur_stack_low; la t2, evm_stack_low; sd t2, 0(t0)\n" ++
  "  j 5f\n" ++
  "4:\n" ++
  "  addi t2, t1, -1               # (parent_depth - 1)\n" ++
  "  li t3, 0x19000               # FRAME_STRIDE\n" ++
  "  mul t2, t2, t3\n" ++
  "  la t3, call_frame_arena\n" ++
  "  add t2, t3, t2               # frame_base(parent_depth)\n" ++
  -- Frame-relative stack bounds: restore the guards to the parent frame's stack.
  "  li t3, 0x8200\n" ++
  "  add t3, t2, t3               # parent stack top = frame_base + frameStackTopOff\n" ++
  "  la t4, evm_cur_stack_top; sd t3, 0(t4)\n" ++
  "  li t4, 0x8000\n" ++
  "  sub t3, t3, t4               # parent stack low = top - 1024*32\n" ++
  "  la t4, evm_cur_stack_low; sd t3, 0(t4)\n" ++
  "5:\n" ++
  -- Merge child frame log cursors into the parent only on success. On failure,
  -- the parent env still holds the pre-child checkpoint values, so stale child
  -- entries past those cursors remain ignored.
  "  beqz s0, .Lfr_log_merge_done\n" ++
  "  sd s8, 448(x20)\n" ++
  "  sd s9, 464(x20)\n" ++
  "  sd s10, 472(x20)\n" ++
  ".Lfr_log_merge_done:\n" ++
  -- EIP-150 gas refund: return the child frame's UNUSED gas to the parent
  -- (x20 = parent env here). Pairs with the cost deduction in call_frame_descend.
  "  ld t0, 568(x20)\n" ++
  "  add t0, t0, s7\n" ++
  "  sd t0, 568(x20)\n" ++
  -- Restore the parent stack top: pop the CALL args, push the success word.
  "  add x12, s3, s6              # parent_x12 + netPopBytes\n" ++
  "  sd s0, 0(x12)\n" ++
  "  sd x0, 8(x12); sd x0, 16(x12); sd x0, 24(x12)\n" ++
  -- Resume the parent one byte past the CALL opcode.
  "  addi x10, x10, 1\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s6, 40(sp); ld s7, 48(sp)\n" ++
  "  ld s8, 56(sp); ld s9, 64(sp); ld s10, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `sparse_window_read(a0 = dst, a1 = window offset, a2 = window size,
    a3 = dense memory base)`: materialize the current frame's EVM-memory
    window `[offset, offset+size)` into a flat byte buffer at `dst`
    (evm-asm-0w05f.13, depth-1+ windows beyond the dense arena).

    Semantics: dst gets exactly what a per-byte read of the frame's memory
    model would produce — zeros, overlaid with the dense arena bytes for
    `[offset, min(end, runtimeMemoryArenaLimitBytes))`, overlaid with the
    depth-matching sparse word-store entries replayed in APPEND ORDER (a
    later MSTORE shadows an earlier one, mirroring `sparseMemoryLoadWordAsm`'s
    backward-scan-first-hit), each entry's 32 bytes converted from the stored
    stack-limb payload to the big-endian byte layout dense MSTORE writes
    (limb `j` at window bytes `[8*(3-j), 8*(3-j)+8)`, MSB first — see
    `Evm64.MStore.mstore_one_limb`) and clipped per byte at the window edges.

    The caller guarantees `size` fits the destination buffer (the RETURN
    tail guards `offset+size ≤ precompileFrameReturndataCapBytes`).
    Preserves a0-a3 and all dispatcher state; clobbers t0-t6 and a4-a7
    (x14-x17, dead at the RETURN/REVERT tail call sites). -/
def sparseWindowReadFunction : String :=
  "sparse_window_read:\n" ++
  -- Zero dst[0..size).
  "  mv t0, a0\n" ++
  "  mv t1, a2\n" ++
  "1:\n" ++
  "  beqz t1, 2f\n" ++
  "  sb x0, 0(t0)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j 1b\n" ++
  "2:\n" ++
  -- Dense overlap: copy [offset, min(end, dense_limit)) from a3 + offset.
  "  li t0, " ++ toString EvmAsm.Codegen.runtimeMemoryArenaLimitBytes ++ "\n" ++
  "  bgeu a1, t0, 3f\n" ++
  "  sub t1, t0, a1                 # dense bytes available past offset\n" ++
  "  bltu t1, a2, 21f\n" ++
  "  mv t1, a2                      # n = min(size, available)\n" ++
  "21:\n" ++
  "  add t2, a3, a1                 # src = dense base + offset\n" ++
  "  mv t3, a0                      # dst cursor\n" ++
  "22:\n" ++
  "  beqz t1, 3f\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  sb t4, 0(t3)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j 22b\n" ++
  "3:\n" ++
  -- Sparse replay, forward (append order): later entries shadow earlier.
  "  la t0, evm_sparse_memory_count\n" ++
  "  ld t0, 0(t0)\n" ++
  "  beqz t0, 9f\n" ++
  "  la t1, evm_sparse_memory_entries\n" ++
  -- evm-asm-m8pdu: match by frame TAG = (depth-epoch << 16) | depth (see
  -- sparseMemoryStoreWordAsm) so a returned same-depth sibling's stale
  -- entries never replay into this frame's window.
  "  la t2, evm_call_depth\n" ++
  "  ld t2, 0(t2)\n" ++
  "  la t3, evm_sparse_memory_epoch_by_depth\n" ++
  "  slli t2, t2, 3\n" ++
  "  add t3, t3, t2\n" ++
  "  ld t3, 0(t3)\n" ++
  "  slli t3, t3, 16\n" ++
  "  srli t2, t2, 3\n" ++
  "  or t2, t3, t2\n" ++
  "  add t6, a1, a2                 # window end\n" ++
  "4:\n" ++
  "  ld t3, 0(t1)                   # entry depth\n" ++
  "  bne t3, t2, 8f\n" ++
  "  ld t3, 8(t1)                   # entry offset\n" ++
  "  bgeu t3, t6, 8f                # entry starts at/after window end\n" ++
  "  addi t4, t3, 32\n" ++
  "  bgeu a1, t4, 8f                # entry ends at/before window start\n" ++
  -- Replay the entry's 32 bytes (limb j at bytes 8*(3-j)+0..7, MSB first),
  -- clipping each byte against [a1, t6).
  "  li t4, 3                       # j = 3 (high limb first)\n" ++
  "5:\n" ++
  "  slli t5, t4, 3\n" ++
  "  add t5, t1, t5\n" ++
  "  ld t5, 16(t5)                  # limb value\n" ++
  "  li a4, 3\n" ++
  "  sub a4, a4, t4\n" ++
  "  slli a4, a4, 3\n" ++
  "  add a4, t3, a4                 # abs byte cursor = entry_off + 8*(3-j)\n" ++
  "  li a5, 8\n" ++
  "6:\n" ++
  "  bltu a4, a1, 7f                # below window start: skip store\n" ++
  "  bgeu a4, t6, 7f                # at/past window end: skip store\n" ++
  "  srli a6, t5, 56\n" ++
  "  sub a7, a4, a1\n" ++
  "  add a7, a0, a7\n" ++
  "  sb a6, 0(a7)\n" ++
  "7:\n" ++
  "  slli t5, t5, 8\n" ++
  "  addi a4, a4, 1\n" ++
  "  addi a5, a5, -1\n" ++
  "  bnez a5, 6b\n" ++
  "  beqz t4, 8f\n" ++
  "  addi t4, t4, -1\n" ++
  "  j 5b\n" ++
  "8:\n" ++
  "  addi t1, t1, 48                # entry stride (8 depth + 8 offset + 32 payload)\n" ++
  "  addi t0, t0, -1\n" ++
  "  bnez t0, 4b\n" ++
  "9:\n" ++
  "  ret"

/-- `sparse_window_write(a0 = src, a1 = window offset, a2 = size,
    a3 = dense memory base, a4 = frame depth)`: write the flat byte buffer
    `src[0..size)` into a frame's EVM-memory model at
    `[offset, offset+size)` when the window's end lies beyond the dense
    arena (evm-asm-0w05f.13 surface 2 — the CALL out-window write-back for
    a nested caller; the callee's RETURN tail invokes this on the PARENT's
    model, so the depth is an argument, not `evm_call_depth`).

    - Bytes below `runtimeMemoryArenaLimitBytes` are copied raw into the
      dense arena (`a3 + offset`).
    - Each 32-byte chunk `[offset+32k, offset+32k+32)` whose end exceeds
      the dense limit is appended as one sparse word entry
      `(depth = a4, offset = offset+32k, payload = stack limbs)` — chunk
      offsets are aligned to the WINDOW start, which is exactly where the
      caller's subsequent MLOADs read (the word store is exact-offset
      keyed). A later append shadows earlier entries for both
      `sparseMemoryLoadWordAsm` (backward scan) and `sparse_window_read`
      (forward replay).
    - The final partial chunk starts from the frame's CURRENT model word
      at that offset (backward exact-offset scan, zeros default —
      mirroring `sparseMemoryLoadWordAsm`) and overlays the `size % 32`
      src bytes, so unwritten window-tail bytes keep their model value.
    - Appending past `sparseMemoryWordCapacity` routes to `.exit_outofgas`
      (conservative frame OOG, mirroring `sparseMemoryStoreWordAsm`) — a
      false-reject risk only, never a false accept.

    Byte-to-limb layout matches dense MSTORE (`Evm64.MStore.mstore_one_limb`):
    window byte `8*(3-j)+i` is bit `(7-i)*8..` of limb `j`.
    Entries are stamped/matched by frame TAG = (depth-epoch << 16) | depth
    (evm-asm-m8pdu), so a returned same-depth sibling frame's stale entries
    are never read back or shadow-matched.
    Preserves a0-a4; clobbers t0-t6 and a7. Uses a 48-byte sp scratch frame. -/
def sparseWindowWriteFunction : String :=
  "sparse_window_write:\n" ++
  "  addi sp, sp, -48\n" ++
  -- evm-asm-m8pdu: entries are stamped with the TARGET frame's TAG =
  -- (evm_sparse_memory_epoch_by_depth[a4] << 16) | a4 — the parent is still
  -- live at write-back time, so its epoch cell is current. The partial-chunk
  -- current-word scan below matches the same tag, so a returned same-depth
  -- sibling's stale entries are never read back. a7 holds the tag for the
  -- whole call (nothing else uses it).
  "  la t0, evm_sparse_memory_epoch_by_depth\n" ++
  "  slli t1, a4, 3\n" ++
  "  add t0, t0, t1\n" ++
  "  ld a7, 0(t0)\n" ++
  "  slli a7, a7, 16\n" ++
  "  or a7, a7, a4\n" ++
  -- Dense prefix: copy [offset, min(end, dense_limit)) raw.
  "  li t0, " ++ toString EvmAsm.Codegen.runtimeMemoryArenaLimitBytes ++ "\n" ++
  "  bgeu a1, t0, 2f\n" ++
  "  sub t1, t0, a1                 # dense bytes available past offset\n" ++
  "  bltu t1, a2, 1f\n" ++
  "  mv t1, a2                      # n_dense = min(size, available)\n" ++
  "1:\n" ++
  "  mv t2, a0                      # src cursor\n" ++
  "  add t3, a3, a1                 # dst cursor = dense base + offset\n" ++
  "11:\n" ++
  "  beqz t1, 2f\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  sb t4, 0(t3)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j 11b\n" ++
  "2:\n" ++
  -- Chunk loop: t0 = abs chunk offset, t1 = remaining bytes.
  "  mv t0, a1\n" ++
  "  mv t1, a2\n" ++
  "3:\n" ++
  "  beqz t1, 9f\n" ++
  "  addi t2, t0, 32\n" ++
  "  li t3, " ++ toString EvmAsm.Codegen.runtimeMemoryArenaLimitBytes ++ "\n" ++
  "  bgeu t3, t2, 8f                # chunk end <= dense limit: dense prefix covered it\n" ++
  -- Capacity check + claim the new entry (index = old count).
  "  la t2, evm_sparse_memory_count\n" ++
  "  ld t3, 0(t2)\n" ++
  "  li t4, " ++ toString sparseMemoryWordCapacity ++ "\n" ++
  "  bgeu t3, t4, .Lsww_capacity_oog\n" ++
  "  slli t4, t3, 5\n" ++
  "  slli t5, t3, 4\n" ++
  "  add t4, t4, t5\n" ++
  "  la t5, evm_sparse_memory_entries\n" ++
  "  add t4, t4, t5                 # t4 = new entry ptr\n" ++
  "  addi t3, t3, 1\n" ++
  "  sd t3, 0(t2)\n" ++
  "  sd a7, 0(t4)                   # entry tag = (epoch << 16) | target depth\n" ++
  "  sd t0, 8(t4)                   # entry offset = window-aligned chunk offset\n" ++
  -- Stage the chunk\'s 32 BE bytes at sp[0..32): src bytes for [0, min(rem,32)),
  -- current-model bytes (exact-offset backward scan, zeros default) for the rest.
  "  li t2, 32\n" ++
  "  bgeu t1, t2, 4f\n" ++
  -- Partial final chunk: seed sp[0..32) from the current model word at t0
  -- (mirrors sparseMemoryLoadWordAsm: exact-offset match, zeros default).
  "  sd x0, 0(sp); sd x0, 8(sp); sd x0, 16(sp); sd x0, 24(sp)\n" ++
  "  la t2, evm_sparse_memory_count\n" ++
  "  ld t2, 0(t2)\n" ++
  "  addi t2, t2, -1                # scan only the pre-existing entries\n" ++
  "41:\n" ++
  "  beqz t2, 44f\n" ++
  "  addi t2, t2, -1\n" ++
  "  slli t3, t2, 5\n" ++
  "  slli t5, t2, 4\n" ++
  "  add t3, t3, t5\n" ++
  "  la t5, evm_sparse_memory_entries\n" ++
  "  add t3, t3, t5                 # t3 = scanned entry ptr\n" ++
  "  ld t5, 0(t3)\n" ++
  "  bne t5, a7, 41b                # frame-tag mismatch (depth or epoch)\n" ++
  "  ld t5, 8(t3)\n" ++
  "  bne t5, t0, 41b                # offset mismatch\n" ++
  -- Hit: unpack the entry\'s limbs to BE bytes at sp[0..32)
  -- (limb j -> bytes 8*(3-j)..8*(3-j)+7, MSB first). t3 stays the entry ptr.
  "  li t5, 3                       # j\n" ++
  "42:\n" ++
  "  slli t6, t5, 3\n" ++
  "  add t6, t3, t6\n" ++
  "  ld t6, 16(t6)                  # limb j\n" ++
  "  li t2, 3\n" ++
  "  sub t2, t2, t5\n" ++
  "  slli t2, t2, 3\n" ++
  "  add t2, sp, t2                 # dst byte cursor = sp + 8*(3-j)\n" ++
  "  li a5, 8\n" ++
  "43:\n" ++
  "  srli a6, t6, 56\n" ++
  "  sb a6, 0(t2)\n" ++
  "  slli t6, t6, 8\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi a5, a5, -1\n" ++
  "  bnez a5, 43b\n" ++
  "  beqz t5, 44f\n" ++
  "  addi t5, t5, -1\n" ++
  "  j 42b\n" ++
  "44:\n" ++
  -- Overlay the src bytes [0, rem) over sp[0..32).
  "  sub t2, t0, a1                 # chunk offset within window\n" ++
  "  add t2, a0, t2                 # src cursor\n" ++
  "  mv t3, sp\n" ++
  "  mv t5, t1                      # rem (< 32)\n" ++
  "45:\n" ++
  "  beqz t5, 5f\n" ++
  "  lbu t6, 0(t2)\n" ++
  "  sb t6, 0(t3)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t5, t5, -1\n" ++
  "  j 45b\n" ++
  "4:\n" ++
  -- Full chunk: stage 32 src bytes at sp[0..32).
  "  sub t2, t0, a1\n" ++
  "  add t2, a0, t2                 # src cursor\n" ++
  "  mv t3, sp\n" ++
  "  li t5, 32\n" ++
  "46:\n" ++
  "  lbu t6, 0(t2)\n" ++
  "  sb t6, 0(t3)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t5, t5, -1\n" ++
  "  bnez t5, 46b\n" ++
  "5:\n" ++
  -- Pack sp[0..32) BE bytes into the entry\'s stack limbs (inverse of the
  -- unpack above): limb j = be64(sp[8*(3-j) .. 8*(3-j)+8)). t4 = entry ptr.
  "  li t5, 3                       # j\n" ++
  "51:\n" ++
  "  li t2, 3\n" ++
  "  sub t2, t2, t5\n" ++
  "  slli t2, t2, 3\n" ++
  "  add t2, sp, t2                 # src byte cursor = sp + 8*(3-j)\n" ++
  "  li t3, 8\n" ++
  "  li t6, 0\n" ++
  "52:\n" ++
  "  slli t6, t6, 8\n" ++
  "  lbu a5, 0(t2)\n" ++
  "  or t6, t6, a5\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, -1\n" ++
  "  bnez t3, 52b\n" ++
  "  slli t2, t5, 3\n" ++
  "  add t2, t4, t2\n" ++
  "  sd t6, 16(t2)                  # entry limb j\n" ++
  "  beqz t5, 6f\n" ++
  "  addi t5, t5, -1\n" ++
  "  j 51b\n" ++
  "6:\n" ++
  -- Advance past a processed chunk; a partial (rem < 32) chunk is the last.
  "  li t2, 32\n" ++
  "  bltu t1, t2, 9f\n" ++
  "8:\n" ++
  "  addi t0, t0, 32\n" ++
  "  li t2, 32\n" ++
  "  bltu t1, t2, 9f\n" ++
  "  addi t1, t1, -32\n" ++
  "  j 3b\n" ++
  "9:\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret\n" ++
  ".Lsww_capacity_oog:\n" ++
  "  addi sp, sp, 48\n" ++
  "  j .exit_outofgas"

/-- `zisk_frame_return`: unit probe for `frame_return` over synthesized state.
    It builds two return scenarios — a depth-1→0 return (parent uses the
    `evm_memory`/`evm_env` labels) and a depth-2→1 return (parent uses
    `frame_base(1)` = `call_frame_arena`) — and records the restored registers so
    a script can assert the pc/codebase/mem/env/stack-top math and the pushed
    success word.

    Output (depth-1→0 case):
      +0  packed parent codebase:pc+1     (expect 0x222:0x101)
      +8  running bloom word0 after success (expect child-updated word0)
      +16 packed x20/x13 deltas           (expect 0:0 against evm_env/evm_memory)
      +24 running bloom word31 after success
      +32 packed success:x12-delta        (expect 1:192)
      +48 evm_call_depth after            (expect 0)
    Output (depth-2→1 case):
      +40 running bloom word0 after REVERT (expect checkpoint[1] word0)
      +56 packed x20/x13 deltas           (expect 0x18400:0 against call_frame_arena)
      +64 running bloom word31 after REVERT
      +72 x12 - &fr_pstack2               (expect 160 = netPopBytes)
      +80 success word at x12             (expect 0 — REVERT path)
      +88 evm_call_depth after            (expect 1)
      +96 first copied returndata byte at outoff_abs (expect 0xab)
    Frame-relative stack-bound restores:
      +104 evm_cur_stack_top - &evm_stack_top   (scenario A, expect 0)
      +112 evm_cur_stack_top - &call_frame_arena (scenario B, expect 0x8200)
    Returndata staging into evm_precompile_frame:
      +120 precompile_frame size after scenario A (STOP, expect 0)
      +128 scenario B pack: data[299] << 32 | size (expect 0x5a<<32 | 300 —
           the high half witnesses full staging past the old 256-byte cap)
      +136 precompile_frame data[0] after scenario B (expect 0xab)
    EIP-150 gas refund (parent gas += child leftover):
      +144 parent gas after scenario A (100 + 50 = 150)
      +152 parent gas after scenario B (200 + 30 = 230)
    Log cursor merge/rollback:
      +224 parent persistent cursor after success
      +232 parent transient/event cursors after success packed as transient<<32 | event
      +240 parent persistent cursor after revert
      +248 parent transient/event cursors after revert packed as transient<<32 | event -/
def ziskFrameReturnPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- ---- Scenario A: depth 1 -> 0, STOP-style (no returndata) ----
  "  la t0, evm_call_depth; li t1, 1; sd t1, 0(t0)\n" ++
  -- frame_save_area[0] = (pc=0x100, cb=0x222)
  "  la t0, frame_save_area; li t1, 0x100; sd t1, 0(t0); li t1, 0x222; sd t1, 8(t0)\n" ++
  -- frame_call_ctx[1] = (parent_x12=fr_pstack, outoff_abs=fr_out, outsize=0, netPop=192)
  "  la t0, frame_call_ctx; addi t0, t0, 32\n" ++
  "  la t1, fr_pstack; sd t1, 0(t0)\n" ++
  "  la t1, fr_out; sd t1, 8(t0)\n" ++
  "  sd x0, 16(t0)\n" ++
  "  li t1, 192; sd t1, 24(t0)\n" ++
  "  la t0, frame_parent_bases; addi t0, t0, 16; la t1, evm_memory; sd t1, 0(t0); la t1, evm_env; sd t1, 8(t0)\n" ++
  "  la x20, fr_child_env\n" ++                       -- child env for the gas read
  "  la t0, fr_child_env; li t1, 50; sd t1, 568(t0)\n" ++   -- child leftover gas = 50
  "  la t0, evm_env;      li t1, 100; sd t1, 568(t0)\n" ++  -- parent gas = 100
  -- Success should merge the child's committed storage/transient/event cursors into the parent.
  "  la t0, fr_child_env; li t1, 12; sd t1, 448(t0); li t1, 13; sd t1, 464(t0); li t1, 14; sd t1, 472(t0)\n" ++
  "  la t0, evm_env;      li t1, 1;  sd t1, 448(t0); li t1, 2;  sd t1, 464(t0); li t1, 3;  sd t1, 472(t0)\n" ++
  -- nxio8.4.1: state gas before a SUCCESS return = 1000/2000; success leaves the
  -- globals (child state-gas stays accumulated); the +624/632 snapshot is ignored.
  "  la t0, evm_state_gas_left; li t1, 1000; sd t1, 0(t0)\n" ++
  "  la t0, evm_state_gas_used; li t1, 2000; sd t1, 0(t0)\n" ++
  "  la t0, evm_refund_acc; li t1, 3000; sd t1, 0(t0)\n" ++   -- nxio8.4.2: success leaves refund
  "  la t0, evm_storage_access_count; li t1, 11; sd t1, 0(t0)\n" ++   -- nxio8.4.3: success leaves warmth
  "  la t0, fr_child_env; li t1, 333; sd t1, 624(t0); li t1, 444; sd t1, 632(t0); li t1, 888; sd t1, 640(t0); li t1, 22; sd t1, 648(t0)\n" ++
  "  la t0, rb_running_block_bloom; li t1, 0x1111222233334444; sd t1, 0(t0); li t1, 0xaaaabbbbccccdddd; sd t1, 248(t0)\n" ++
  "  li a0, 1; li a1, 0; li a2, 0\n" ++
  "  jal ra, frame_return\n" ++
  "  slli t0, x21, 32; or t0, t0, x10; sd t0, 0(s0)       # pack parent_cb:parent_pc+1\n" ++
  "  la t0, rb_running_block_bloom; ld t1, 0(t0); sd t1, 8(s0); ld t1, 248(t0); sd t1, 24(s0)\n" ++
  "  la t0, evm_memory; sub t1, x13, t0; la t0, evm_env; sub t2, x20, t0; slli t2, t2, 32; or t1, t1, t2; sd t1, 16(s0)\n" ++
  "  la t0, fr_pstack; sub t1, x12, t0; ld t2, 0(x12); slli t2, t2, 32; or t1, t1, t2; sd t1, 32(s0)\n" ++
  "  la t0, evm_call_depth; ld t1, 0(t0); sd t1, 48(s0)  # expect 0\n" ++
  -- frame-relative stack bounds restored to the depth-0 global arena (cur_top == &evm_stack_top).
  "  la t0, evm_cur_stack_top; ld t1, 0(t0); la t2, evm_stack_top; sub t1, t1, t2; sd t1, 104(s0)  # expect 0\n" ++
  -- returndata staging: STOP carried no returndata -> precompile_frame size 0.
  "  la t0, evm_precompile_frame; ld t1, 8(t0); sd t1, 120(s0)  # expect 0\n" ++
  -- EIP-150 gas refund: parent gas 100 + child leftover 50 = 150.
  "  la t0, evm_env; ld t1, 568(t0); sd t1, 144(s0)  # expect 150\n" ++
  -- nxio8.4.1: SUCCESS leaves the state-gas globals unchanged (1000/2000).
  "  la t0, evm_state_gas_left; ld t1, 0(t0); sd t1, 160(s0)  # expect 1000\n" ++
  "  la t0, evm_state_gas_used; ld t1, 0(t0); sd t1, 168(s0)  # expect 2000\n" ++
  "  la t0, evm_refund_acc; ld t1, 0(t0); sd t1, 192(s0)      # expect 3000 (success leaves)\n" ++
  "  la t0, evm_storage_access_count; ld t1, 0(t0); sd t1, 208(s0)  # expect 11 (success leaves)\n" ++
  "  la t0, evm_env; ld t1, 448(t0); sd t1, 224(s0)  # expect 12 (success merges persistent)\n" ++
  "  ld t1, 464(t0); slli t1, t1, 32; ld t2, 472(t0); or t1, t1, t2; sd t1, 232(s0)  # expect 13<<32 | 14\n" ++
  -- ---- Scenario B: depth 2 -> 1, REVERT-style with a returndata byte ----
  "  la t0, evm_call_depth; li t1, 2; sd t1, 0(t0)\n" ++
  -- frame_save_area[1] = (pc=0x300, cb=0x444)
  "  la t0, frame_save_area; addi t0, t0, 16; li t1, 0x300; sd t1, 0(t0); li t1, 0x444; sd t1, 8(t0)\n" ++
  -- frame_call_ctx[2] = (parent_x12=fr_pstack2, outoff_abs=fr_out, outsize=1, netPop=160)
  "  la t0, frame_call_ctx; addi t0, t0, 64\n" ++
  "  la t1, fr_pstack2; sd t1, 0(t0)\n" ++
  "  la t1, fr_out; sd t1, 8(t0)\n" ++
  "  li t1, 1; sd t1, 16(t0)\n" ++
  "  li t1, 160; sd t1, 24(t0)\n" ++
  "  la t0, frame_parent_bases; addi t0, t0, 32; la t1, call_frame_arena; sd t1, 0(t0); li t1, 0x18400; la t2, call_frame_arena; add t1, t1, t2; sd t1, 8(t0)\n" ++
  -- returndata source: 300 bytes (> the old 256 cap) — first byte 0xab, a
  -- marker 0x5a at index 299 to witness full-length staging past 256.
  "  la t0, fr_ret; li t1, 0xab; sb t1, 0(t0)\n" ++
  "  li t1, 0x5a; sb t1, 299(t0)\n" ++
  "  la x20, fr_child_env\n" ++
  "  la t0, fr_child_env; li t1, 30; sd t1, 568(t0)\n" ++   -- child leftover gas = 30
  "  la t0, call_frame_arena; li t2, 0x18400; add t0, t0, t2; li t1, 200; sd t1, 568(t0)\n" ++  -- parent (frame[1]) gas = 200
  -- Revert should preserve the parent's pre-child cursors and ignore the child lengths.
  "  la t0, fr_child_env; li t1, 99; sd t1, 448(t0); li t1, 98; sd t1, 464(t0); li t1, 97; sd t1, 472(t0)\n" ++
  "  la t0, call_frame_arena; li t2, 0x18400; add t0, t0, t2; li t1, 21; sd t1, 448(t0); li t1, 22; sd t1, 464(t0); li t1, 23; sd t1, 472(t0)\n" ++
  -- nxio8.4.1: child mutated the state-gas globals to 444/766; the pre-child
  -- snapshot (555/666) lives in the child env at +624/632. A REVERT must roll the
  -- globals back to the snapshot (incorporate_child_on_error returns the child's
  -- entire state-gas allocation; state_gas_used is not accumulated).
  "  la t0, evm_state_gas_left; li t1, 444; sd t1, 0(t0)\n" ++
  "  la t0, evm_state_gas_used; li t1, 766; sd t1, 0(t0)\n" ++
  "  la t0, evm_refund_acc; li t1, 9999; sd t1, 0(t0)\n" ++   -- child-modified refund
  "  la t0, evm_storage_access_count; li t1, 33; sd t1, 0(t0)\n" ++   -- child-modified warmth count
  "  la t0, fr_child_env; li t1, 555; sd t1, 624(t0); li t1, 666; sd t1, 632(t0); li t1, 777; sd t1, 640(t0); li t1, 44; sd t1, 648(t0)\n" ++
  "  la t0, rb_running_block_bloom; li t1, 0x9999888877776666; sd t1, 0(t0); li t1, 0x5555444433332222; sd t1, 248(t0)\n" ++
  "  la t0, rb_bloom_checkpoints; addi t0, t0, 256; li t1, 0x123456789abcdef0; sd t1, 0(t0); li t1, 0x0fedcba987654321; sd t1, 248(t0)\n" ++
  "  li a0, 0; la a1, fr_ret; li a2, 300\n" ++
  "  jal ra, frame_return\n" ++
  "  la t0, rb_running_block_bloom; ld t1, 0(t0); sd t1, 40(s0); ld t1, 248(t0); sd t1, 64(s0)\n" ++
  "  la t0, call_frame_arena; sub t1, x13, t0; sub t2, x20, t0; slli t2, t2, 32; or t1, t1, t2; sd t1, 56(s0)\n" ++
  "  la t0, fr_pstack2; sub t0, x12, t0; sd t0, 72(s0)         # expect 160\n" ++
  "  ld t0, 0(x12); sd t0, 80(s0)                              # expect 0\n" ++
  "  la t0, evm_call_depth; ld t1, 0(t0); sd t1, 88(s0)        # expect 1\n" ++
  "  la t0, fr_out; lbu t1, 0(t0); sd t1, 96(s0)               # expect 0xab\n" ++
  -- frame-relative stack bounds restored to the parent frame[1] arena stack.
  "  la t0, evm_cur_stack_top; ld t1, 0(t0); la t2, call_frame_arena; sub t1, t1, t2; sd t1, 112(s0)  # expect 0x8200\n" ++
  -- returndata staging: retlen 300 -> precompile_frame size 300; first byte
  -- 0xab @ +16; byte 299 (past the old 256 cap) staged @ +16+299, packed into
  -- the size cell's high half (the 256-byte probe output window is full).
  "  la t0, evm_precompile_frame; ld t1, 8(t0)\n" ++
  "  lbu t2, 315(t0); slli t2, t2, 32; or t1, t1, t2\n" ++
  "  sd t1, 128(s0)                                               # expect 0x5a<<32 | 300\n" ++
  "  la t0, evm_precompile_frame; lbu t1, 16(t0); sd t1, 136(s0)  # expect 0xab\n" ++
  -- EIP-150 gas refund: parent gas 200 + child leftover 30 = 230.
  "  la t0, call_frame_arena; li t2, 0x18400; add t0, t0, t2; ld t1, 568(t0); sd t1, 152(s0)  # expect 230\n" ++
  -- nxio8.4.1: REVERT restored the state-gas globals to the child-env snapshot.
  "  la t0, evm_state_gas_left; ld t1, 0(t0); sd t1, 176(s0)  # expect 555\n" ++
  "  la t0, evm_state_gas_used; ld t1, 0(t0); sd t1, 184(s0)  # expect 666\n" ++
  "  la t0, evm_refund_acc; ld t1, 0(t0); sd t1, 200(s0)      # expect 777 (revert restores)\n" ++
  "  la t0, evm_storage_access_count; ld t1, 0(t0); sd t1, 216(s0)  # expect 44 (revert restores)\n" ++
  "  la t0, call_frame_arena; li t2, 0x18400; add t0, t0, t2; ld t1, 448(t0); sd t1, 240(s0)  # expect 21 (revert preserves persistent)\n" ++
  "  ld t1, 464(t0); slli t1, t1, 32; ld t2, 472(t0); or t1, t1, t2; sd t1, 248(s0)  # expect 22<<32 | 23\n" ++
  "  j .Lfr_done\n" ++
  frameReturnFunction ++ "\n" ++
  createCreatorNonceUseFunction ++ "\n" ++
  ".Lfr_done:"

/-- Data stubs so the probe links standalone (the real symbols live in the guest's
    dispatcher data section). `call_frame_arena` holds frame[1] (depth-2→1 parent). -/
def ziskFrameReturnDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "evm_call_depth:\n  .zero 8\n" ++
  ".balign 16\n" ++
  "frame_save_area:\n  .zero 16400\n" ++
  ".balign 32\n" ++
  "frame_call_ctx:\n  .zero 32800\n" ++          -- 1025 × 32 B
  ".balign 16\n" ++
  "frame_parent_bases:\n  .zero 16400\n" ++          -- 1025 × 16 B
  ".balign 32\n" ++
  "call_frame_arena:\n  .zero " ++ toString (0x19000 : Nat) ++ "\n" ++
  ".balign 32\n" ++
  "evm_memory:\n  .zero 64\n" ++
  "evm_env:\n  .zero 640\n" ++          -- enlarged: frame_return refunds gas at env+568
  "fr_child_env:\n  .zero 768\n" ++       -- child env (x20 at frame_return entry); +568 = child gas, +624/632 = state-gas snapshot (nxio8.4.1)
  -- nxio8.4.1: global EIP-8037 state-gas accumulators (the real symbols live in
  -- the guest dispatcher data section; stubbed here so the probe links).
  "evm_state_gas_left:\n  .zero 8\n" ++
  "evm_state_gas_used:\n  .zero 8\n" ++
  "evm_state_gas_spilled:\n  .zero 8\n" ++
  "evm_refund_acc:\n  .zero 8\n" ++
  "evm_storage_access_count:\n  .zero 8\n" ++
  "evm_access_account_count:\n  .zero 8\n" ++
  "evm_selfdestruct_destroyed_count:\n  .zero 8\n" ++
  "exec_nonstorage_effect_count:\n  .zero 8\n" ++
  "exec_nonstorage_effect_overflow:\n  .zero 8\n" ++
  "exec_code_effect_count:\n  .zero 8\n" ++
  "exec_code_effect_next:\n  .zero 8\n" ++
  "exec_code_effect_overflow:\n  .zero 8\n" ++
  "rb_running_block_bloom:\n  .zero 256\n" ++
  "rb_running_receipt_bloom:\n  .zero 256\n" ++
  "rb_bloom_checkpoints:\n  .zero 262144\n" ++

  -- Frame-relative stack-bound labels + cells. `evm_stack_top`/`evm_stack_low`
  -- are address-only stubs (frame_return takes their `&` for the depth-0
  -- restore); the cur cells hold the restored current-frame bounds.
  "evm_stack_top:\n  .zero 8\n" ++
  "evm_stack_low:\n  .zero 8\n" ++
  "evm_cur_stack_top:\n  .zero 8\n" ++
  "evm_cur_stack_low:\n  .zero 8\n" ++
  -- Returndata staging target (frame_return writes size@+8, data@+16).
  ".balign 8\n" ++
  "evm_precompile_frame:\n  .zero " ++ toString (16 + precompileFrameReturndataCapBytes) ++ "\n" ++
  "fr_pstack:\n  .zero 256\n" ++
  "fr_pstack2:\n  .zero 256\n" ++
  "fr_out:\n  .zero 64\n" ++
  "fr_ret:\n  .zero 512\n" ++
  createNonceTableData

def ziskFrameReturnProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskFrameReturnPrologue
  dataAsm     := ziskFrameReturnDataSection
}

end EvmAsm.Codegen
