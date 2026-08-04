/-
  EvmAsm.Codegen.Programs.ChildFrameHandlerTails

  Extracted from `ChildFrameHandlers.lean` to keep every file under the
  `FileSizeGuard` line cap. Holds the CALL/STATICCALL precompile tail builder
  plus delegation-access helper. The CREATE-family tail lives in
  `ChildFrameCreateTail.lean` and is re-exported through this import chain.
-/

import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Codegen.Programs.EvmStorageAccessGas
import EvmAsm.Codegen.Programs.PrecompileRuntime
import EvmAsm.Codegen.Programs.AmsterdamSystemTx
import EvmAsm.Rv64.Program
import EvmAsm.Stateless.SpecRef.Gas
import EvmAsm.Codegen.Programs.ChildFrameHandlerTailHelpers
namespace EvmAsm.Codegen
open EvmAsm.Rv64

/-- Process a CALL-family message whose `code_address` may select a precompile.

    This is the shared message-processor portion of the four child CALL-family
    handlers.  Its ABI is deliberately explicit: `x10` is the EVM dispatch PC,
    `x12` is the operand-stack cursor, `x13` is the frame memory base, and
    `x20` is the current EVM environment.  The offset parameters describe the
    caller's stack layout; `netPopBytes` is the result-stack adjustment; and
    `fallThroughAsm` resumes ordinary bytecode processing when `code_address`
    is not a supported precompile.  Callers must materialise that ABI rather
    than relying on a route-specific scratch convention. -/
def precompileMessageProcessorAsm
      (tag : String) (netPopBytes inOffsetOff inSizeOff outOffsetOff outSizeOff : Nat)
      (valueOff? : Option Nat)
      (fallThroughAsm : String)
      (sparseWindows : Bool := false) : String :=
    -- Stack top at entry is the call gas word. The destination
    -- address is the next word for both CALL and STATICCALL. EVM
    -- address operands are masked to the low 160 bits: limb 1 and
    -- the low 32 bits of limb 2 participate in precompile dispatch,
    -- while bits 160..255 are ignored.
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  addi t0, x12, 32\n" ++
    "  la t1, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
    runtimeAccessWordToBe20Asm tag "t0" "t1" "t2" "t3" ++
    -- Materialize the CALL target for the initial access charge. The save triple above
    -- is the definition source for the restores after that charge: every CALL-family
    -- handler enters this common tail before reaching them.
    --
    -- Delegation resolution must remain after the initial access/transfer/memory gas
    -- check. The original target is nevertheless always read by the spec's
    -- `get_account(tx_state, code_address)` once that check has passed; the helper
    -- below records a second read only for a resolved `0xef0100 || address` delegate.
    --
    "  la a0, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
    "  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
    "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
    "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
    "  jal ra, runtime_access_account_charge\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    callMemoryExpansionGasAsm
      ("precompile_" ++ tag)
      inOffsetOff inSizeOff outOffsetOff outSizeOff sparseWindows ++
    -- State access begins only after the initial access/transfer/memory gas check.
    -- The value-gas probe does not charge: the branch-specific fall-through or
    -- precompile gate performs the single actual CALL_VALUE charge later. Its
    -- purpose is to keep the producer behind the complete static check.
    (match valueOff? with
    | none => ""
    | some valueOff => callValueGasAvailabilityGateAsm tag valueOff) ++
    -- `system.py` then unconditionally reads `code_address`, and
    -- `state_tracker.get_account_optional` first adds it to `account_reads`.
    -- Preserve x10/x12/x13: x10 is the dispatch PC and the tail still consumes all
    -- three after this recorder returns.
    "  addi sp, sp, -32; sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
    "  la a0, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
    "  jal ra, account_read_record\n" ++
    "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 32\n" ++
    -- A delegated marker additionally records its resolved code address.
    callDelegationAccessChargeAsm tag ++
    (if tag == "call_target" || tag == "staticcall_target" then (
    -- EIP-4788 beacon-roots system contract fast path for the current block's
    -- begin-of-block write. The ordinary bytecode descent resolves storage at a
    -- committed header root and therefore cannot see the just-modeled system
    -- storage update; `system_writes` has already staged that `(timestamp, root)`
    -- pair in swd_4788_{val,root_val}. CALLCODE/DELEGATECALL into the predeploy
    -- must keep normal bytecode semantics because their ADDRESS context is the
    -- caller, not the system contract. Historical/stale cases also keep using the
    -- normal bytecode path below.
    "  la t0, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
    "  la t1, bsr_addr_4788\n" ++
    "  li t2, 20\n" ++
    ".L" ++ tag ++ "_eip4788_addr_cmp:\n" ++
    "  beqz t2, .L" ++ tag ++ "_eip4788_addr_match\n" ++
    "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .L" ++ tag ++ "_eip4788_fallthrough\n" ++
    "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .L" ++ tag ++ "_eip4788_addr_cmp\n" ++
    ".L" ++ tag ++ "_eip4788_addr_match:\n" ++
    -- This specialized EIP-4788 region returns without descending on both its
    -- current-success and same-slot-stale arms.  Gate before either arm can
    -- take its special child-allotment charge.
    precompileDepthGateAsm (tag ++ "_eip4788_depth") netPopBytes ++
    (match valueOff? with
    | none => ""
    | some valueOff =>
      -- A value-bearing CALL needs the complete generic-call machinery:
      -- balance validation, CALL_VALUE gas, value transfer, child rollback,
      -- and EIP-7708 logging. The callee seed now contains the current-block
      -- system-write overlay, so normal bytecode descent is exact here.
      "  ld t0, " ++ toString valueOff ++ "(x12); ld t1, " ++ toString (valueOff + 8) ++ "(x12); or t0, t0, t1\n" ++
      "  ld t1, " ++ toString (valueOff + 16) ++ "(x12); or t0, t0, t1; ld t1, " ++ toString (valueOff + 24) ++ "(x12); or t0, t0, t1\n" ++
      "  bnez t0, .L" ++ tag ++ "_eip4788_fallthrough\n") ++
    "  ld t0, " ++ toString inSizeOff ++ "(x12); li t1, 32; bne t0, t1, .L" ++ tag ++ "_eip4788_fallthrough\n" ++
    "  ld t0, 0(x12); li t1, 3000; bltu t0, t1, .L" ++ tag ++ "_eip4788_fallthrough\n" ++
    "  ld t0, " ++ toString inOffsetOff ++ "(x12); add t0, x13, t0\n" ++
    "  li t2, 24\n" ++
    ".L" ++ tag ++ "_eip4788_ts_hi_zero:\n" ++
    "  beqz t2, .L" ++ tag ++ "_eip4788_ts_low_cmp_init\n" ++
    "  lbu t3, 0(t0); bnez t3, .L" ++ tag ++ "_eip4788_fallthrough\n" ++
    "  addi t0, t0, 1; addi t2, t2, -1; j .L" ++ tag ++ "_eip4788_ts_hi_zero\n" ++
    ".L" ++ tag ++ "_eip4788_ts_low_cmp_init:\n" ++
    "  mv t5, t0\n" ++
    "  la t1, swd_ts_be8\n" ++
    "  li t2, 8\n" ++
    ".L" ++ tag ++ "_eip4788_ts_cmp:\n" ++
    "  beqz t2, .L" ++ tag ++ "_eip4788_current\n" ++
    "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .L" ++ tag ++ "_eip4788_stale_slot_check\n" ++
    "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .L" ++ tag ++ "_eip4788_ts_cmp\n" ++
    ".L" ++ tag ++ "_eip4788_stale_slot_check:\n" ++
    "  mv t0, t5; li t2, 8; li t3, 0\n" ++
    ".L" ++ tag ++ "_eip4788_req_ts_u64:\n" ++
    "  beqz t2, .L" ++ tag ++ "_eip4788_req_idx\n" ++
    "  lbu t4, 0(t0); slli t3, t3, 8; or t3, t3, t4; addi t0, t0, 1; addi t2, t2, -1; j .L" ++ tag ++ "_eip4788_req_ts_u64\n" ++
    ".L" ++ tag ++ "_eip4788_req_idx:\n" ++
    "  li t4, 8191; remu t3, t3, t4\n" ++
    "  la t0, swd_4788_slot; lbu t4, 30(t0); slli t4, t4, 8; lbu t6, 31(t0); or t4, t4, t6\n" ++
    "  beq t3, t4, .L" ++ tag ++ "_eip4788_stale_current_slot\n" ++
    "  j .L" ++ tag ++ "_eip4788_fallthrough\n" ++
    ".L" ++ tag ++ "_eip4788_current:\n" ++
    -- The shortcut substitutes for the successful user-call path through the
    -- beacon-roots bytecode. Debit that path's regular gas from the EIP-150
    -- child allotment: non-SLOAD opcodes + two warm SLOAD floors, plus the
    -- 2900-gas cold delta for each slot not already warmed by the tx access list.
    "  la t0, stal_token_le; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
    "  la t1, bsr_addr_4788; addi t1, t1, 19; li t2, 20\n" ++
    ".L" ++ tag ++ "_eip4788_token_copy:\n" ++
    "  lbu t3, 0(t1); sb t3, 0(t0); addi t0, t0, 1; addi t1, t1, -1; addi t2, t2, -1; bnez t2, .L" ++ tag ++ "_eip4788_token_copy\n" ++
    "  la t0, stal_slot_le; la t1, swd_4788_slot; addi t1, t1, 31; li t2, 32\n" ++
    ".L" ++ tag ++ "_eip4788_ts_slot_copy:\n" ++
    "  lbu t3, 0(t1); sb t3, 0(t0); addi t0, t0, 1; addi t1, t1, -1; addi t2, t2, -1; bnez t2, .L" ++ tag ++ "_eip4788_ts_slot_copy\n" ++
    "  la t0, cd_callee_be; la t1, swd_4788_root_slot; addi t1, t1, 31; li t2, 32\n" ++
    ".L" ++ tag ++ "_eip4788_root_slot_copy:\n" ++
    "  lbu t3, 0(t1); sb t3, 0(t0); addi t0, t0, 1; addi t1, t1, -1; addi t2, t2, -1; bnez t2, .L" ++ tag ++ "_eip4788_root_slot_copy\n" ++
    "  li x16, 320\n" ++
    "  la t6, stal_token_le; la a1, stal_slot_le\n" ++
    storageAccessKeyScanAsm (tag ++ "_eip4788_ts_scan") (tag ++ "_eip4788_ts_warm") (tag ++ "_eip4788_ts_cold") (tag ++ "_eip4788_ts_next") ++
    ".L" ++ tag ++ "_eip4788_ts_warm:\n" ++
    "  j .L" ++ tag ++ "_eip4788_root_cost\n" ++
    ".L" ++ tag ++ "_eip4788_ts_cold:\n" ++
    "  li x17, 2900; add x16, x16, x17\n" ++
    ".L" ++ tag ++ "_eip4788_root_cost:\n" ++
    "  la t6, stal_token_le; la a1, cd_callee_be\n" ++
    storageAccessKeyScanAsm (tag ++ "_eip4788_root_scan") (tag ++ "_eip4788_root_warm") (tag ++ "_eip4788_root_cold") (tag ++ "_eip4788_root_next") ++
    ".L" ++ tag ++ "_eip4788_root_warm:\n" ++
    "  j .L" ++ tag ++ "_eip4788_charge\n" ++
    ".L" ++ tag ++ "_eip4788_root_cold:\n" ++
    "  li x17, 2900; add x16, x16, x17\n" ++
    ".L" ++ tag ++ "_eip4788_charge:\n" ++
    chargePrecompileGasWithAllotmentAsm tag "x16" "x17" ++
    "  addi sp, sp, -32; sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
    "  la a0, stal_token_le; la a1, stal_slot_le; jal ra, evm_storage_access_seed_key\n" ++
    "  la a0, stal_token_le; la a1, cd_callee_be; jal ra, evm_storage_access_seed_key\n" ++
    "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 32\n" ++
    "  li t0, 1; la t1, bv_eip4788_current_fast_seen; sd t0, 0(t1)\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li t0, 1; sd t0, 0(x15)\n" ++
    "  li t0, 32; sd t0, 8(x15)\n" ++
    "  addi t1, x15, 16; li t2, 32\n" ++
    ".L" ++ tag ++ "_eip4788_frame_zero:\n" ++
    "  sb zero, 0(t1); addi t1, t1, 1; addi t2, t2, -1; bnez t2, .L" ++ tag ++ "_eip4788_frame_zero\n" ++
    "  la t0, swd_4788_root_vlen; ld t2, 0(t0); beqz t2, .L" ++ tag ++ "_eip4788_frame_ready\n" ++
    "  li t3, 32; bgtu t2, t3, .L" ++ tag ++ "_eip4788_frame_ready\n" ++
    "  addi t1, x15, 48; sub t1, t1, t2; la t0, swd_4788_root_val\n" ++
    ".L" ++ tag ++ "_eip4788_frame_copy:\n" ++
    "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .L" ++ tag ++ "_eip4788_frame_copy\n" ++
    ".L" ++ tag ++ "_eip4788_frame_ready:\n" ++
    "  ld t2, " ++ toString outSizeOff ++ "(x12); li t3, 32; bgeu t2, t3, .L" ++ tag ++ "_eip4788_out_cap\n" ++
    "  mv t3, t2\n" ++
    ".L" ++ tag ++ "_eip4788_out_cap:\n" ++
    "  beqz t3, .L" ++ tag ++ "_eip4788_success\n" ++
    "  addi t0, x15, 16; ld t1, " ++ toString outOffsetOff ++ "(x12); add t1, x13, t1\n" ++
    ".L" ++ tag ++ "_eip4788_out_copy:\n" ++
    "  lbu t2, 0(t0); sb t2, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t3, t3, -1; bnez t3, .L" ++ tag ++ "_eip4788_out_copy\n" ++
    ".L" ++ tag ++ "_eip4788_success:\n" ++
    "  addi x12, x12, " ++ toString netPopBytes ++ "\n" ++
    "  li x14, 1; sd x14, 0(x12); sd x0, 8(x12); sd x0, 16(x12); sd x0, 24(x12)\n" ++
    "  j .L" ++ tag ++ "_eip4788_done\n" ++
    ".L" ++ tag ++ "_eip4788_stale_current_slot:\n" ++
    -- Same-slot stale requests execute the EIP-4788 bytecode until the stored
    -- timestamp check fails and reverts. The parent-state bytecode fallback is
    -- wrong here because it cannot see the current block's begin-of-block write;
    -- charge the regular gas used by that revert path before returning CALL=0.
    "  li x16, 3104\n" ++
    chargePrecompileGasWithAllotmentAsm tag "x16" "x17" ++
    "  ld t2, " ++ toString outSizeOff ++ "(x12); li t3, 32; bgeu t2, t3, .L" ++ tag ++ "_eip4788_stale_out_cap\n" ++
    "  mv t3, t2\n" ++
    ".L" ++ tag ++ "_eip4788_stale_out_cap:\n" ++
    "  beqz t3, .L" ++ tag ++ "_eip4788_stale_fail\n" ++
    "  ld t1, " ++ toString outOffsetOff ++ "(x12); add t1, x13, t1\n" ++
    ".L" ++ tag ++ "_eip4788_stale_out_zero:\n" ++
    "  sb zero, 0(t1); addi t1, t1, 1; addi t3, t3, -1; bnez t3, .L" ++ tag ++ "_eip4788_stale_out_zero\n" ++
    ".L" ++ tag ++ "_eip4788_stale_fail:\n" ++
    "  addi x12, x12, " ++ toString netPopBytes ++ "\n" ++
    "  sd x0, 0(x12); sd x0, 8(x12); sd x0, 16(x12); sd x0, 24(x12)\n" ++
    ".L" ++ tag ++ "_eip4788_done:\n" ++
    "  addi x10, x10, 1\n" ++
    dispatchContinueRet ++ "\n" ++
    ".L" ++ tag ++ "_eip4788_fallthrough:\n"
    ) else "") ++
    -- Materialize the route-neutral descriptor and call the one emitted
    -- selector/pricing kernel.  Save the dispatcher ABI because the shared
    -- routine is intentionally free to use caller-saved registers.
    "  addi sp, sp, -32; sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
    "  la t0, precompile_shared_ctx; la t1, " ++ runtimeAccessSeedScratchLabel ++ "; sd t1, 0(t0)\n" ++
    "  ld t1, " ++ toString inOffsetOff ++ "(x12); add t1, x13, t1; sd t1, 8(t0)\n" ++
    "  ld t1, " ++ toString inSizeOff ++ "(x12); sd t1, 16(t0)\n" ++
    "  jal x1, precompile_shared_select_price\n" ++
    "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 32\n" ++
    "  la t0, precompile_shared_selector; ld x14, 0(t0)\n" ++
    "  bnez x14, .L" ++ tag ++ "_supported_precompile\n" ++
    "  j .L" ++ tag ++ "_nonprecompile_fallthrough\n" ++
    ".L" ++ tag ++ "_supported_precompile:\n" ++
    precompileDepthGateAsm (tag ++ "_precompile_depth") netPopBytes ++
    (if sparseWindows then
      -- 0w05f.13 surface 3: with the depth-1+ OUT-window arena bail relaxed
      -- in callMemoryExpansionGasAsm above, re-impose the dense bound for
      -- the PRECOMPILE branch only — precompile outputs are copied raw to
      -- `x13 + outoff` with no sparse write-back, so a beyond-dense out
      -- window keeps today's conservative OOG. The frame-descend
      -- fallthrough (contract callee) is the path served sparsely (the
      -- child RETURN tail write-back). Depth 0 was already root-guarded.
      "  la t0, evm_call_depth\n" ++
      "  ld t0, 0(t0)\n" ++
      "  beqz t0, .L" ++ tag ++ "_preout_ok\n" ++
      "  ld t1, " ++ toString outSizeOff ++ "(x12)\n" ++
      "  beqz t1, .L" ++ tag ++ "_preout_ok\n" ++
      "  ld t2, " ++ toString outOffsetOff ++ "(x12)\n" ++
      "  add t1, t1, t2\n" ++
      "  li t2, " ++ toString runtimeMemoryArenaLimitBytes ++ "\n" ++
      "  bltu t2, t1, .exit_outofgas\n" ++
      ".L" ++ tag ++ "_preout_ok:\n"
     else "") ++
    (match valueOff? with
    | none => ".L" ++ tag ++ "_precompile_dispatch:\n"
    | some valueOff => precompileValueBalanceGateAsm tag netPopBytes valueOff) ++
    successfulPrecompileNewAccountStateGasAsm tag valueOff? ++
    -- Shape/formula overflow is checked after the shared depth, value, and
    -- new-account gates, preserving the child route's exceptional-halt order.
    precompileSharedStatusFailAsm (".L" ++ tag ++ "_bn254_fail_allot") ++
    -- #11163 item 2: thin wrapper — charge allotment, shared execute core,
    -- frame→OUT copy, success push. No dual selector tree.
    precompileSharedLoadCostAsm "x16" ++
    bn254ChargeGateAsm tag ++
    "  addi sp, sp, -32; sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
    "  jal x1, precompile_shared_execute\n" ++
    "  mv x16, a0\n" ++
    "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 32\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    precompileCopyFrameReturndataToOutAsm tag outOffsetOff outSizeOff ++
    ".L" ++ tag ++ "_precompile_success:\n" ++
    refundSuccessfulPrecompileValueStipendAsm tag valueOff? ++
    recordSuccessfulPrecompileValueEffectsAsm tag valueOff? ++
    emitSuccessfulPrecompileValueLogAsm tag valueOff? ++
    "  addi x12, x12, " ++ toString netPopBytes ++ "\n" ++
    "  li x14, 1\n" ++
    "  sd x14, 0(x12)\n" ++
    "  sd x0, 8(x12)\n" ++
    "  sd x0, 16(x12)\n" ++
    "  sd x0, 24(x12)\n" ++
    "  addi x10, x10, 1\n" ++
    dispatchContinueRet ++ "\n" ++
    bn254FailureStubAsm tag netPopBytes ++
    ".L" ++ tag ++ "_nonprecompile_fallthrough:\n" ++
    "1:\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    fallThroughAsm

end EvmAsm.Codegen
