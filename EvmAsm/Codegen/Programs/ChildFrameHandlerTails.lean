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
