/-
  EvmAsm.Codegen.Programs.EvmRegistry

  Runtime dispatcher opcode registry.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmStackHandlers
import EvmAsm.Codegen.Programs.EvmSingletonHandlers
import EvmAsm.Codegen.Programs.EvmMemoryHandlers
import EvmAsm.Codegen.Programs.EvmGasHandlers
import EvmAsm.Codegen.Programs.EvmCodeHandlers
import EvmAsm.Codegen.Programs.EvmEnvHandlers
import EvmAsm.Codegen.Programs.EvmSlotnumHandlers
import EvmAsm.Codegen.Programs.EvmBlobContextHandlers
import EvmAsm.Codegen.Programs.EvmBlockHashHandlers
import EvmAsm.Codegen.Programs.EvmCalldataHandlers
import EvmAsm.Codegen.Programs.EvmMcopyHandlers
import EvmAsm.Codegen.Programs.EvmControlFlowHandlers
import EvmAsm.Codegen.Programs.EvmHashHandlers
import EvmAsm.Codegen.Programs.EvmLogHandlers
import EvmAsm.Codegen.Programs.EvmMulmodHandler
import EvmAsm.Codegen.Programs.EvmDivModHandlers
import EvmAsm.Codegen.Programs.EvmSignedDivModHandlers
import EvmAsm.Codegen.Programs.EvmSelfCallingHandlers
import EvmAsm.Codegen.Programs.EvmBalance
import EvmAsm.Codegen.Programs.Noop
import EvmAsm.Codegen.Programs.EvmAccountWitness
import EvmAsm.Codegen.Programs.EvmExtcodecopy
import EvmAsm.Codegen.Programs.Storage

namespace EvmAsm.Codegen

/-! ## tiny_interp_dispatch — M5b runtime fetch/decode/dispatch loop

    Same EVM bytecodes as M5a, but routed through an actual RISC-V
    dispatch loop. The dispatcher scaffolding (loop body, 256-entry
    jump table, `h_invalid` fallback, `.exit_label`) lives in
    `EvmAsm.Codegen.Dispatch`; this module declares only the opcode
    handler registry.

    All other opcode bytes fall to `h_invalid` (emitted automatically
    by `emitDispatcherEpilogue`), which takes the same exit path as
    STOP. -/

/-- STOP transitions out of the dispatcher loop instead of returning to it. -/
def stopHandler : OpcodeHandlerSpec :=
  { label   := "h_STOP"
    opcodes := [0x00]
    body    := []
    tail    := .custom (dispatchHaltRet 1) }

/-- M5b dispatch registry. Order doesn't affect correctness; the 256-entry
    jump table is built by `jumpTargetLabel`, which scans the list for a
    spec whose `opcodes` contains the byte. -/
def tinyInterpRegistry : List OpcodeHandlerSpec :=
  pushHandlers ++ dupHandlers ++ swapHandlers ++ eip8024StackHandlers ++ singletonHandlers ++
  memoryHandlers ++ memoryMetadataHandlers ++ gasHandlers ++ envHandlers ++ slotnumContextHandlers ++
  blobContextHandlers ++ blockHashHandlers ++ calldataHandlers ++ codeHandlers ++
  controlFlowHandlers ++ hashHandlers ++ logHandlers ++
  balanceWitnessHandlers ++ accountWitnessHandlers ++ extcodecopyWitnessHandlers ++ storageHandlers ++
  mcopyHandlers ++ haltHandlers false ++ pushZeroHandlers ++ returnDataHandlers ++
  popPushZeroHandlers ++ copyNoopHandlers ++
  childFrameHandlers (callPushZeroFallThrough 192) (callPushZeroFallThrough 192)
    (callPushZeroFallThrough 160) (callPushZeroFallThrough 160) ++
  arithNoopHandlers ++ mulmodHandlers ++ divModHandlers ++ signedDivModHandlers ++
  selfCallingHandlers ++ [stopHandler]

/-- Depth-aware STOP for the call-frame guest (.61.6.6). At call depth 0 this is
    byte-identical to `stopHandler` (`beqz → .exit_label`), so the single-frame
    verdict path is unchanged. At depth > 0 (a child frame) it pops one frame via
    `frame_return` (success word 1, no return-data) and resumes the parent's
    dispatch loop instead of halting the guest. Only used by `callFrameGuestRegistry`
    (the guest links `frame_return` / `evm_call_depth`); the standalone dispatch
    probes keep `stopHandler` so they need not link the frame helpers. -/
def stopHandlerCF : OpcodeHandlerSpec :=
  { label   := "h_STOP"
    opcodes := [0x00]
    body    := []
    tail    := .custom (
      "  la t0, evm_call_depth\n" ++
      "  ld t0, 0(t0)\n" ++
      -- 4ch8f.10.3: depth-0 STOP halts via the flag+ret discipline (routes to
      -- .exit_label) instead of jumping there directly; depth>0 continues below.
      "  bnez t0, .Lstop_depth_nonzero\n" ++
      dispatchHaltRet 1 ++ "\n" ++
      ".Lstop_depth_nonzero:\n" ++
      -- drj99.1.7: a STOP in a CREATE child frame deposits an EMPTY deployed code (STOP = RETURN
      -- with no data). Route it through the RETURN handler's create-deposit (record code-effect +
      -- the created account's nonstorage effect + push the derived address), exactly like RETURN
      -- but with offset/size = 0. A non-create (CALL) frame keeps the plain success=1 frame_return.
      -- create_frame_flag[depth] is set by create_frame_descend; clear it on the create path (slot
      -- reuse) to mirror returnRevertTail line .Lrr's clear. x14/x15 set to 0 = empty return data.
      "  la t1, create_frame_flag\n" ++
      "  slli t2, t0, 3\n" ++
      "  add t1, t1, t2\n" ++
      "  ld t3, 0(t1)\n" ++
      "  beqz t3, .Lstop_call_frame\n" ++
      "  sd x0, 0(t1)\n" ++
      -- The shared CREATE deposit body is normally reached from RETURN, whose
      -- depth-aware return tail restores the CREATE metadata for this child
      -- before calling it.  STOP enters that body directly.  Restore the same
      -- depth-indexed metadata here, otherwise a nested CREATE leaves the
      -- inner creator/value/address live and the outer CREATE records its
      -- parent's balance under the inner creator address.
      "  la t1, create_address_by_depth; slli t2, t0, 5; add t1, t1, t2\n" ++
      "  la t2, create_address_be; ld t3, 0(t1); sd t3, 0(t2); ld t3, 8(t1); sd t3, 8(t2); ld t3, 16(t1); sd t3, 16(t2); ld t3, 24(t1); sd t3, 24(t2)\n" ++
      "  la t1, create_sender_by_depth; slli t2, t0, 5; add t1, t1, t2\n" ++
      "  la t2, create_sender_be; ld t3, 0(t1); sd t3, 0(t2); ld t3, 8(t1); sd t3, 8(t2); ld t3, 16(t1); sd t3, 16(t2); ld t3, 24(t1); sd t3, 24(t2)\n" ++
      "  la t1, create_value_by_depth; slli t2, t0, 5; add t1, t1, t2\n" ++
      "  la t2, create_value_be; ld t3, 0(t1); sd t3, 0(t2); ld t3, 8(t1); sd t3, 8(t2); ld t3, 16(t1); sd t3, 16(t2); ld t3, 24(t1); sd t3, 24(t2)\n" ++
      "  la t1, create_nonce_by_depth; slli t2, t0, 3; add t1, t1, t2\n" ++
      "  la t2, create_nonce; ld t3, 0(t1); sd t3, 0(t2)\n" ++
      "  la t1, create_pre_bal_by_depth; slli t2, t0, 5; add t1, t1, t2\n" ++
      "  la t2, nse_create_pre_bal; ld t3, 0(t1); sd t3, 0(t2); ld t3, 8(t1); sd t3, 8(t2); ld t3, 16(t1); sd t3, 16(t2); ld t3, 24(t1); sd t3, 24(t2)\n" ++
      "  li x14, 0\n" ++
      "  li x15, 0\n" ++
      "  j .Lcreate_deposit_from_halt_1\n" ++
      ".Lstop_call_frame:\n" ++

      "  li a0, 1\n" ++
      "  li a1, 0\n" ++
      "  li a2, 0\n" ++
      "  jal ra, frame_return\n" ++
      dispatchContinueRet) }

/-- Registry for the call-frame round-trip probe: depth-aware STOP (so a child
    frame returns to its parent) but the push-0 CALL fall-through, so the emitted
    CALL handler does NOT pull in the `code_at_header_state_root` dependency tree.
    The probe descends manually via `call_frame_descend` with a fixed child-code
    blob, so it never needs the CALL-handler code resolution. -/
def callFrameProbeRegistry : List OpcodeHandlerSpec :=
  pushHandlers ++ dupHandlers ++ swapHandlers ++ eip8024StackHandlers ++ singletonHandlers ++
  memoryHandlers ++ memoryMetadataHandlers ++ gasHandlers ++ envHandlers ++ slotnumContextHandlers ++
  blobContextHandlers ++ blockHashHandlers ++ calldataHandlers ++ codeHandlers ++
  controlFlowHandlers ++ hashHandlers ++ logHandlers ++
  balanceWitnessHandlers ++ accountWitnessHandlers ++ extcodecopyWitnessHandlers ++ storageHandlers ++
  mcopyHandlers ++ haltHandlers true ++ pushZeroHandlers ++ returnDataHandlers ++
  popPushZeroHandlers ++ copyNoopHandlers ++
  childFrameHandlers (callPushZeroFallThrough 192) (callPushZeroFallThrough 192)
    (callPushZeroFallThrough 160) (callPushZeroFallThrough 160) ++
  arithNoopHandlers ++ mulmodHandlers ++ divModHandlers ++ signedDivModHandlers ++
  selfCallingHandlers ++ [stopHandlerCF]

/-- The dispatch registry used by the stateless guest's embedded EVM dispatcher.
    Identical to `tinyInterpRegistry` except STOP is depth-aware (`stopHandlerCF`),
    so child frames return to the parent instead of halting. Same opcodes/labels as
    `tinyInterpRegistry` (only the STOP body differs), so the jump table and the
    `RegistryInvariants` structural facts are unaffected. The standalone dispatch
    probes keep `tinyInterpRegistry`. -/
def callFrameGuestRegistry : List OpcodeHandlerSpec :=
  pushHandlers ++ dupHandlers ++ swapHandlers ++ eip8024StackHandlers ++ singletonHandlers ++
  memoryHandlers ++ memoryMetadataHandlers ++ gasHandlers ++ envHandlers ++ slotnumContextHandlers ++
  blobContextHandlers ++ blockHashHandlers ++ calldataHandlers ++ codeHandlers ++
  controlFlowHandlers ++ hashHandlers ++ logHandlers ++
  balanceWitnessHandlers ++ accountWitnessHandlers ++ extcodecopyWitnessHandlers ++ storageHandlers ++
  -- sparseWindows = true (evm-asm-0w05f.13): depth-1+ CALL-frame RETURN/REVERT
  -- windows beyond the dense arena are charged-only + materialized from the
  -- sparse word store (`sparse_window_read`, linked via the runtime
  -- dispatcher's embedded helpers). The roundtrip probe registry above keeps
  -- the dense arena bail (no sparse cells in its data section).
  mcopyHandlers ++ haltHandlers true true ++ pushZeroHandlers ++ returnDataHandlers ++
  popPushZeroHandlers ++ copyNoopHandlers ++
  childFrameHandlers
    (callDescendFallThrough "call_target" 192 64 96 128 160 192 0)
    (callDescendFallThrough "callcode_target" 192 64 96 128 160 192 2)
    (callDescendFallThrough "delegatecall_target" 160 0 64 96 128 160 3)
    (callDescendFallThrough "staticcall_target" 160 0 64 96 128 160 1)
    (sparseWindows := true) ++
  arithNoopHandlers ++ mulmodHandlers ++ divModHandlers ++ signedDivModHandlers ++
  selfCallingHandlers ++ [stopHandlerCF]

end EvmAsm.Codegen
