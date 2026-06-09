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
    tail    := .custom "  j .exit_label" }

/-- M5b dispatch registry. Order doesn't affect correctness; the 256-entry
    jump table is built by `jumpTargetLabel`, which scans the list for a
    spec whose `opcodes` contains the byte. -/
def tinyInterpRegistry : List OpcodeHandlerSpec :=
  pushHandlers ++ dupHandlers ++ swapHandlers ++ eip8024StackHandlers ++ singletonHandlers ++
  memoryHandlers ++ memoryMetadataHandlers ++ gasHandlers ++ envHandlers ++ slotnumContextHandlers ++
  blobContextHandlers ++ blockHashHandlers ++ calldataHandlers ++ codeHandlers ++
  controlFlowHandlers ++ hashHandlers ++ logHandlers ++
  balanceWitnessHandlers ++ accountWitnessHandlers ++ extcodecopyWitnessHandlers ++ storageHandlers ++
  mcopyHandlers ++ haltHandlers ++ pushZeroHandlers ++ returnDataHandlers ++
  popPushZeroHandlers ++ copyNoopHandlers ++
  childFrameHandlers (callPushZeroFallThrough 192) (callPushZeroFallThrough 160) ++
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
      "  beqz t0, .exit_label\n" ++
      "  li a0, 1\n" ++
      "  li a1, 0\n" ++
      "  li a2, 0\n" ++
      "  jal ra, frame_return\n" ++
      "  j .dispatch_loop") }

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
  mcopyHandlers ++ haltHandlers ++ pushZeroHandlers ++ returnDataHandlers ++
  popPushZeroHandlers ++ copyNoopHandlers ++
  childFrameHandlers
    (callDescendFallThrough "call_target" 192 64 96 128 160 192 false)
    (callDescendFallThrough "staticcall_target" 160 0 64 96 128 160 true) ++
  arithNoopHandlers ++ mulmodHandlers ++ divModHandlers ++ signedDivModHandlers ++
  selfCallingHandlers ++ [stopHandlerCF]

end EvmAsm.Codegen
