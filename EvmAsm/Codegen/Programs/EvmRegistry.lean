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
  pushHandlers ++ dupHandlers ++ swapHandlers ++ singletonHandlers ++
  memoryHandlers ++ memoryMetadataHandlers ++ gasHandlers ++ envHandlers ++ slotnumContextHandlers ++
  blobContextHandlers ++ blockHashHandlers ++ calldataHandlers ++ codeHandlers ++
  controlFlowHandlers ++ hashHandlers ++ logHandlers ++
  balanceWitnessHandlers ++ accountWitnessHandlers ++ extcodecopyWitnessHandlers ++ storageHandlers ++
  mcopyHandlers ++ haltHandlers ++ pushZeroHandlers ++ returnDataHandlers ++
  popPushZeroHandlers ++ copyNoopHandlers ++ childFrameHandlers ++
  arithNoopHandlers ++ mulmodHandlers ++ divModHandlers ++ signedDivModHandlers ++
  selfCallingHandlers ++ [stopHandler]

end EvmAsm.Codegen
