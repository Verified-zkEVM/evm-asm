/-
  EvmAsm.EL.ModexpEcallBridge

  Pure zkVM MODEXP accelerator ECALL surface for the Ethereum MODEXP
  precompile (address 0x05 / `zkvm_modexp`).
-/

module

public import EvmAsm.EL.ModexpInputBridge
public import EvmAsm.EL.ModexpResultBridge
public import EvmAsm.Evm64.Accelerators.SyscallIds

@[expose] public section

namespace EvmAsm.EL

namespace ModexpEcallBridge

abbrev Rv64Word := BitVec 64
abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

/-- Selector reserved for the `zkvm_modexp` accelerator ECALL surface. -/
def modexpSelector : Rv64Word := EvmAsm.Rv64.SyscallIdWord.modexp

/-- ECALL request passed to the zkVM MODEXP accelerator. -/
structure ModexpRequest where
  selector : Rv64Word
  input    : ModexpInputBridge.AcceleratorInput
  deriving Repr

/-- ECALL result returned by the zkVM MODEXP accelerator. -/
structure ModexpResult where
  status : ZkvmStatus
  output : ModexpResultBridge.AcceleratorOutput

/-- Build the MODEXP accelerator request from already-loaded input buffers. -/
def requestFromInput
    (input : ModexpInputBridge.AcceleratorInput) : ModexpRequest :=
  { selector := modexpSelector, input := input }

/-- Stack word projected from a successful MODEXP accelerator result. -/
def stackWordFromResult (result : ModexpResult) : EvmWord :=
  ModexpResultBridge.stackWordFromAcceleratorOutput result.output

/--
Pure execution boundary for the MODEXP ECALL. The modular-exponentiation
computation itself is supplied by the accelerator model; this bridge
fixes the request/result shape, the selector, the status return, and the
stack-word projection of the variable-width output buffer.

Distinctive token: ModexpEcallBridge.executeModexpEcall.
-/
def executeModexpEcall
    (accelerator : ModexpInputBridge.AcceleratorInput →
      ModexpResultBridge.AcceleratorResult)
    (request : ModexpRequest) : ModexpResult :=
  let result := accelerator request.input
  { status := result.status, output := result.output }

theorem requestFromInput_selector
    (input : ModexpInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = modexpSelector := rfl

theorem requestFromInput_input
    (input : ModexpInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl

theorem executeModexpEcall_status
    (accelerator : ModexpInputBridge.AcceleratorInput →
      ModexpResultBridge.AcceleratorResult)
    (request : ModexpRequest) :
    (executeModexpEcall accelerator request).status =
      (accelerator request.input).status := rfl

theorem executeModexpEcall_output
    (accelerator : ModexpInputBridge.AcceleratorInput →
      ModexpResultBridge.AcceleratorResult)
    (request : ModexpRequest) :
    (executeModexpEcall accelerator request).output =
      (accelerator request.input).output := rfl

theorem executeModexpEcall_stackWord
    (accelerator : ModexpInputBridge.AcceleratorInput →
      ModexpResultBridge.AcceleratorResult)
    (request : ModexpRequest) :
    stackWordFromResult (executeModexpEcall accelerator request) =
      ModexpResultBridge.stackWordFromAcceleratorOutput
        (accelerator request.input).output := rfl

theorem executeModexpEcall_fromMemory_stackWord
    (accelerator : ModexpInputBridge.AcceleratorInput →
      ModexpResultBridge.AcceleratorResult)
    (memory : ModexpInputBridge.MemoryReader)
    (baseStart baseLen expStart expLen modStart modLen : Nat) :
    stackWordFromResult
        (executeModexpEcall accelerator
          (requestFromInput
            (ModexpInputBridge.acceleratorInputFromMemory
              memory baseStart baseLen expStart expLen modStart modLen))) =
      ModexpResultBridge.stackWordFromAcceleratorOutput
        (accelerator
          (ModexpInputBridge.acceleratorInputFromMemory
            memory baseStart baseLen expStart expLen modStart modLen)).output := rfl

end ModexpEcallBridge

end EvmAsm.EL
