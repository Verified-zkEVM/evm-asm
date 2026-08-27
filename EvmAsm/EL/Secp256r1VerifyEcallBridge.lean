/-
  EvmAsm.EL.Secp256r1VerifyEcallBridge

  Pure zkVM secp256r1 signature-verification accelerator ECALL surface.
-/

module

public import EvmAsm.EL.Secp256r1VerifyInputBridge
public import EvmAsm.EL.Secp256r1VerifyResultBridge
public import EvmAsm.Evm64.Accelerators.SyscallIds

@[expose] public section

namespace EvmAsm.EL

namespace Secp256r1VerifyEcallBridge

abbrev Rv64Word := BitVec 64
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

/-- Selector reserved for the secp256r1 verify accelerator ECALL surface. -/
def secp256r1VerifySelector : Rv64Word := EvmAsm.Rv64.SyscallIdWord.secp256r1_verify

/-- ECALL request passed to the zkVM secp256r1 verify accelerator. -/
structure Secp256r1VerifyRequest where
  selector : Rv64Word
  input : Secp256r1VerifyInputBridge.AcceleratorInput

/-- ECALL result returned by the zkVM secp256r1 verify accelerator. -/
structure Secp256r1VerifyResult where
  status : ZkvmStatus
  output : Secp256r1VerifyResultBridge.AcceleratorOutput

/-- Build the secp256r1 verify request from already-loaded input. -/
def requestFromInput
    (input : Secp256r1VerifyInputBridge.AcceleratorInput) :
    Secp256r1VerifyRequest :=
  { selector := secp256r1VerifySelector, input := input }

/-- Stack/precompile success word exposed by a successful secp256r1 verify result. -/
def successWordFromResult (result : Secp256r1VerifyResult) : BitVec 256 :=
  Secp256r1VerifyResultBridge.successWordFromVerified result.output.verified

/--
Pure execution boundary for the secp256r1 verify ECALL. The signature
verification itself is supplied by the accelerator model; this bridge fixes
the request/result shape, selector, status code, and verified flag.
-/
def executeSecp256r1VerifyEcall
    (accelerator : Secp256r1VerifyInputBridge.AcceleratorInput →
      Secp256r1VerifyResultBridge.AcceleratorResult)
    (request : Secp256r1VerifyRequest) : Secp256r1VerifyResult :=
  let result := accelerator request.input
  { status := result.status, output := result.output }

theorem requestFromInput_selector
    (input : Secp256r1VerifyInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = secp256r1VerifySelector := rfl

theorem requestFromInput_input
    (input : Secp256r1VerifyInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl

theorem executeSecp256r1VerifyEcall_status
    (accelerator : Secp256r1VerifyInputBridge.AcceleratorInput →
      Secp256r1VerifyResultBridge.AcceleratorResult)
    (request : Secp256r1VerifyRequest) :
    (executeSecp256r1VerifyEcall accelerator request).status =
      (accelerator request.input).status := rfl

theorem executeSecp256r1VerifyEcall_output
    (accelerator : Secp256r1VerifyInputBridge.AcceleratorInput →
      Secp256r1VerifyResultBridge.AcceleratorResult)
    (request : Secp256r1VerifyRequest) :
    (executeSecp256r1VerifyEcall accelerator request).output =
      (accelerator request.input).output := rfl

theorem executeSecp256r1VerifyEcall_successWord
    (accelerator : Secp256r1VerifyInputBridge.AcceleratorInput →
      Secp256r1VerifyResultBridge.AcceleratorResult)
    (request : Secp256r1VerifyRequest) :
    successWordFromResult (executeSecp256r1VerifyEcall accelerator request) =
      Secp256r1VerifyResultBridge.successWordFromVerified
        (accelerator request.input).output.verified := rfl

theorem executeSecp256r1VerifyEcall_fromMemory_successWord
    (accelerator : Secp256r1VerifyInputBridge.AcceleratorInput →
      Secp256r1VerifyResultBridge.AcceleratorResult)
    (memory : Secp256r1VerifyInputBridge.MemoryReader)
    (msgStart sigStart pubkeyStart : Nat) :
    successWordFromResult
        (executeSecp256r1VerifyEcall accelerator
          (requestFromInput
            (Secp256r1VerifyInputBridge.secp256r1VerifyInputFromMemory
              memory msgStart sigStart pubkeyStart))) =
      Secp256r1VerifyResultBridge.successWordFromVerified
        (accelerator
          (Secp256r1VerifyInputBridge.secp256r1VerifyInputFromMemory
            memory msgStart sigStart pubkeyStart)).output.verified := rfl

end Secp256r1VerifyEcallBridge

end EvmAsm.EL
