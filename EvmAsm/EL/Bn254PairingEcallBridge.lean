/-
  EvmAsm.EL.Bn254PairingEcallBridge

  Pure zkVM BN254 pairing accelerator ECALL surface.
-/

module

public import EvmAsm.EL.Bn254PairingInputBridge
public import EvmAsm.EL.Bn254PairingResultBridge
public import EvmAsm.Evm64.Accelerators.SyscallIds

@[expose] public section

namespace EvmAsm.EL

namespace Bn254PairingEcallBridge

abbrev Rv64Word := BitVec 64
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

/-- Selector reserved for the BN254 pairing accelerator ECALL surface. -/
def bn254PairingSelector : Rv64Word := EvmAsm.Rv64.SyscallIdWord.bn254_pairing

/-- ECALL request passed to the zkVM BN254 pairing accelerator. -/
structure Bn254PairingRequest where
  selector : Rv64Word
  input : Bn254PairingInputBridge.AcceleratorInput

/-- ECALL result returned by the zkVM BN254 pairing accelerator. -/
structure Bn254PairingResult where
  status : ZkvmStatus
  output : Bn254PairingResultBridge.AcceleratorOutput

/-- Build the BN254 pairing accelerator request from already-loaded input pairs. -/
def requestFromInput
    (input : Bn254PairingInputBridge.AcceleratorInput) : Bn254PairingRequest :=
  { selector := bn254PairingSelector, input := input }

/-- Stack/precompile success word exposed by a successful BN254 pairing result. -/
def successWordFromResult (result : Bn254PairingResult) : BitVec 256 :=
  Bn254PairingResultBridge.successWordFromVerified result.output.verified

/--
Pure execution boundary for the BN254 pairing ECALL. The pairing check itself
is supplied by the accelerator model; this bridge fixes the request/result
shape, selector, status code, and verified flag.
-/
def executeBn254PairingEcall
    (accelerator : Bn254PairingInputBridge.AcceleratorInput →
      Bn254PairingResultBridge.AcceleratorResult)
    (request : Bn254PairingRequest) : Bn254PairingResult :=
  let result := accelerator request.input
  { status := result.status, output := result.output }

theorem requestFromInput_selector
    (input : Bn254PairingInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = bn254PairingSelector := rfl

theorem requestFromInput_input
    (input : Bn254PairingInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl

theorem executeBn254PairingEcall_status
    (accelerator : Bn254PairingInputBridge.AcceleratorInput →
      Bn254PairingResultBridge.AcceleratorResult)
    (request : Bn254PairingRequest) :
    (executeBn254PairingEcall accelerator request).status =
      (accelerator request.input).status := rfl

theorem executeBn254PairingEcall_output
    (accelerator : Bn254PairingInputBridge.AcceleratorInput →
      Bn254PairingResultBridge.AcceleratorResult)
    (request : Bn254PairingRequest) :
    (executeBn254PairingEcall accelerator request).output =
      (accelerator request.input).output := rfl

theorem executeBn254PairingEcall_successWord
    (accelerator : Bn254PairingInputBridge.AcceleratorInput →
      Bn254PairingResultBridge.AcceleratorResult)
    (request : Bn254PairingRequest) :
    successWordFromResult (executeBn254PairingEcall accelerator request) =
      Bn254PairingResultBridge.successWordFromVerified
        (accelerator request.input).output.verified := rfl

theorem executeBn254PairingEcall_fromMemory_successWord
    (accelerator : Bn254PairingInputBridge.AcceleratorInput →
      Bn254PairingResultBridge.AcceleratorResult)
    (memory : Bn254PairingInputBridge.MemoryReader)
    (pairsStart numPairs : Nat) :
    successWordFromResult
        (executeBn254PairingEcall accelerator
          (requestFromInput
            (Bn254PairingInputBridge.bn254PairingInputFromMemory
              memory pairsStart numPairs))) =
      Bn254PairingResultBridge.successWordFromVerified
        (accelerator
          (Bn254PairingInputBridge.bn254PairingInputFromMemory
            memory pairsStart numPairs)).output.verified := rfl

end Bn254PairingEcallBridge

end EvmAsm.EL
