/-
  EvmAsm.EL.Bls12PairingEcallBridge

  Pure zkVM BLS12-381 pairing accelerator ECALL surface.
-/

module

public import EvmAsm.EL.Bls12PairingInputBridge
public import EvmAsm.EL.Bls12PairingResultBridge
public import EvmAsm.Evm64.Accelerators.SyscallIds

@[expose] public section

namespace EvmAsm.EL

namespace Bls12PairingEcallBridge

abbrev Rv64Word := BitVec 64
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

/-- Selector reserved for the BLS12-381 pairing accelerator ECALL surface. -/
def bls12PairingSelector : Rv64Word := EvmAsm.Rv64.SyscallIdWord.bls12_pairing

/-- ECALL request passed to the zkVM BLS12-381 pairing accelerator. -/
structure Bls12PairingRequest where
  selector : Rv64Word
  input : Bls12PairingInputBridge.AcceleratorInput

/-- ECALL result returned by the zkVM BLS12-381 pairing accelerator. -/
structure Bls12PairingResult where
  status : ZkvmStatus
  output : Bls12PairingResultBridge.AcceleratorOutput

/-- Build the BLS12-381 pairing accelerator request from already-loaded input pairs. -/
def requestFromInput
    (input : Bls12PairingInputBridge.AcceleratorInput) : Bls12PairingRequest :=
  { selector := bls12PairingSelector, input := input }

/-- Stack/precompile success word exposed by a successful BLS12-381 pairing result. -/
def successWordFromResult (result : Bls12PairingResult) : BitVec 256 :=
  Bls12PairingResultBridge.successWordFromVerified result.output.verified

/--
Pure execution boundary for the BLS12-381 pairing ECALL. The pairing check
itself is supplied by the accelerator model; this bridge fixes the
request/result shape, selector, status code, and verified flag.
-/
def executeBls12PairingEcall
    (accelerator : Bls12PairingInputBridge.AcceleratorInput →
      Bls12PairingResultBridge.AcceleratorResult)
    (request : Bls12PairingRequest) : Bls12PairingResult :=
  let result := accelerator request.input
  { status := result.status, output := result.output }

theorem requestFromInput_selector
    (input : Bls12PairingInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = bls12PairingSelector := rfl

theorem requestFromInput_input
    (input : Bls12PairingInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl

theorem executeBls12PairingEcall_status
    (accelerator : Bls12PairingInputBridge.AcceleratorInput →
      Bls12PairingResultBridge.AcceleratorResult)
    (request : Bls12PairingRequest) :
    (executeBls12PairingEcall accelerator request).status =
      (accelerator request.input).status := rfl

theorem executeBls12PairingEcall_output
    (accelerator : Bls12PairingInputBridge.AcceleratorInput →
      Bls12PairingResultBridge.AcceleratorResult)
    (request : Bls12PairingRequest) :
    (executeBls12PairingEcall accelerator request).output =
      (accelerator request.input).output := rfl

theorem executeBls12PairingEcall_successWord
    (accelerator : Bls12PairingInputBridge.AcceleratorInput →
      Bls12PairingResultBridge.AcceleratorResult)
    (request : Bls12PairingRequest) :
    successWordFromResult (executeBls12PairingEcall accelerator request) =
      Bls12PairingResultBridge.successWordFromVerified
        (accelerator request.input).output.verified := rfl

theorem executeBls12PairingEcall_fromMemory_successWord
    (accelerator : Bls12PairingInputBridge.AcceleratorInput →
      Bls12PairingResultBridge.AcceleratorResult)
    (memory : Bls12PairingInputBridge.MemoryReader)
    (pairsStart numPairs : Nat) :
    successWordFromResult
        (executeBls12PairingEcall accelerator
          (requestFromInput
            (Bls12PairingInputBridge.bls12PairingInputFromMemory
              memory pairsStart numPairs))) =
      Bls12PairingResultBridge.successWordFromVerified
        (accelerator
          (Bls12PairingInputBridge.bls12PairingInputFromMemory
            memory pairsStart numPairs)).output.verified := rfl

end Bls12PairingEcallBridge

end EvmAsm.EL
