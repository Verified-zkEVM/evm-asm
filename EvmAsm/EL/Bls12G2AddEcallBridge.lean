/-
  EvmAsm.EL.Bls12G2AddEcallBridge

  Pure zkVM BLS12-381 G2 addition accelerator ECALL surface.
-/

module

public import EvmAsm.EL.Bls12G2AddInputBridge
public import EvmAsm.EL.Bls12G2AddResultBridge
public import EvmAsm.Evm64.Accelerators.Status
public import EvmAsm.Evm64.Accelerators.SyscallIds

@[expose] public section

namespace EvmAsm.EL

namespace Bls12G2AddEcallBridge

abbrev Rv64Word := BitVec 64
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

/-- Selector reserved for the BLS12-381 G2 add accelerator ECALL surface. -/
def bls12G2AddSelector : Rv64Word := EvmAsm.Rv64.SyscallIdWord.bls12_g2_add

/-- ECALL request passed to the zkVM BLS12-381 G2 add accelerator. -/
structure Bls12G2AddRequest where
  selector : Rv64Word
  input : Bls12G2AddInputBridge.AcceleratorInput

/-- ECALL result returned by the zkVM BLS12-381 G2 add accelerator. -/
structure Bls12G2AddResult where
  status : ZkvmStatus
  output : Bls12G2AddResultBridge.AcceleratorOutput

/-- Build the BLS12-381 G2 add accelerator request from already-loaded input points. -/
def requestFromInput
    (input : Bls12G2AddInputBridge.AcceleratorInput) : Bls12G2AddRequest :=
  { selector := bls12G2AddSelector, input := input }

/-- Project the output point exposed by a successful BLS12-381 G2 add result. -/
def outputPointFromResult (result : Bls12G2AddResult) :
    Bls12G2AddInputBridge.G2PointBytes :=
  result.output.point

/--
Pure execution boundary for the BLS12-381 G2 add ECALL. The curve operation
itself is supplied by the accelerator model; this bridge fixes the
request/result shape, selector, status code, and output buffer.
-/
def executeBls12G2AddEcall
    (accelerator : Bls12G2AddInputBridge.AcceleratorInput →
      Bls12G2AddResultBridge.AcceleratorResult)
    (request : Bls12G2AddRequest) : Bls12G2AddResult :=
  let result := accelerator request.input
  { status := result.status, output := result.output }

theorem requestFromInput_selector
    (input : Bls12G2AddInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = bls12G2AddSelector := rfl

theorem requestFromInput_input
    (input : Bls12G2AddInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl

theorem executeBls12G2AddEcall_status
    (accelerator : Bls12G2AddInputBridge.AcceleratorInput →
      Bls12G2AddResultBridge.AcceleratorResult)
    (request : Bls12G2AddRequest) :
    (executeBls12G2AddEcall accelerator request).status =
      (accelerator request.input).status := rfl

theorem executeBls12G2AddEcall_output
    (accelerator : Bls12G2AddInputBridge.AcceleratorInput →
      Bls12G2AddResultBridge.AcceleratorResult)
    (request : Bls12G2AddRequest) :
    (executeBls12G2AddEcall accelerator request).output =
      (accelerator request.input).output := rfl

theorem executeBls12G2AddEcall_outputPoint
    (accelerator : Bls12G2AddInputBridge.AcceleratorInput →
      Bls12G2AddResultBridge.AcceleratorResult)
    (request : Bls12G2AddRequest) :
    outputPointFromResult (executeBls12G2AddEcall accelerator request) =
      (accelerator request.input).output.point := rfl

theorem executeBls12G2AddEcall_fromMemory_outputPoint
    (accelerator : Bls12G2AddInputBridge.AcceleratorInput →
      Bls12G2AddResultBridge.AcceleratorResult)
    (memory : Bls12G2AddInputBridge.MemoryReader)
    (p1Start p2Start : Nat) :
    outputPointFromResult
        (executeBls12G2AddEcall accelerator
          (requestFromInput
            (Bls12G2AddInputBridge.bls12G2AddInputFromMemory
              memory p1Start p2Start))) =
      (accelerator
        (Bls12G2AddInputBridge.bls12G2AddInputFromMemory
          memory p1Start p2Start)).output.point := rfl

/-- RV64 `a0` return-register `Word` for the accelerator status, mirroring
`Sha256EcallBridge.statusWord`. The accelerator places the `zkvm_status`
return code in `a0` after the ECALL; this projection extracts that word from
a `Bls12G2AddResult` for postcondition reasoning. -/
def statusWord (result : Bls12G2AddResult) : BitVec 64 :=
  EvmAsm.Rv64.zkvmStatusToWord result.status

theorem statusWord_eok
    {result : Bls12G2AddResult} (h_status : result.status = .eok) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEokWord := by
  show EvmAsm.Rv64.zkvmStatusToWord result.status = _
  rw [h_status]; rfl

theorem statusWord_efail
    {result : Bls12G2AddResult} (h_status : result.status = .efail) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEfailWord := by
  show EvmAsm.Rv64.zkvmStatusToWord result.status = _
  rw [h_status]; rfl

/-- The `a0` word is `ZKVM_EOK` iff the accelerator reported success. -/
theorem statusWord_eq_eokWord_iff (result : Bls12G2AddResult) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEokWord ↔ result.status = .eok := by
  cases h_st : result.status with
  | eok => simp [statusWord_eok h_st]
  | efail =>
    rw [statusWord_efail h_st]
    constructor
    · intro h; exact absurd h.symm EvmAsm.Rv64.zkvmStatusEokWord_ne_efailWord
    · intro h; simp at h

/-- The `a0` word decodes back to the original status. -/
theorem zkvmStatusFromWord?_statusWord (result : Bls12G2AddResult) :
    EvmAsm.Rv64.zkvmStatusFromWord? (statusWord result) = some result.status :=
  EvmAsm.Rv64.zkvmStatusFromWord?_toWord result.status

/-- Push `statusWord` through `executeBls12G2AddEcall`: the returned `a0` word is
the accelerator-supplied status encoded via `zkvmStatusToWord`. This bridge
uses the `AcceleratorResult` struct shape (status as a named field), so the
push-through reads `(accelerator request.input).status`. -/
theorem executeBls12G2AddEcall_statusWord
    (accelerator : Bls12G2AddInputBridge.AcceleratorInput →
      Bls12G2AddResultBridge.AcceleratorResult)
    (request : Bls12G2AddRequest) :
    statusWord (executeBls12G2AddEcall accelerator request) =
      EvmAsm.Rv64.zkvmStatusToWord (accelerator request.input).status := by
  rfl

end Bls12G2AddEcallBridge

end EvmAsm.EL
