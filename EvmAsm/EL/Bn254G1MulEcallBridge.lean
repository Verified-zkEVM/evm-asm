/-
  EvmAsm.EL.Bn254G1MulEcallBridge

  Pure zkVM BN254 G1 scalar-multiplication accelerator ECALL surface.
-/

module

public import EvmAsm.EL.Bn254G1MulInputBridge
public import EvmAsm.EL.Bn254G1MulResultBridge
public import EvmAsm.Evm64.Accelerators.Status
public import EvmAsm.Evm64.Accelerators.SyscallIds

@[expose] public section

namespace EvmAsm.EL

namespace Bn254G1MulEcallBridge

abbrev Rv64Word := BitVec 64
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

/-- Selector reserved for the BN254 G1 mul accelerator ECALL surface. -/
def bn254G1MulSelector : Rv64Word := EvmAsm.Rv64.SyscallIdWord.bn254_g1_mul

/-- ECALL request passed to the zkVM BN254 G1 mul accelerator. -/
structure Bn254G1MulRequest where
  selector : Rv64Word
  input : Bn254G1MulInputBridge.AcceleratorInput

/-- ECALL result returned by the zkVM BN254 G1 mul accelerator. -/
structure Bn254G1MulResult where
  status : ZkvmStatus
  output : Bn254G1MulResultBridge.AcceleratorOutput

/-- Build the BN254 G1 mul accelerator request from already-loaded input bytes. -/
def requestFromInput
    (input : Bn254G1MulInputBridge.AcceleratorInput) : Bn254G1MulRequest :=
  { selector := bn254G1MulSelector, input := input }

/-- Project the output point exposed by a successful BN254 G1 mul result. -/
def outputPointFromResult (result : Bn254G1MulResult) :
    Bn254G1MulInputBridge.G1PointBytes :=
  result.output.point

/--
Pure execution boundary for the BN254 G1 mul ECALL. The curve operation itself
is supplied by the accelerator model; this bridge fixes the request/result
shape, selector, status code, and output buffer.
-/
def executeBn254G1MulEcall
    (accelerator : Bn254G1MulInputBridge.AcceleratorInput →
      Bn254G1MulResultBridge.AcceleratorResult)
    (request : Bn254G1MulRequest) : Bn254G1MulResult :=
  let result := accelerator request.input
  { status := result.status, output := result.output }

theorem requestFromInput_selector
    (input : Bn254G1MulInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = bn254G1MulSelector := rfl

theorem requestFromInput_input
    (input : Bn254G1MulInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl

theorem executeBn254G1MulEcall_status
    (accelerator : Bn254G1MulInputBridge.AcceleratorInput →
      Bn254G1MulResultBridge.AcceleratorResult)
    (request : Bn254G1MulRequest) :
    (executeBn254G1MulEcall accelerator request).status =
      (accelerator request.input).status := rfl

theorem executeBn254G1MulEcall_output
    (accelerator : Bn254G1MulInputBridge.AcceleratorInput →
      Bn254G1MulResultBridge.AcceleratorResult)
    (request : Bn254G1MulRequest) :
    (executeBn254G1MulEcall accelerator request).output =
      (accelerator request.input).output := rfl

theorem executeBn254G1MulEcall_outputPoint
    (accelerator : Bn254G1MulInputBridge.AcceleratorInput →
      Bn254G1MulResultBridge.AcceleratorResult)
    (request : Bn254G1MulRequest) :
    outputPointFromResult (executeBn254G1MulEcall accelerator request) =
      (accelerator request.input).output.point := rfl

theorem executeBn254G1MulEcall_fromMemory_outputPoint
    (accelerator : Bn254G1MulInputBridge.AcceleratorInput →
      Bn254G1MulResultBridge.AcceleratorResult)
    (memory : Bn254G1MulInputBridge.MemoryReader)
    (pointStart scalarStart : Nat) :
    outputPointFromResult
        (executeBn254G1MulEcall accelerator
          (requestFromInput
            (Bn254G1MulInputBridge.bn254G1MulInputFromMemory
              memory pointStart scalarStart))) =
      (accelerator
        (Bn254G1MulInputBridge.bn254G1MulInputFromMemory
          memory pointStart scalarStart)).output.point := rfl

/-- RV64 `a0` return-register `Word` for the accelerator status, mirroring
`Sha256EcallBridge.statusWord`. The accelerator places the `zkvm_status`
return code in `a0` after the ECALL; this projection extracts that word from
a `Bn254G1MulResult` for postcondition reasoning. -/
def statusWord (result : Bn254G1MulResult) : BitVec 64 :=
  EvmAsm.Rv64.zkvmStatusToWord result.status

theorem statusWord_eok
    {result : Bn254G1MulResult} (h_status : result.status = .eok) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEokWord := by
  show EvmAsm.Rv64.zkvmStatusToWord result.status = _
  rw [h_status]; rfl

theorem statusWord_efail
    {result : Bn254G1MulResult} (h_status : result.status = .efail) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEfailWord := by
  show EvmAsm.Rv64.zkvmStatusToWord result.status = _
  rw [h_status]; rfl

/-- The `a0` word is `ZKVM_EOK` iff the accelerator reported success. -/
theorem statusWord_eq_eokWord_iff (result : Bn254G1MulResult) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEokWord ↔ result.status = .eok := by
  cases h_st : result.status with
  | eok => simp [statusWord_eok h_st]
  | efail =>
    rw [statusWord_efail h_st]
    constructor
    · intro h; exact absurd h.symm EvmAsm.Rv64.zkvmStatusEokWord_ne_efailWord
    · intro h; simp at h

/-- The `a0` word decodes back to the original status. -/
theorem zkvmStatusFromWord?_statusWord (result : Bn254G1MulResult) :
    EvmAsm.Rv64.zkvmStatusFromWord? (statusWord result) = some result.status :=
  EvmAsm.Rv64.zkvmStatusFromWord?_toWord result.status

/-- Push `statusWord` through `executeBn254G1MulEcall`: the returned `a0` word is
the accelerator-supplied status encoded via `zkvmStatusToWord`. -/
theorem executeBn254G1MulEcall_statusWord
    (accelerator : Bn254G1MulInputBridge.AcceleratorInput →
      Bn254G1MulResultBridge.AcceleratorResult)
    (request : Bn254G1MulRequest) :
    statusWord (executeBn254G1MulEcall accelerator request) =
      EvmAsm.Rv64.zkvmStatusToWord (accelerator request.input).status := by
  rfl

end Bn254G1MulEcallBridge

end EvmAsm.EL
