/-
  EvmAsm.EL.Bn254G1AddEcallBridge

  Pure zkVM `zkvm_bn254_g1_add` accelerator ECALL surface. Mirrors the
  SHA256/RIPEMD160/Secp256k1 ECALL bridge skeletons: fixes the request and
  result shapes, the selector binding (via `SyscallIdWord.bn254_g1_add`), and
  exposes a pure execution boundary `executeBn254G1AddEcall` parameterised by
  an accelerator model.
-/

module

public import EvmAsm.EL.Bn254G1AddInputBridge
public import EvmAsm.EL.Bn254G1AddResultBridge
public import EvmAsm.Evm64.Accelerators.Status
public import EvmAsm.Evm64.Accelerators.SyscallIds

@[expose] public section

namespace EvmAsm.EL

namespace Bn254G1AddEcallBridge

/-- Selector reserved for the `zkvm_bn254_g1_add` accelerator ECALL. -/
def bn254G1AddSelector : BitVec 64 :=
  EvmAsm.Rv64.SyscallIdWord.bn254_g1_add

/-- ECALL request passed to the zkVM BN254 G1-add accelerator. -/
structure Bn254G1AddRequest where
  selector : BitVec 64
  input    : Bn254G1AddInputBridge.AcceleratorInput

/-- ECALL result returned by the zkVM BN254 G1-add accelerator. -/
structure Bn254G1AddResult where
  status : EvmAsm.Accelerators.ZkvmStatus
  output : Bn254G1AddResultBridge.AcceleratorOutput

/-- Build the BN254 G1-add accelerator request from already-loaded input. -/
def requestFromInput
    (input : Bn254G1AddInputBridge.AcceleratorInput) : Bn254G1AddRequest :=
  { selector := bn254G1AddSelector, input := input }

/-- Output byte list (length 64) exposed by a BN254 G1-add accelerator result. -/
def outputBytesList (result : Bn254G1AddResult) : List Byte :=
  Bn254G1AddResultBridge.outputBytesList result.output

/--
Pure execution boundary for the BN254 G1-add ECALL. The point-addition itself
is supplied by the accelerator model; this bridge fixes the request/result
shape, the status return, and the output bytes extracted from the returned
buffer.

Distinctive token: Bn254G1AddEcallBridge.executeBn254G1AddEcall.
-/
def executeBn254G1AddEcall
    (accelerator : Bn254G1AddInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Bn254G1AddResultBridge.AcceleratorOutput)
    (request : Bn254G1AddRequest) : Bn254G1AddResult :=
  let result := accelerator request.input
  { status := result.1, output := result.2 }

theorem requestFromInput_selector
    (input : Bn254G1AddInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = bn254G1AddSelector := rfl

theorem requestFromInput_input
    (input : Bn254G1AddInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl

theorem executeBn254G1AddEcall_status
    (accelerator : Bn254G1AddInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Bn254G1AddResultBridge.AcceleratorOutput)
    (request : Bn254G1AddRequest) :
    (executeBn254G1AddEcall accelerator request).status =
      (accelerator request.input).1 := by
  rfl

theorem executeBn254G1AddEcall_output
    (accelerator : Bn254G1AddInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Bn254G1AddResultBridge.AcceleratorOutput)
    (request : Bn254G1AddRequest) :
    (executeBn254G1AddEcall accelerator request).output =
      (accelerator request.input).2 := by
  rfl

theorem executeBn254G1AddEcall_outputBytes
    (accelerator : Bn254G1AddInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Bn254G1AddResultBridge.AcceleratorOutput)
    (request : Bn254G1AddRequest) :
    outputBytesList (executeBn254G1AddEcall accelerator request) =
      Bn254G1AddResultBridge.outputBytesList (accelerator request.input).2 := by
  rfl

theorem executeBn254G1AddEcall_fromMemory_outputBytes
    (accelerator : Bn254G1AddInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Bn254G1AddResultBridge.AcceleratorOutput)
    (memory : Bn254G1AddInputBridge.MemoryReader)
    (p1Start p2Start : Nat) :
    outputBytesList
        (executeBn254G1AddEcall accelerator
          (requestFromInput
            (Bn254G1AddInputBridge.bn254G1AddInputFromMemory
              memory p1Start p2Start))) =
      Bn254G1AddResultBridge.outputBytesList
        (accelerator
          (Bn254G1AddInputBridge.bn254G1AddInputFromMemory
            memory p1Start p2Start)).2 := by
  rfl

/-- RV64 `a0` return-register `Word` for the accelerator status, mirroring
`Sha256EcallBridge.statusWord`. The accelerator places the `zkvm_status`
return code in `a0` after the ECALL; this projection extracts that word from
a `Bn254G1AddResult` for postcondition reasoning. -/
def statusWord (result : Bn254G1AddResult) : BitVec 64 :=
  EvmAsm.Rv64.zkvmStatusToWord result.status

theorem statusWord_eok
    {result : Bn254G1AddResult} (h_status : result.status = .eok) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEokWord := by
  show EvmAsm.Rv64.zkvmStatusToWord result.status = _
  rw [h_status]; rfl

theorem statusWord_efail
    {result : Bn254G1AddResult} (h_status : result.status = .efail) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEfailWord := by
  show EvmAsm.Rv64.zkvmStatusToWord result.status = _
  rw [h_status]; rfl

/-- The `a0` word is `ZKVM_EOK` iff the accelerator reported success. -/
theorem statusWord_eq_eokWord_iff (result : Bn254G1AddResult) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEokWord ↔ result.status = .eok := by
  cases h_st : result.status with
  | eok => simp [statusWord_eok h_st]
  | efail =>
    rw [statusWord_efail h_st]
    constructor
    · intro h; exact absurd h.symm EvmAsm.Rv64.zkvmStatusEokWord_ne_efailWord
    · intro h; simp at h

/-- The `a0` word decodes back to the original status. -/
theorem zkvmStatusFromWord?_statusWord (result : Bn254G1AddResult) :
    EvmAsm.Rv64.zkvmStatusFromWord? (statusWord result) = some result.status :=
  EvmAsm.Rv64.zkvmStatusFromWord?_toWord result.status

/-- Push `statusWord` through `executeBn254G1AddEcall`: the returned `a0` word is
the accelerator-supplied status encoded via `zkvmStatusToWord`. -/
theorem executeBn254G1AddEcall_statusWord
    (accelerator : Bn254G1AddInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Bn254G1AddResultBridge.AcceleratorOutput)
    (request : Bn254G1AddRequest) :
    statusWord (executeBn254G1AddEcall accelerator request) =
      EvmAsm.Rv64.zkvmStatusToWord (accelerator request.input).1 := by
  rfl

end Bn254G1AddEcallBridge

end EvmAsm.EL
