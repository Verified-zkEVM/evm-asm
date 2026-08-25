/-
  EvmAsm.EL.KzgPointEvalResultBridge

  Bridge from the `zkvm_kzg_point_eval` accelerator output to the executable
  precompile-result surface.
-/

module

public import EvmAsm.Evm64.Accelerators.Status

@[expose] public section

namespace EvmAsm.EL

namespace KzgPointEvalResultBridge

abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

/-- Accelerator output payload for `zkvm_kzg_point_eval`. -/
structure AcceleratorOutput where
  verified : Bool
  deriving Repr

/-- Full ECALL result: status code plus output buffer contents. -/
structure AcceleratorResult where
  status : ZkvmStatus
  output : AcceleratorOutput

/-- EVM precompile success word for a true KZG point-evaluation proof. -/
def successWordFromVerified (verified : Bool) : BitVec 256 :=
  if verified then 1 else 0

theorem successWordFromVerified_true :
    successWordFromVerified true = 1 := rfl

theorem successWordFromVerified_false :
    successWordFromVerified false = 0 := rfl

theorem acceleratorResult_status (result : AcceleratorResult) :
    result.status = result.status := rfl

theorem acceleratorResult_output (result : AcceleratorResult) :
    result.output = result.output := rfl

theorem acceleratorOutput_successWord (output : AcceleratorOutput) :
    successWordFromVerified output.verified = if output.verified then 1 else 0 := rfl

end KzgPointEvalResultBridge

end EvmAsm.EL
