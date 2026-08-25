/-
  EvmAsm.EL.Bls12PairingResultBridge

  Bridge from the `zkvm_bls12_pairing` accelerator output to the executable
  precompile-result surface.
-/

module

public import EvmAsm.Evm64.Accelerators.Status

@[expose] public section

namespace EvmAsm.EL

namespace Bls12PairingResultBridge

abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

/-- Accelerator output payload for `zkvm_bls12_pairing`. -/
structure AcceleratorOutput where
  verified : Bool
  deriving Repr

/-- Full ECALL result: status code plus output buffer contents. -/
structure AcceleratorResult where
  status : ZkvmStatus
  output : AcceleratorOutput

/-- EVM precompile success word for a true pairing check. -/
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

end Bls12PairingResultBridge

end EvmAsm.EL
