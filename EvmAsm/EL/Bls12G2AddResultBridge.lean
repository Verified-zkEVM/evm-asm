/-
  EvmAsm.EL.Bls12G2AddResultBridge

  Bridge from the `zkvm_bls12_g2_add` accelerator output to the executable
  precompile-result surface.
-/

module

public import EvmAsm.Evm64.Accelerators.Status
public import EvmAsm.EL.WorldState

@[expose] public section

namespace EvmAsm.EL

namespace Bls12G2AddResultBridge

abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus
abbrev G2PointBytes := Fin 192 → Byte

/-- Accelerator output payload for `zkvm_bls12_g2_add`. -/
structure AcceleratorOutput where
  point : G2PointBytes

/-- Full ECALL result: status code plus output buffer contents. -/
structure AcceleratorResult where
  status : ZkvmStatus
  output : AcceleratorOutput

def g2PointBytesList (point : G2PointBytes) : List Byte :=
  List.ofFn point

theorem g2PointBytesList_length (point : G2PointBytes) :
    (g2PointBytesList point).length = 192 := by
  unfold g2PointBytesList
  exact List.length_ofFn

theorem acceleratorResult_status (result : AcceleratorResult) :
    result.status = result.status := rfl

theorem acceleratorResult_output (result : AcceleratorResult) :
    result.output = result.output := rfl

theorem acceleratorOutput_point_length (output : AcceleratorOutput) :
    (g2PointBytesList output.point).length = 192 :=
  g2PointBytesList_length output.point

end Bls12G2AddResultBridge

end EvmAsm.EL
