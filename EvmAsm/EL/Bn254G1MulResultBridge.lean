/-
  EvmAsm.EL.Bn254G1MulResultBridge

  Bridge from the `zkvm_bn254_g1_mul` accelerator output to the executable
  precompile-result surface.
-/

module

public import EvmAsm.Evm64.Accelerators.Status
public import EvmAsm.EL.WorldState

@[expose] public section

namespace EvmAsm.EL

namespace Bn254G1MulResultBridge

abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus
abbrev G1PointBytes := Fin 64 → Byte

/-- Accelerator output payload for `zkvm_bn254_g1_mul`. -/
structure AcceleratorOutput where
  point : G1PointBytes

/-- Full ECALL result: status code plus output buffer contents. -/
structure AcceleratorResult where
  status : ZkvmStatus
  output : AcceleratorOutput

def g1PointBytesList (point : G1PointBytes) : List Byte :=
  List.ofFn point

theorem g1PointBytesList_length (point : G1PointBytes) :
    (g1PointBytesList point).length = 64 := by
  simp [g1PointBytesList]

theorem acceleratorResult_status (result : AcceleratorResult) :
    result.status = result.status := rfl

theorem acceleratorResult_output (result : AcceleratorResult) :
    result.output = result.output := rfl

theorem acceleratorOutput_point_length (output : AcceleratorOutput) :
    (g1PointBytesList output.point).length = 64 :=
  g1PointBytesList_length output.point

end Bn254G1MulResultBridge

end EvmAsm.EL
