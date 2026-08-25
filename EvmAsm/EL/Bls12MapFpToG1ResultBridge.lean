/-
  EvmAsm.EL.Bls12MapFpToG1ResultBridge

  Bridge from the `zkvm_bls12_map_fp_to_g1` accelerator output to the executable
  precompile-result surface.
-/

module

public import EvmAsm.Evm64.Accelerators.Status
public import EvmAsm.EL.WorldState

@[expose] public section

namespace EvmAsm.EL

namespace Bls12MapFpToG1ResultBridge

abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

/-- The result is `zkvm_bls12_381_g1_point` (96 bytes). -/
abbrev G1PointBytes := Fin 96 → Byte

/-- Accelerator output payload for `zkvm_bls12_map_fp_to_g1`. -/
structure AcceleratorOutput where
  point : G1PointBytes

/-- Full ECALL result: status code plus output buffer contents. -/
structure AcceleratorResult where
  status : ZkvmStatus
  output : AcceleratorOutput

def g1PointBytesList (point : G1PointBytes) : List Byte :=
  List.ofFn point

theorem g1PointBytesList_length (point : G1PointBytes) :
    (g1PointBytesList point).length = 96 := by
  simp [g1PointBytesList]

theorem acceleratorResult_status (result : AcceleratorResult) :
    result.status = result.status := rfl

theorem acceleratorResult_output (result : AcceleratorResult) :
    result.output = result.output := rfl

theorem acceleratorOutput_point_length (output : AcceleratorOutput) :
    (g1PointBytesList output.point).length = 96 :=
  g1PointBytesList_length output.point

end Bls12MapFpToG1ResultBridge

end EvmAsm.EL
