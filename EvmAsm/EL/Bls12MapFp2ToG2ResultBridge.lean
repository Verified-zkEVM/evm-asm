/-
  EvmAsm.EL.Bls12MapFp2ToG2ResultBridge

  Bridge from the `zkvm_bls12_map_fp2_to_g2` accelerator output to the
  executable precompile-result surface.
-/

module

public import EvmAsm.Evm64.Accelerators.Status
public import EvmAsm.EL.WorldState

@[expose] public section

namespace EvmAsm.EL

namespace Bls12MapFp2ToG2ResultBridge

abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

/-- A BLS12-381 G2 point as represented by `zkvm_bls12_381_g2_point`
(`zkvm_bytes_192`). -/
abbrev G2PointBytes := Fin 192 → Byte

/-- Accelerator output payload for `zkvm_bls12_map_fp2_to_g2`. -/
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
  exact List.length_ofFn (f := point)

theorem acceleratorResult_status (result : AcceleratorResult) :
    result.status = result.status := rfl

theorem acceleratorResult_output (result : AcceleratorResult) :
    result.output = result.output := rfl

theorem acceleratorOutput_point_length (output : AcceleratorOutput) :
    (g2PointBytesList output.point).length = 192 :=
  g2PointBytesList_length output.point

end Bls12MapFp2ToG2ResultBridge

end EvmAsm.EL
