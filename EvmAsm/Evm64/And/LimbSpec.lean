/-
  EvmAsm.Evm64.And.LimbSpec

  Per-limb AND spec.
-/

import EvmAsm.Evm64.And.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Per-limb AND spec (4 instructions: LD x7, LD x6, AND x7 x7 x6, SD x12 x7).
    Loads A[i] and B[i], computes AND, stores result at B[i]'s location. -/
theorem and_limb_spec (offA offB : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Word) :
    let memA := sp + signExtend12 offA
    let memB := sp + signExtend12 offB
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 offA))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 offB))
      (CodeReq.union (CodeReq.singleton (base + 8) (.AND .x7 .x7 .x6))
       (CodeReq.singleton (base + 12) (.SD .x12 .x7 offB))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (memA ↦ₘ a_limb) ** (memB ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb &&& b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (memA ↦ₘ a_limb) ** (memB ↦ₘ (a_limb &&& b_limb))) := by
  runBlock

end EvmAsm.Evm64
