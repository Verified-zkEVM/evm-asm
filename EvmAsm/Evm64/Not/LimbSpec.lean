/-
  EvmAsm.Evm64.Not.LimbSpec

  Per-limb NOT spec.
-/

import EvmAsm.Evm64.Not.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

/-- Per-limb NOT spec (3 instructions: LD x7, XORI x7 x7 (-1), SD x12 x7).
    Unary: loads limb, complements it, stores back to same location. -/
theorem not_limb_spec (off : BitVec 12)
    (sp limb v7 : Word) (base : Word)
    (hvalid : isValidDwordAccess (sp + signExtend12 off) = true) :
    let mem := sp + signExtend12 off
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.XORI .x7 .x7 (-1)))
       (CodeReq.singleton (base + 8) (.SD .x12 .x7 off)))
    cpsTriple base (base + 12) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (mem ↦ₘ limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (limb ^^^ signExtend12 (-1))) ** (mem ↦ₘ (limb ^^^ signExtend12 (-1)))) := by
  runBlock

end EvmAsm.Rv64
