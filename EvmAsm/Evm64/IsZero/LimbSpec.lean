/-
  EvmAsm.Evm64.IsZero.LimbSpec

  Per-limb ISZERO spec (OR reduction).
-/

import EvmAsm.Evm64.IsZero.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

/-- ISZERO OR-limb spec (2 instructions): LD x6, OR x7 x7 x6.
    Loads a limb and OR-accumulates into x7. -/
theorem iszero_or_limb_spec (off : BitVec 12)
    (sp a_limb v6 acc : Word) (base : Word)
    (hvalid : isValidDwordAccess (sp + signExtend12 off) = true) :
    let mem := sp + signExtend12 off
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x6 .x12 off))
       (CodeReq.singleton (base + 4) (.OR .x7 .x7 .x6))
    cpsTriple base (base + 8) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ acc) ** (.x6 ↦ᵣ v6) **
       (mem ↦ₘ a_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (acc ||| a_limb)) ** (.x6 ↦ᵣ a_limb) **
       (mem ↦ₘ a_limb)) := by
  runBlock

end EvmAsm.Rv64
