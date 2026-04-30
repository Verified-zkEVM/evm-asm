/-
  EvmAsm.Evm64.IsZero.LimbSpec

  Per-limb ISZERO spec (OR reduction).
-/

import EvmAsm.Evm64.IsZero.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- ISZERO OR-limb spec (2 instructions): LD x6, OR x7 x7 x6.
    Loads a limb and OR-accumulates into x7. -/
theorem iszero_or_limb_spec_within (off : BitVec 12)
    (sp aLimb v6 acc : Word) (base : Word) :
    let mem := sp + signExtend12 off
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x6 .x12 off))
       (CodeReq.singleton (base + 4) (.OR .x7 .x7 .x6))
    cpsTripleWithin 2 base (base + 8) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ acc) ** (.x6 ↦ᵣ v6) **
       (mem ↦ₘ aLimb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (acc ||| aLimb)) ** (.x6 ↦ᵣ aLimb) **
       (mem ↦ₘ aLimb)) := by
  have L := ld_spec_gen_within .x6 .x12 sp v6 aLimb off base (by nofun)
  have O := or_spec_gen_rd_eq_rs1_within .x7 .x6 acc aLimb (base + 4) (by nofun)
  runBlock L O


end EvmAsm.Evm64
