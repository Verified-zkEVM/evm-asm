/-
  EvmAsm.Evm64.Not.LimbSpec

  Per-limb NOT spec.
-/

import EvmAsm.Evm64.Not.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Per-limb NOT spec (3 instructions: LD x7, XORI x7 x7 (-1), SD x12 x7).
    Unary: loads limb, complements it, stores back to same location. -/
theorem not_limb_spec_within (off : BitVec 12)
    (sp limb v7 : Word) (base : Word) :
    let mem := sp + signExtend12 off
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.XORI .x7 .x7 (-1)))
       (CodeReq.singleton (base + 8) (.SD .x12 .x7 off)))
    cpsTripleWithin 3 base (base + 12) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (mem ↦ₘ limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (limb ^^^ signExtend12 (-1))) ** (mem ↦ₘ (limb ^^^ signExtend12 (-1)))) := by
  have L := ld_spec_gen_within .x7 .x12 sp v7 limb off base (by nofun)
  have X := xori_spec_gen_same_within .x7 limb (-1) (base + 4) (by nofun)
  have S := sd_spec_gen_within .x12 .x7 sp (limb ^^^ signExtend12 (-1)) limb off (base + 8)
  runBlock L X S


end EvmAsm.Evm64
