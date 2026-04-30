/-
  EvmAsm.Evm64.Or.LimbSpec

  Per-limb OR spec.
-/

import EvmAsm.Evm64.Or.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Per-limb OR spec (4 instructions: LD x7, LD x6, OR x7 x7 x6, SD x12 x7). -/
theorem or_limb_spec_within (offA offB : BitVec 12)
    (sp aLimb bLimb v7 v6 : Word) (base : Word) :
    let memA := sp + signExtend12 offA
    let memB := sp + signExtend12 offB
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 offA))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 offB))
      (CodeReq.union (CodeReq.singleton (base + 8) (.OR .x7 .x7 .x6))
       (CodeReq.singleton (base + 12) (.SD .x12 .x7 offB))))
    cpsTripleWithin 4 base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ bLimb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (aLimb ||| bLimb)) ** (.x6 ↦ᵣ bLimb) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ (aLimb ||| bLimb))) := by
  have L0 := ld_spec_gen_within .x7 .x12 sp v7 aLimb offA base (by nofun)
  have L1 := ld_spec_gen_within .x6 .x12 sp v6 bLimb offB (base + 4) (by nofun)
  have O := or_spec_gen_rd_eq_rs1_within .x7 .x6 aLimb bLimb (base + 8) (by nofun)
  have S := sd_spec_gen_within .x12 .x7 sp (aLimb ||| bLimb) bLimb offB (base + 12)
  runBlock L0 L1 O S


end EvmAsm.Evm64
