/-
  EvmAsm.Evm64.Eq.LimbSpec

  Per-limb EQ specs (XOR + OR accumulation).
-/

import EvmAsm.Evm64.Eq.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- EQ limb 0 spec (3 instructions): LD x7, LD x6, XOR x7 x7 x6. -/
theorem eq_limb0_spec_within (offA offB : BitVec 12)
    (sp aLimb bLimb v7 v6 : Word) (base : Word) :
    let memA := sp + signExtend12 offA
    let memB := sp + signExtend12 offB
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 offA))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 offB))
       (CodeReq.singleton (base + 8) (.XOR .x7 .x7 .x6)))
    cpsTripleWithin 3 base (base + 12) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ bLimb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (aLimb ^^^ bLimb)) ** (.x6 ↦ᵣ bLimb) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ bLimb)) := by
  have L0 := ld_spec_gen_within .x7 .x12 sp v7 aLimb offA base (by nofun)
  have L1 := ld_spec_gen_within .x6 .x12 sp v6 bLimb offB (base + 4) (by nofun)
  have X := xor_spec_gen_rd_eq_rs1_within .x7 .x6 aLimb bLimb (base + 8) (by nofun)
  runBlock L0 L1 X


/-- EQ OR-limb spec (4 instructions): LD x6, LD x5, XOR x6 x6 x5, OR x7 x7 x6. -/
theorem eq_or_limb_spec_within (offA offB : BitVec 12)
    (sp aLimb bLimb v6 v5 acc : Word) (base : Word) :
    let memA := sp + signExtend12 offA
    let memB := sp + signExtend12 offB
    let xorK := aLimb ^^^ bLimb
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x6 .x12 offA))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x5 .x12 offB))
      (CodeReq.union (CodeReq.singleton (base + 8) (.XOR .x6 .x6 .x5))
       (CodeReq.singleton (base + 12) (.OR .x7 .x7 .x6))))
    cpsTripleWithin 4 base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ acc) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ bLimb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (acc ||| xorK)) ** (.x6 ↦ᵣ xorK) ** (.x5 ↦ᵣ bLimb) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ bLimb)) := by
  have L0 := ld_spec_gen_within .x6 .x12 sp v6 aLimb offA base (by nofun)
  have L1 := ld_spec_gen_within .x5 .x12 sp v5 bLimb offB (base + 4) (by nofun)
  have X := xor_spec_gen_rd_eq_rs1_within .x6 .x5 aLimb bLimb (base + 8) (by nofun)
  have O := or_spec_gen_rd_eq_rs1_within .x7 .x6 acc (aLimb ^^^ bLimb) (base + 12) (by nofun)
  runBlock L0 L1 X O


end EvmAsm.Evm64
