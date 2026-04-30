/-
  EvmAsm.Evm64.Sub.LimbSpec

  Per-limb SUB specs (from Arithmetic.lean).
-/

import EvmAsm.Evm64.Sub.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- SUB limb 0 spec (5 instructions): LD, LD, SLTU, SUB, SD.
    Computes diff = a - b (mod 2^64) and borrow = (a < b ? 1 : 0). -/
theorem sub_limb0_spec_within (offA offB : BitVec 12)
    (sp aLimb bLimb v7 v6 v5 : Word) (base : Word) :
    let memA := sp + signExtend12 offA
    let memB := sp + signExtend12 offB
    let borrow := if BitVec.ult aLimb bLimb then (1 : Word) else 0
    let diff := aLimb - bLimb
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 offA))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 offB))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLTU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SUB .x7 .x7 .x6))
       (CodeReq.singleton (base + 16) (.SD .x12 .x7 offB)))))
    cpsTripleWithin 5 base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ bLimb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ diff) ** (.x6 ↦ᵣ bLimb) ** (.x5 ↦ᵣ borrow) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ diff)) := by
  intro memA memB borrow diff cr
  have L0 := ld_spec_gen_within .x7 .x12 sp v7 aLimb offA base (by nofun)
  have L1 := ld_spec_gen_within .x6 .x12 sp v6 bLimb offB (base + 4) (by nofun)
  have B := sltu_spec_gen_within .x5 .x7 .x6 v5 aLimb bLimb (base + 8) (by nofun)
  have S := sub_spec_gen_rd_eq_rs1_within .x7 .x6 aLimb bLimb (base + 12) (by nofun)
  have St := sd_spec_gen_within .x12 .x7 sp diff bLimb offB (base + 16)
  runBlock L0 L1 B S St


/-- SUB carry limb phase 1 (4 instructions): LD, LD, SLTU, SUB.
    Loads aLimb and bLimb, computes borrow1 = (a < b ? 1 : 0), temp = a - b. -/
theorem sub_limb_carry_spec_phase1_within (offA offB : BitVec 12)
    (sp aLimb bLimb v7 v6 borrowIn v11 : Word) (base : Word) :
    let memA := sp + signExtend12 offA
    let memB := sp + signExtend12 offB
    let borrow1 := if BitVec.ult aLimb bLimb then (1 : Word) else 0
    let temp := aLimb - bLimb
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 offA))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 offB))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLTU .x11 .x7 .x6))
       (CodeReq.singleton (base + 12) (.SUB .x7 .x7 .x6))))
    cpsTripleWithin 4 base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrowIn) ** (.x11 ↦ᵣ v11) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ bLimb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ temp) ** (.x6 ↦ᵣ bLimb) ** (.x5 ↦ᵣ borrowIn) ** (.x11 ↦ᵣ borrow1) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ bLimb)) := by
  intro memA memB borrow1 temp cr
  have L0 := ld_spec_gen_within .x7 .x12 sp v7 aLimb offA base (by nofun)
  have L1 := ld_spec_gen_within .x6 .x12 sp v6 bLimb offB (base + 4) (by nofun)
  have B := sltu_spec_gen_within .x11 .x7 .x6 v11 aLimb bLimb (base + 8) (by nofun)
  have S := sub_spec_gen_rd_eq_rs1_within .x7 .x6 aLimb bLimb (base + 12) (by nofun)
  runBlock L0 L1 B S


/-- SUB carry limb phase 2 (4 instructions): SLTU, SUB, OR, SD.
    Takes temp, borrow1, borrowIn, computes borrow2 = (temp < borrowIn ? 1 : 0),
    result = temp - borrowIn, borrowOut = borrow1 ||| borrow2. -/
theorem sub_limb_carry_spec_phase2_within (offB : BitVec 12)
    (sp temp bLimb borrowIn borrow1 aLimb : Word) (memA : Word) (base : Word) :
    let memB := sp + signExtend12 offB
    let borrow2 := if BitVec.ult temp borrowIn then (1 : Word) else 0
    let result := temp - borrowIn
    let borrowOut := borrow1 ||| borrow2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLTU .x6 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SUB .x7 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.OR .x5 .x11 .x6))
       (CodeReq.singleton (base + 12) (.SD .x12 .x7 offB))))
    cpsTripleWithin 4 base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ temp) ** (.x6 ↦ᵣ bLimb) ** (.x5 ↦ᵣ borrowIn) ** (.x11 ↦ᵣ borrow1) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ bLimb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ borrow2) ** (.x5 ↦ᵣ borrowOut) ** (.x11 ↦ᵣ borrow1) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ result)) := by
  intro memB borrow2 result borrowOut cr
  have B := sltu_spec_gen_within .x6 .x7 .x5 bLimb temp borrowIn base (by nofun)
  have S := sub_spec_gen_rd_eq_rs1_within .x7 .x5 temp borrowIn (base + 4) (by nofun)
  have O := or_spec_gen_within .x5 .x11 .x6 borrowIn borrow1 borrow2 (base + 8) (by nofun)
  have St := sd_spec_gen_within .x12 .x7 sp result bLimb offB (base + 12)
  runBlock B S O St


/-- SUB carry limb spec (8 instructions): LD, LD, SLTU, SUB, SLTU, SUB, OR, SD.
    Composed from phase1 and phase2. -/
theorem sub_limb_carry_spec_within (offA offB : BitVec 12)
    (sp aLimb bLimb v7 v6 borrowIn v11 : Word) (base : Word) :
    let memA := sp + signExtend12 offA
    let memB := sp + signExtend12 offB
    let borrow1 := if BitVec.ult aLimb bLimb then (1 : Word) else 0
    let temp := aLimb - bLimb
    let borrow2 := if BitVec.ult temp borrowIn then (1 : Word) else 0
    let result := temp - borrowIn
    let borrowOut := borrow1 ||| borrow2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 offA))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 offB))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLTU .x11 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SUB .x7 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SLTU .x6 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 20) (.SUB .x7 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 24) (.OR .x5 .x11 .x6))
       (CodeReq.singleton (base + 28) (.SD .x12 .x7 offB))))))))
    cpsTripleWithin 8 base (base + 32) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrowIn) ** (.x11 ↦ᵣ v11) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ bLimb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ borrow2) ** (.x5 ↦ᵣ borrowOut) ** (.x11 ↦ᵣ borrow1) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ result)) := by
  have p1 := sub_limb_carry_spec_phase1_within offA offB sp aLimb bLimb v7 v6 borrowIn v11 base
  have p2 := sub_limb_carry_spec_phase2_within offB sp (aLimb - bLimb) bLimb borrowIn
    (if BitVec.ult aLimb bLimb then (1 : Word) else 0)
    aLimb (sp + signExtend12 offA) (base + 16)
  runBlock p1 p2


end EvmAsm.Evm64
