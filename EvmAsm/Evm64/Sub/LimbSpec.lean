/-
  EvmAsm.Evm64.Sub.LimbSpec

  Per-limb SUB specs (from Arithmetic.lean).
-/

import EvmAsm.Evm64.Sub.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- SUB limb 0 spec (5 instructions): LD, LD, SLTU, SUB, SD.
    Computes diff = a - b (mod 2^64) and borrow = (a < b ? 1 : 0). -/
theorem sub_limb0_spec (offA offB : BitVec 12)
    (sp a_limb b_limb v7 v6 v5 : Word) (base : Word) :
    let memA := sp + signExtend12 offA
    let memB := sp + signExtend12 offB
    let borrow := if BitVec.ult a_limb b_limb then (1 : Word) else 0
    let diff := a_limb - b_limb
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 offA))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 offB))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLTU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SUB .x7 .x7 .x6))
       (CodeReq.singleton (base + 16) (.SD .x12 .x7 offB)))))
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (memA ↦ₘ a_limb) ** (memB ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ diff) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ borrow) **
       (memA ↦ₘ a_limb) ** (memB ↦ₘ diff)) := by
  runBlock

/-- SUB carry limb phase 1 (4 instructions): LD, LD, SLTU, SUB.
    Loads a_limb and b_limb, computes borrow1 = (a < b ? 1 : 0), temp = a - b. -/
theorem sub_limb_carry_spec_phase1 (offA offB : BitVec 12)
    (sp a_limb b_limb v7 v6 borrow_in v11 : Word) (base : Word) :
    let memA := sp + signExtend12 offA
    let memB := sp + signExtend12 offB
    let borrow1 := if BitVec.ult a_limb b_limb then (1 : Word) else 0
    let temp := a_limb - b_limb
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 offA))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 offB))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLTU .x11 .x7 .x6))
       (CodeReq.singleton (base + 12) (.SUB .x7 .x7 .x6))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ v11) **
       (memA ↦ₘ a_limb) ** (memB ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ temp) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ borrow1) **
       (memA ↦ₘ a_limb) ** (memB ↦ₘ b_limb)) := by
  runBlock

/-- SUB carry limb phase 2 (4 instructions): SLTU, SUB, OR, SD.
    Takes temp, borrow1, borrow_in, computes borrow2 = (temp < borrow_in ? 1 : 0),
    result = temp - borrow_in, borrowOut = borrow1 ||| borrow2. -/
theorem sub_limb_carry_spec_phase2 (offB : BitVec 12)
    (sp temp b_limb borrow_in borrow1 a_limb : Word) (memA : Word) (base : Word) :
    let memB := sp + signExtend12 offB
    let borrow2 := if BitVec.ult temp borrow_in then (1 : Word) else 0
    let result := temp - borrow_in
    let borrowOut := borrow1 ||| borrow2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SLTU .x6 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SUB .x7 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.OR .x5 .x11 .x6))
       (CodeReq.singleton (base + 12) (.SD .x12 .x7 offB))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ temp) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ borrow1) **
       (memA ↦ₘ a_limb) ** (memB ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ borrow2) ** (.x5 ↦ᵣ borrowOut) ** (.x11 ↦ᵣ borrow1) **
       (memA ↦ₘ a_limb) ** (memB ↦ₘ result)) := by
  runBlock

/-- SUB carry limb spec (8 instructions): LD, LD, SLTU, SUB, SLTU, SUB, OR, SD.
    Composed from phase1 and phase2. -/
theorem sub_limb_carry_spec (offA offB : BitVec 12)
    (sp a_limb b_limb v7 v6 borrow_in v11 : Word) (base : Word) :
    let memA := sp + signExtend12 offA
    let memB := sp + signExtend12 offB
    let borrow1 := if BitVec.ult a_limb b_limb then (1 : Word) else 0
    let temp := a_limb - b_limb
    let borrow2 := if BitVec.ult temp borrow_in then (1 : Word) else 0
    let result := temp - borrow_in
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
    cpsTriple base (base + 32) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ v11) **
       (memA ↦ₘ a_limb) ** (memB ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ borrow2) ** (.x5 ↦ᵣ borrowOut) ** (.x11 ↦ᵣ borrow1) **
       (memA ↦ₘ a_limb) ** (memB ↦ₘ result)) := by
  have p1 := sub_limb_carry_spec_phase1 offA offB sp a_limb b_limb v7 v6 borrow_in v11 base
  have p2 := sub_limb_carry_spec_phase2 offB sp (a_limb - b_limb) b_limb borrow_in
    (if BitVec.ult a_limb b_limb then (1 : Word) else 0)
    a_limb (sp + signExtend12 offA) (base + 16)
  runBlock p1 p2

end EvmAsm.Evm64
