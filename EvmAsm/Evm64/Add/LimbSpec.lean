/-
  EvmAsm.Evm64.Add.LimbSpec

  Per-limb ADD specs (from Arithmetic.lean).
-/

import EvmAsm.Evm64.Add.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- ADD limb 0 spec (5 instructions): LD, LD, ADD, SLTU, SD.
    Computes sum = a + b (mod 2^64) and carry = (sum < b ? 1 : 0). -/
theorem add_limb0_spec (offA offB : BitVec 12)
    (sp aLimb bLimb v7 v6 v5 : Word) (base : Word) :
    let memA := sp + signExtend12 offA
    let memB := sp + signExtend12 offB
    let sum := aLimb + bLimb
    let carry := if BitVec.ult sum bLimb then (1 : Word) else 0
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 offA))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 offB))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADD .x7 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x5 .x7 .x6))
       (CodeReq.singleton (base + 16) (.SD .x12 .x7 offB)))))
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ bLimb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ sum) ** (.x6 ↦ᵣ bLimb) ** (.x5 ↦ᵣ carry) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ sum)) := by
  runBlock

/-- ADD carry limb phase 1 (4 instructions): LD, LD, ADD, SLTU.
    Loads aLimb and bLimb, computes psum = a + b, carry1 = (psum < b ? 1 : 0). -/
theorem add_limb_carry_spec_phase1 (offA offB : BitVec 12)
    (sp aLimb bLimb v7 v6 carryIn v11 : Word) (base : Word) :
    let memA := sp + signExtend12 offA
    let memB := sp + signExtend12 offB
    let psum := aLimb + bLimb
    let carry1 := if BitVec.ult psum bLimb then (1 : Word) else 0
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 offA))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 offB))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADD .x7 .x7 .x6))
       (CodeReq.singleton (base + 12) (.SLTU .x11 .x7 .x6))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ carryIn) ** (.x11 ↦ᵣ v11) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ bLimb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ psum) ** (.x6 ↦ᵣ bLimb) ** (.x5 ↦ᵣ carryIn) ** (.x11 ↦ᵣ carry1) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ bLimb)) := by
  runBlock

/-- ADD carry limb phase 2 (4 instructions): ADD, SLTU, OR, SD.
    Takes psum, carry1, carryIn, computes result = psum + carryIn,
    carry2 = (result < carryIn ? 1 : 0), carryOut = carry1 ||| carry2. -/
theorem add_limb_carry_spec_phase2 (offB : BitVec 12)
    (sp psum bLimb carryIn carry1 aLimb : Word) (memA : Word) (base : Word) :
    let memB := sp + signExtend12 offB
    let result := psum + carryIn
    let carry2 := if BitVec.ult result carryIn then (1 : Word) else 0
    let carryOut := carry1 ||| carry2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.ADD .x7 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SLTU .x6 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.OR .x5 .x11 .x6))
       (CodeReq.singleton (base + 12) (.SD .x12 .x7 offB))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ psum) ** (.x6 ↦ᵣ bLimb) ** (.x5 ↦ᵣ carryIn) ** (.x11 ↦ᵣ carry1) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ bLimb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ carry2) ** (.x5 ↦ᵣ carryOut) ** (.x11 ↦ᵣ carry1) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ result)) := by
  runBlock

/-- ADD carry limb spec (8 instructions): LD, LD, ADD, SLTU, ADD, SLTU, OR, SD.
    Composed from phase1 and phase2. -/
theorem add_limb_carry_spec (offA offB : BitVec 12)
    (sp aLimb bLimb v7 v6 carryIn v11 : Word) (base : Word) :
    let memA := sp + signExtend12 offA
    let memB := sp + signExtend12 offB
    let psum := aLimb + bLimb
    let carry1 := if BitVec.ult psum bLimb then (1 : Word) else 0
    let result := psum + carryIn
    let carry2 := if BitVec.ult result carryIn then (1 : Word) else 0
    let carryOut := carry1 ||| carry2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 offA))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 offB))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADD .x7 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x11 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 16) (.ADD .x7 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 20) (.SLTU .x6 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 24) (.OR .x5 .x11 .x6))
       (CodeReq.singleton (base + 28) (.SD .x12 .x7 offB))))))))
    cpsTriple base (base + 32) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ carryIn) ** (.x11 ↦ᵣ v11) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ bLimb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ carry2) ** (.x5 ↦ᵣ carryOut) ** (.x11 ↦ᵣ carry1) **
       (memA ↦ₘ aLimb) ** (memB ↦ₘ result)) := by
  have p1 := add_limb_carry_spec_phase1 offA offB sp aLimb bLimb v7 v6 carryIn v11 base
  have p2 := add_limb_carry_spec_phase2 offB sp (aLimb + bLimb) bLimb carryIn
    (if BitVec.ult (aLimb + bLimb) bLimb then (1 : Word) else 0)
    aLimb (sp + signExtend12 offA) (base + 16)
  runBlock p1 p2

end EvmAsm.Evm64
