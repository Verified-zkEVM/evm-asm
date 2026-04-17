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
theorem add_limb0_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 v5 : Word) (base : Word) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let sum := a_limb + b_limb
    let carry := if BitVec.ult sum b_limb then (1 : Word) else 0
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off_a))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 off_b))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADD .x7 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x5 .x7 .x6))
       (CodeReq.singleton (base + 16) (.SD .x12 .x7 off_b)))))
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ sum) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ carry) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ sum)) := by
  runBlock

/-- ADD carry limb phase 1 (4 instructions): LD, LD, ADD, SLTU.
    Loads a_limb and b_limb, computes psum = a + b, carry1 = (psum < b ? 1 : 0). -/
theorem add_limb_carry_spec_phase1 (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 carry_in v11 : Word) (base : Word) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let psum := a_limb + b_limb
    let carry1 := if BitVec.ult psum b_limb then (1 : Word) else 0
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off_a))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 off_b))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADD .x7 .x7 .x6))
       (CodeReq.singleton (base + 12) (.SLTU .x11 .x7 .x6))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ carry_in) ** (.x11 ↦ᵣ v11) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ psum) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ carry_in) ** (.x11 ↦ᵣ carry1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb)) := by
  runBlock

/-- ADD carry limb phase 2 (4 instructions): ADD, SLTU, OR, SD.
    Takes psum, carry1, carry_in, computes result = psum + carry_in,
    carry2 = (result < carry_in ? 1 : 0), carry_out = carry1 ||| carry2. -/
theorem add_limb_carry_spec_phase2 (off_b : BitVec 12)
    (sp psum b_limb carry_in carry1 a_limb : Word) (mem_a : Word) (base : Word) :
    let mem_b := sp + signExtend12 off_b
    let result := psum + carry_in
    let carry2 := if BitVec.ult result carry_in then (1 : Word) else 0
    let carry_out := carry1 ||| carry2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.ADD .x7 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 4) (.SLTU .x6 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 8) (.OR .x5 .x11 .x6))
       (CodeReq.singleton (base + 12) (.SD .x12 .x7 off_b))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ psum) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ carry_in) ** (.x11 ↦ᵣ carry1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ carry2) ** (.x5 ↦ᵣ carry_out) ** (.x11 ↦ᵣ carry1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ result)) := by
  runBlock

/-- ADD carry limb spec (8 instructions): LD, LD, ADD, SLTU, ADD, SLTU, OR, SD.
    Composed from phase1 and phase2. -/
theorem add_limb_carry_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 carry_in v11 : Word) (base : Word) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let psum := a_limb + b_limb
    let carry1 := if BitVec.ult psum b_limb then (1 : Word) else 0
    let result := psum + carry_in
    let carry2 := if BitVec.ult result carry_in then (1 : Word) else 0
    let carry_out := carry1 ||| carry2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off_a))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 off_b))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADD .x7 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x11 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 16) (.ADD .x7 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 20) (.SLTU .x6 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 24) (.OR .x5 .x11 .x6))
       (CodeReq.singleton (base + 28) (.SD .x12 .x7 off_b))))))))
    cpsTriple base (base + 32) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ carry_in) ** (.x11 ↦ᵣ v11) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ carry2) ** (.x5 ↦ᵣ carry_out) ** (.x11 ↦ᵣ carry1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ result)) := by
  have p1 := add_limb_carry_spec_phase1 off_a off_b sp a_limb b_limb v7 v6 carry_in v11 base
  have p2 := add_limb_carry_spec_phase2 off_b sp (a_limb + b_limb) b_limb carry_in
    (if BitVec.ult (a_limb + b_limb) b_limb then (1 : Word) else 0)
    a_limb (sp + signExtend12 off_a) (base + 16)
  runBlock p1 p2

end EvmAsm.Evm64
