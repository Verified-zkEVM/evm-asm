/-
  EvmAsm.Evm64.AddMod.LimbSpec

  Per-block / per-limb cpsTriple specs for ADDMOD sub-blocks (operand
  widening, callable-divide JAL, result narrowing).

  Skeleton placeholder for GH #91 (beads slice evm-asm-w1s0). Per
  `OPCODE_TEMPLATE.md`, each sub-block will get exactly one cpsTriple
  lemma once the Compose layer pins the layout.
-/

import EvmAsm.Evm64.AddMod.Program
import EvmAsm.Evm64.Add.Spec
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- evm_addmod_prologue (30 instructions, slice evm-asm-hm8z3 toward evm-asm-s7v49)
-- ============================================================================
--
-- `evm_addmod_prologue` (defined in `Evm64/AddMod/Program.lean`) is the
-- 30-instruction prologue that folds `a + b` (mod 2^256) into the second
-- EVM stack slot, leaving the 257th carry-out bit in scratch register `x5`.
-- Per `Evm64/AddMod/Program.lean`, `evm_addmod_prologue := evm_add`, so the
-- spec is a thin wrapper around `evm_add_spec_within` /
-- `evm_add_stack_spec_within` (Evm64/Add/Spec.lean §1, §2).

abbrev evm_addmod_prologue_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_addmod_prologue

/-- Register/memory-level prologue spec: thin lift of `evm_add_spec_within`
    through the `evm_addmod_prologue := evm_add` alias. -/
theorem evm_addmod_prologue_spec_within (sp : Word) (base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (v7 v6 v5 v11 : Word) :
    let sum0 := a0 + b0
    let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
    let psum1 := a1 + b1
    let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
    let carry1 := carry1a ||| carry1b
    let psum2 := a2 + b2
    let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
    let carry2 := carry2a ||| carry2b
    let psum3 := a3 + b3
    let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
    let result3 := psum3 + carry2
    let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
    let carry3 := carry3a ||| carry3b
    let code := evm_addmod_prologue_code base
    cpsTripleWithin 30 base (base + 120) code
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) **
       (.x5 ↦ᵣ carry3) ** (.x11 ↦ᵣ carry3a) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ sum0) ** ((sp + 40) ↦ₘ result1) ** ((sp + 48) ↦ₘ result2) **
       ((sp + 56) ↦ₘ result3)) := by
  -- `evm_addmod_prologue` is definitionally `evm_add`, so the codes coincide.
  show cpsTripleWithin 30 base (base + 120) (evm_add_code base) _ _
  exact evm_add_spec_within sp base a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 v5 v11

/-- Bundled postcondition for `evm_addmod_prologue_spec_within` (register/memory level).
    Hides 18 carry-chain let-bindings. -/
@[irreducible]
def evmAddModPrologueLimbPost (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let sum0 := a0 + b0
  let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
  let psum1 := a1 + b1
  let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
  let result1 := psum1 + carry0
  let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
  let carry1 := carry1a ||| carry1b
  let psum2 := a2 + b2
  let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
  let result2 := psum2 + carry1
  let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
  let carry2 := carry2a ||| carry2b
  let psum3 := a3 + b3
  let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
  let result3 := psum3 + carry2
  let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
  let carry3 := carry3a ||| carry3b
  (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) **
  (.x5 ↦ᵣ carry3) ** (.x11 ↦ᵣ carry3a) **
  (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + 32) ↦ₘ sum0) ** ((sp + 40) ↦ₘ result1) ** ((sp + 48) ↦ₘ result2) **
  ((sp + 56) ↦ₘ result3)

theorem evmAddModPrologueLimbPost_unfold (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    evmAddModPrologueLimbPost sp a0 a1 a2 a3 b0 b1 b2 b3 =
      (let sum0 := a0 + b0
       let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
       let psum1 := a1 + b1
       let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
       let result1 := psum1 + carry0
       let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
       let carry1 := carry1a ||| carry1b
       let psum2 := a2 + b2
       let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
       let result2 := psum2 + carry1
       let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
       let carry2 := carry2a ||| carry2b
       let psum3 := a3 + b3
       let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
       let result3 := psum3 + carry2
       let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
       let carry3 := carry3a ||| carry3b
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) **
       (.x5 ↦ᵣ carry3) ** (.x11 ↦ᵣ carry3a) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ sum0) ** ((sp + 40) ↦ₘ result1) ** ((sp + 48) ↦ₘ result2) **
       ((sp + 56) ↦ₘ result3)) := by
  delta evmAddModPrologueLimbPost; rfl

theorem evm_addmod_prologue_named_spec_within (sp : Word) (base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (v7 v6 v5 v11 : Word) :
    cpsTripleWithin 30 base (base + 120) (evm_addmod_prologue_code base)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (evmAddModPrologueLimbPost sp a0 a1 a2 a3 b0 b1 b2 b3) :=
  cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by simp only [evmAddModPrologueLimbPost_unfold]; exact hp)
    (evm_addmod_prologue_spec_within sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 v5 v11)

/-- Stack-level prologue spec on `evmWordIs` surface: thin lift of
    `evm_add_stack_spec_within`. -/
theorem evm_addmod_prologue_stack_spec_within (sp base : Word)
    (a b : EvmWord) (v7 v6 v5 v11 : Word) :
    let a0 := a.getLimbN 0; let b0 := b.getLimbN 0
    let a1 := a.getLimbN 1; let b1 := b.getLimbN 1
    let a2 := a.getLimbN 2; let b2 := b.getLimbN 2
    let a3 := a.getLimbN 3; let b3 := b.getLimbN 3
    let sum0 := a0 + b0
    let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
    let psum1 := a1 + b1
    let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
    let carry1 := carry1a ||| carry1b
    let psum2 := a2 + b2
    let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
    let carry2 := carry2a ||| carry2b
    let psum3 := a3 + b3
    let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
    let result3 := psum3 + carry2
    let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
    let carry3 := carry3a ||| carry3b
    let code := evm_addmod_prologue_code base
    cpsTripleWithin 30 base (base + 120) code
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) **
       (.x5 ↦ᵣ carry3) ** (.x11 ↦ᵣ carry3a) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a + b)) := by
  show cpsTripleWithin 30 base (base + 120) (evm_add_code base) _ _
  exact evm_add_stack_spec_within sp base a b v7 v6 v5 v11

/-- Bundled postcondition for `evm_addmod_prologue_stack_spec_within`.
    Hides all 22 limb-extraction and carry-chain lets. -/
@[irreducible]
def evmAddModPrologueStackPost (sp : Word) (a b : EvmWord) : Assertion :=
  let a0 := a.getLimbN 0; let b0 := b.getLimbN 0
  let a1 := a.getLimbN 1; let b1 := b.getLimbN 1
  let a2 := a.getLimbN 2; let b2 := b.getLimbN 2
  let a3 := a.getLimbN 3; let b3 := b.getLimbN 3
  let sum0 := a0 + b0
  let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
  let psum1 := a1 + b1
  let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
  let result1 := psum1 + carry0
  let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
  let carry1 := carry1a ||| carry1b
  let psum2 := a2 + b2
  let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
  let result2 := psum2 + carry1
  let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
  let carry2 := carry2a ||| carry2b
  let psum3 := a3 + b3
  let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
  let result3 := psum3 + carry2
  let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
  let carry3 := carry3a ||| carry3b
  (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) **
  (.x5 ↦ᵣ carry3) ** (.x11 ↦ᵣ carry3a) **
  evmWordIs sp a ** evmWordIs (sp + 32) (a + b)

theorem evmAddModPrologueStackPost_unfold (sp : Word) (a b : EvmWord) :
    evmAddModPrologueStackPost sp a b =
      (let a0 := a.getLimbN 0; let b0 := b.getLimbN 0
       let a1 := a.getLimbN 1; let b1 := b.getLimbN 1
       let a2 := a.getLimbN 2; let b2 := b.getLimbN 2
       let a3 := a.getLimbN 3; let b3 := b.getLimbN 3
       let sum0 := a0 + b0
       let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
       let psum1 := a1 + b1
       let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
       let result1 := psum1 + carry0
       let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
       let carry1 := carry1a ||| carry1b
       let psum2 := a2 + b2
       let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
       let result2 := psum2 + carry1
       let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
       let carry2 := carry2a ||| carry2b
       let psum3 := a3 + b3
       let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
       let result3 := psum3 + carry2
       let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
       let carry3 := carry3a ||| carry3b
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) **
       (.x5 ↦ᵣ carry3) ** (.x11 ↦ᵣ carry3a) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a + b)) := by
  delta evmAddModPrologueStackPost; rfl

theorem evm_addmod_prologue_stack_named_spec_within (sp base : Word)
    (a b : EvmWord) (v7 v6 v5 v11 : Word) :
    cpsTripleWithin 30 base (base + 120) (evm_addmod_prologue_code base)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      (evmAddModPrologueStackPost sp a b) :=
  cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by simp only [evmAddModPrologueStackPost_unfold]; exact hp)
    (evm_addmod_prologue_stack_spec_within sp base a b v7 v6 v5 v11)

-- ============================================================================
-- evm_addmod_epilogue (1 instruction, slice evm-asm-hsybl toward evm-asm-s7v49)
-- ============================================================================
--
-- `evm_addmod_epilogue` (defined in `Evm64/AddMod/Program.lean`) is the
-- single-instruction `ADDI x12 x12 32` block that performs the final
-- EVM stack-pointer advance after the result limbs have been written
-- by the upstream phase blocks. Mirrors the shape of
-- `exp_loop_pointer_advance_spec_within` (Exp/LimbSpec.lean §4.5):
-- a `CodeReq.ofProg → singleton` rewrite plus `addi_spec_gen_same_within`.

abbrev evm_addmod_epilogue_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_addmod_epilogue

theorem evm_addmod_epilogue_spec_within
    (vOld : Word) (base : Word) :
    let code := evm_addmod_epilogue_code base
    cpsTripleWithin 1 base (base + 4) code
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 (32 : BitVec 12))) := by
  show cpsTripleWithin 1 base (base + 4)
    (CodeReq.ofProg base evm_addmod_epilogue) _ _
  rw [show CodeReq.ofProg base evm_addmod_epilogue =
      CodeReq.singleton base (.ADDI .x12 .x12 32) from CodeReq.ofProg_singleton]
  exact addi_spec_gen_same_within .x12 vOld 32 base (by nofun)

-- ============================================================================
-- evm_addmod_phase1_carry (1 instruction, slice evm-asm-ot10w toward
-- evm-asm-s7v49)
-- ============================================================================
--
-- `evm_addmod_phase1_carry` (defined in `Evm64/AddMod/Program.lean`) is the
-- single-instruction `ADDI x7 x5 0` block — a register `MV` that copies the
-- 257th carry bit from `x5` into `x7`, freeing `x5` for the modulus-reduction
-- phase that follows. Mirrors the shape of `addi_spec_gen_within`: a
-- `CodeReq.ofProg → singleton` rewrite plus `addi_spec_gen_within` with
-- `imm = 0`.
--
-- Note: post-state register value is `v5 + signExtend12 (0 : BitVec 12)` (the
-- raw shape produced by `addi_spec_gen_within`); downstream callers normalize
-- via `BitVec.add_zero` / `signExtend12` simp lemmas as needed.

abbrev evm_addmod_phase1_carry_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_addmod_phase1_carry

theorem evm_addmod_phase1_carry_spec_within
    (v5 vOld : Word) (base : Word) :
    let code := evm_addmod_phase1_carry_code base
    cpsTripleWithin 1 base (base + 4) code
      ((.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ vOld))
      ((.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ (v5 + signExtend12 (0 : BitVec 12)))) := by
  show cpsTripleWithin 1 base (base + 4)
    (CodeReq.ofProg base evm_addmod_phase1_carry) _ _
  rw [show CodeReq.ofProg base evm_addmod_phase1_carry =
      CodeReq.singleton base (.ADDI .x7 .x5 0) from CodeReq.ofProg_singleton]
  exact addi_spec_gen_within .x7 .x5 vOld v5 0 base (by nofun)

-- ============================================================================
-- evm_addmod_phase2_zero_path (4 instructions, slice evm-asm-eu2hw toward
-- evm-asm-s7v49)
-- ============================================================================
--
-- `evm_addmod_phase2_zero_path` (defined in `Evm64/AddMod/Program.lean`) is the
-- 4-instruction `SD x12, x0, {32,40,48,56}` block that writes zeros into the
-- four result limbs at `x12 + 32 .. 56` on the `N = 0` path. Direct analog
-- of the SD chain at the end of `exp_prologue_spec_within`
-- (`Exp/LimbSpec.lean §5`): four `sd_x0_spec_gen_within` applications glued
-- by `runBlock`. Block layout:
--
--   instr  0 (byte  0) :  SD x12, x0, 32   -- result limb 0 := 0
--   instr  1 (byte  4) :  SD x12, x0, 40   -- result limb 1 := 0
--   instr  2 (byte  8) :  SD x12, x0, 48   -- result limb 2 := 0
--   instr  3 (byte 12) :  SD x12, x0, 56   -- result limb 3 := 0

abbrev evm_addmod_phase2_zero_path_code (base : Word) : CodeReq :=
  (CodeReq.singleton base (.SD .x12 .x0 32)).union
    ((CodeReq.singleton (base + 4) (.SD .x12 .x0 40)).union
      ((CodeReq.singleton (base + 8) (.SD .x12 .x0 48)).union
        (CodeReq.singleton (base + 12) (.SD .x12 .x0 56))))

theorem evm_addmod_phase2_zero_path_code_eq_ofProg (base : Word) :
    evm_addmod_phase2_zero_path_code base =
      CodeReq.ofProg base evm_addmod_phase2_zero_path := by
  unfold evm_addmod_phase2_zero_path_code evm_addmod_phase2_zero_path SD single seq
  change _ = CodeReq.ofProg base
    [.SD .x12 .x0 32, .SD .x12 .x0 40, .SD .x12 .x0 48, .SD .x12 .x0 56]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_singleton]
  bv_addr

/-- Register/memory-level zero-store spec: writes `0` into the four result
    limbs at `x12 + 32 .. 56` via `SD x12, x0, k`. Mirrors the SD chain in
    `exp_prologue_spec_within`. -/
theorem evm_addmod_phase2_zero_path_spec_within
    (sp m0 m1 m2 m3 : Word) (base : Word) :
    let code := evm_addmod_phase2_zero_path_code base
    cpsTripleWithin 4 base (base + 16) code
      ((.x12 ↦ᵣ sp) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ m3))
      ((.x12 ↦ᵣ sp) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ (0 : Word))) := by
  unfold evm_addmod_phase2_zero_path_code
  have hSd0 := generic_sd_x0_spec_within .x12 sp m0
    (32 : BitVec 12) base
  have hSd1 := generic_sd_x0_spec_within .x12 sp m1
    (40 : BitVec 12) (base + 4)
  have hSd2 := generic_sd_x0_spec_within .x12 sp m2
    (48 : BitVec 12) (base + 8)
  have hSd3 := generic_sd_x0_spec_within .x12 sp m3
    (56 : BitVec 12) (base + 12)
  runBlock hSd0 hSd1 hSd2 hSd3

/-- `ofProg`-flavoured zero-store spec: thin lift of
    `evm_addmod_phase2_zero_path_spec_within` through
    `evm_addmod_phase2_zero_path_code_eq_ofProg`. -/
theorem evm_addmod_phase2_zero_path_ofProg_spec_within
    (sp m0 m1 m2 m3 : Word) (base : Word) :
    cpsTripleWithin 4 base (base + 16)
      (CodeReq.ofProg base evm_addmod_phase2_zero_path)
      ((.x12 ↦ᵣ sp) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ m3))
      ((.x12 ↦ᵣ sp) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ (0 : Word))) := by
  rw [← evm_addmod_phase2_zero_path_code_eq_ofProg]
  exact evm_addmod_phase2_zero_path_spec_within sp m0 m1 m2 m3 base

-- ============================================================================
-- evm_addmod_phase2_reduce (1 instruction, slice evm-asm-dg16y toward
-- evm-asm-s7v49)
-- ============================================================================
--
-- `evm_addmod_phase2_reduce modOff` (defined in `Evm64/AddMod/Program.lean`)
-- is the single-instruction `JAL .x1 modOff` block that performs the
-- modulus-reduction near-call to `evm_mod_callable`. The signed 21-bit
-- byte offset `modOff` is the distance from this JAL site to the entry
-- of `evm_mod_callable`; the concrete numeric value is pinned by the
-- surrounding caller frame.
--
-- The cpsTriple shape is identical to `exp_square_block_spec_within`
-- (Exp/LimbSpec.lean §2): a single `JAL .x1 mulOff` near-call. Argument
-- marshalling and post-call result handling are *not* part of this leaf
-- cpsTriple — they live in the surrounding compose layer in slice 3d
-- (`evm-asm-s7v49`) once the runtime branch shape stabilises.

abbrev evm_addmod_phase2_reduce_code (base : Word) (modOff : BitVec 21) :
    CodeReq :=
  CodeReq.ofProg base (evm_addmod_phase2_reduce modOff)

/-- Register-level spec for the `evm_addmod_phase2_reduce` block: a single
    near-`JAL` invoking `evm_mod_callable`. Mirrors
    `exp_square_block_spec_within` (Exp/LimbSpec.lean §2). -/
theorem evm_addmod_phase2_reduce_spec_within
    (modOff : BitVec 21) (vOld : Word) (base : Word) :
    let code := evm_addmod_phase2_reduce_code base modOff
    cpsTripleWithin 1 base (base + signExtend21 modOff) code
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ (base + 4)) := by
  show cpsTripleWithin 1 base (base + signExtend21 modOff)
    (CodeReq.ofProg base (evm_addmod_phase2_reduce modOff)) _ _
  rw [show CodeReq.ofProg base (evm_addmod_phase2_reduce modOff) =
      CodeReq.singleton base (.JAL .x1 modOff) from CodeReq.ofProg_singleton]
  exact jal_spec_within .x1 vOld modOff base (by nofun)

-- ============================================================================
-- evm_addmod_phase2_n_zero_test (8 instructions, slice evm-asm-17ns9 toward
-- evm-asm-s7v49)
-- ============================================================================
--
-- `evm_addmod_phase2_n_zero_test skipOff` (defined in
-- `Evm64/AddMod/Program.lean`) is the 8-instruction OR-fold + BEQ block
-- that checks whether the modulus operand `N` (the 256-bit word at
-- `x12 + 32 .. 56`) is identically zero. Block layout:
--
--   instr 0 (byte  0) :  LD  x6, x12, 32   -- N limb 0 → x6
--   instr 1 (byte  4) :  LD  x5, x12, 40   -- N limb 1 → x5
--   instr 2 (byte  8) :  OR  x6, x6, x5    -- x6 ← N0 ∨ N1
--   instr 3 (byte 12) :  LD  x5, x12, 48   -- N limb 2 → x5
--   instr 4 (byte 16) :  OR  x6, x6, x5    -- x6 ← N0 ∨ N1 ∨ N2
--   instr 5 (byte 20) :  LD  x5, x12, 56   -- N limb 3 → x5
--   instr 6 (byte 24) :  OR  x6, x6, x5    -- x6 ← orAll
--   instr 7 (byte 28) :  BEQ x6, x0, skipOff
--
-- Branches:
--   * Taken     (`orAll = 0`): pc = `(base + 28) + signExtend13 skipOff`,
--     dispatching to `evm_addmod_phase2_zero_path`.
--   * Fall-through (`orAll ≠ 0`): pc = `base + 32`, continues to the
--     modulus-reduction phase.
--
-- The cpsBranchWithin shape mirrors `divK_div128_phase2b_guard_spec_within`
-- (DivMod/LimbSpec/Div128ProdCheck2.lean §Phase 2b guard).

abbrev evm_addmod_phase2_n_zero_test_code (base : Word) (skipOff : BitVec 13) :
    CodeReq :=
  CodeReq.ofProg base (evm_addmod_phase2_n_zero_test skipOff)

theorem evm_addmod_phase2_n_zero_test_code_eq_unfold
    (base : Word) (skipOff : BitVec 13) :
    evm_addmod_phase2_n_zero_test_code base skipOff =
      (CodeReq.singleton base (.LD .x6 .x12 32)).union
        ((CodeReq.singleton (base + 4) (.LD .x5 .x12 40)).union
          ((CodeReq.singleton (base + 8) (.OR .x6 .x6 .x5)).union
            ((CodeReq.singleton (base + 12) (.LD .x5 .x12 48)).union
              ((CodeReq.singleton (base + 16) (.OR .x6 .x6 .x5)).union
                ((CodeReq.singleton (base + 20) (.LD .x5 .x12 56)).union
                  ((CodeReq.singleton (base + 24) (.OR .x6 .x6 .x5)).union
                    (CodeReq.singleton (base + 28)
                      (.BEQ .x6 .x0 skipOff)))))))) := by
  unfold evm_addmod_phase2_n_zero_test_code evm_addmod_phase2_n_zero_test
    LD OR' single seq
  change CodeReq.ofProg base
    [.LD .x6 .x12 32, .LD .x5 .x12 40, .OR .x6 .x6 .x5,
     .LD .x5 .x12 48, .OR .x6 .x6 .x5,
     .LD .x5 .x12 56, .OR .x6 .x6 .x5,
     .BEQ .x6 .x0 skipOff] = _
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  bv_addr

/-- Register/memory-level n-zero-test branch spec: OR-folds the four
    `N` limbs at `x12 + 32 .. 56` into `x6`, then dispatches via `BEQ x6, x0`.
    The `skipOff` argument is the byte offset (relative to the BEQ at
    `base + 28`) of the `evm_addmod_phase2_zero_path` entry; the concrete
    numeric value is pinned by the surrounding caller frame. -/
theorem evm_addmod_phase2_n_zero_test_spec_within
    (sp v5Old v6Old n0 n1 n2 n3 : Word)
    (base : Word) (skipOff : BitVec 13) :
    let orAll := n0 ||| n1 ||| n2 ||| n3
    let code := evm_addmod_phase2_n_zero_test_code base skipOff
    cpsBranchWithin 8 base code
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3))
      ((base + 28) + signExtend13 skipOff)
        ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ orAll) ** (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
         ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
         ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
         ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
         ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
         ⌜orAll = 0⌝)
      (base + 32)
        ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ orAll) ** (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
         ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
         ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
         ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
         ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
         ⌜orAll ≠ 0⌝) := by
  intro orAll code
  -- Build the 7-instruction OR-fold prefix as a cpsTripleWithin over the
  -- full 8-instruction cr (runBlock auto-extends each per-instr spec).
  have hOrFold :
      cpsTripleWithin 7 base (base + 28) code
        ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
         ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
         ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
         ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
         ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3))
        ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ orAll) ** (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
         ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
         ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
         ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
         ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3)) := by
    have L0 := ld_spec_gen_within .x6 .x12 sp v6Old n0
      (32 : BitVec 12) base (by nofun)
    have L1 := ld_spec_gen_within .x5 .x12 sp v5Old n1
      (40 : BitVec 12) (base + 4) (by nofun)
    have O1 := or_spec_gen_rd_eq_rs1_within .x6 .x5 n0 n1
      (base + 8) (by nofun)
    have L2 := ld_spec_gen_within .x5 .x12 sp n1 n2
      (48 : BitVec 12) (base + 12) (by nofun)
    have O2 := or_spec_gen_rd_eq_rs1_within .x6 .x5 (n0 ||| n1) n2
      (base + 16) (by nofun)
    have L3 := ld_spec_gen_within .x5 .x12 sp n2 n3
      (56 : BitVec 12) (base + 20) (by nofun)
    have O3 := or_spec_gen_rd_eq_rs1_within .x6 .x5 (n0 ||| n1 ||| n2) n3
      (base + 24) (by nofun)
    runBlock L0 L1 O1 L2 O2 L3 O3
  -- BEQ x6 x0 skipOff at base + 28
  have hBeq_raw := beq_spec_gen_within .x6 .x0 skipOff orAll (0 : Word)
    (base + 28)
  have hBeq_ext : cpsBranchWithin 1 (base + 28) code
      ((.x6 ↦ᵣ orAll) ** (.x0 ↦ᵣ 0))
      ((base + 28) + signExtend13 skipOff)
        ((.x6 ↦ᵣ orAll) ** (.x0 ↦ᵣ 0) ** ⌜orAll = (0 : Word)⌝)
      ((base + 28) + 4)
        ((.x6 ↦ᵣ orAll) ** (.x0 ↦ᵣ 0) ** ⌜orAll ≠ (0 : Word)⌝) :=
    cpsBranchWithin_extend_code (h := hBeq_raw) (hmono := by
      intro a i hsing
      show code a = some i
      rw [show code = evm_addmod_phase2_n_zero_test_code base skipOff from rfl,
        evm_addmod_phase2_n_zero_test_code_eq_unfold]
      simp only [CodeReq.singleton] at hsing
      split at hsing
      · rename_i ha
        rw [beq_iff_eq] at ha
        subst ha
        simp only [CodeReq.union, CodeReq.singleton]
        have h1 : (base + 28 : Word) ≠ base := by bv_omega
        have h2 : (base + 28 : Word) ≠ base + 4 := by bv_omega
        have h3 : (base + 28 : Word) ≠ base + 8 := by bv_omega
        have h4 : (base + 28 : Word) ≠ base + 12 := by bv_omega
        have h5 : (base + 28 : Word) ≠ base + 16 := by bv_omega
        have h6 : (base + 28 : Word) ≠ base + 20 := by bv_omega
        have h7 : (base + 28 : Word) ≠ base + 24 := by bv_omega
        simp at hsing ⊢
        exact hsing
      · simp at hsing)
  -- Frame the BEQ with the rest of the state (regs + four memory cells).
  have hBeq_framed := cpsBranchWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n3) **
     ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
     ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
     ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
     ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3))
    (by pcFree) hBeq_ext
  -- Compose OR-fold (cpsTripleWithin) + BEQ (cpsBranchWithin).
  have composed := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hOrFold hBeq_framed
  -- 7 + 1 = 8 step bound; (base + 28) + 4 = base + 32.
  have h_addr_eq : (base + 28 : Word) + 4 = base + 32 := by bv_addr
  rw [h_addr_eq] at composed
  exact cpsBranchWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    composed

-- ============================================================================
-- evm_addmod_pow256_prepare_minus_one_mod_args
-- ============================================================================

abbrev evm_addmod_pow256_prepare_minus_one_mod_args_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_addmod_pow256_prepare_minus_one_mod_args

@[irreducible]
def evmAddModPow256PrepareMinusOnePre (sp : Word)
    (x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ x5Old) **
  ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
  ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
  ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
  ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ w0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ w1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ w2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ w3) **
  ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ u0) **
  ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ u1) **
  ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ u2) **
  ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ u3)

theorem evmAddModPow256PrepareMinusOnePre_unfold
    (sp : Word)
    (x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 : Word) :
    evmAddModPow256PrepareMinusOnePre sp
      x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 =
      ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ x5Old) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ w0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ w1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ w2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ w3) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ u0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ u1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ u2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ u3)) := by
  delta evmAddModPow256PrepareMinusOnePre
  rfl

@[irreducible]
def evmAddModPow256PrepareMinusOnePost (sp : Word)
    (n0 n1 n2 n3 : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ n3) **
  ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
  ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
  ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
  ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
  ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
  ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
  ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
  ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)

theorem evmAddModPow256PrepareMinusOnePost_unfold
    (sp : Word) (n0 n1 n2 n3 : Word) :
    evmAddModPow256PrepareMinusOnePost sp n0 n1 n2 n3 =
      ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ n3) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)) := by
  delta evmAddModPow256PrepareMinusOnePost
  rfl

/-- Initialize the overflow-helper MOD-call dividend fill value by
    materializing the all-ones 12-bit immediate in register x5. -/
theorem evm_addmod_pow256_prepare_minus_one_mod_args_init_spec_within
    (base x5Old : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.ADDI .x5 .x0 (4095 : BitVec 12)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ x5Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ signExtend12 (4095 : BitVec 12))) := by
  exact addi_x0_spec_gen_within .x5 x5Old 4095 base (by nofun)

def evm_addmod_pow256_prepare_minus_one_mod_args_tail : Program :=
  SD .x12 .x5 64 ;;
  SD .x12 .x5 72 ;;
  SD .x12 .x5 80 ;;
  SD .x12 .x5 88 ;;
  LD .x5 .x12 32 ;;
  SD .x12 .x5 96 ;;
  LD .x5 .x12 40 ;;
  SD .x12 .x5 104 ;;
  LD .x5 .x12 48 ;;
  SD .x12 .x5 112 ;;
  LD .x5 .x12 56 ;;
  SD .x12 .x5 120

abbrev evm_addmod_pow256_prepare_minus_one_mod_args_tail_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_addmod_pow256_prepare_minus_one_mod_args_tail

@[irreducible]
def evmAddModPow256PrepareMinusOneTailPre (sp fill : Word)
    (n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ fill) **
  ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
  ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
  ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
  ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ w0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ w1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ w2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ w3) **
  ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ u0) **
  ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ u1) **
  ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ u2) **
  ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ u3)

theorem evmAddModPow256PrepareMinusOneTailPre_unfold
    (sp fill : Word) (n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 : Word) :
    evmAddModPow256PrepareMinusOneTailPre sp fill
      n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 =
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ fill) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ w0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ w1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ w2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ w3) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ u0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ u1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ u2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ u3)) := by
  delta evmAddModPow256PrepareMinusOneTailPre
  rfl

@[irreducible]
def evmAddModPow256PrepareMinusOneTailPost (sp fill : Word)
    (n0 n1 n2 n3 : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n3) **
  ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
  ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
  ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
  ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
  ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
  ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
  ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)

theorem evmAddModPow256PrepareMinusOneTailPost_unfold
    (sp fill : Word) (n0 n1 n2 n3 : Word) :
    evmAddModPow256PrepareMinusOneTailPost sp fill n0 n1 n2 n3 =
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n3) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)) := by
  delta evmAddModPow256PrepareMinusOneTailPost
  rfl

abbrev evm_addmod_pow256_prepare_minus_one_mod_args_tail_store_prefix_code
    (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.SD .x12 .x5 (64 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SD .x12 .x5 (72 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SD .x12 .x5 (80 : BitVec 12)))
   (CodeReq.singleton (base + 12) (.SD .x12 .x5 (88 : BitVec 12)))))

abbrev evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy0_prefix_code
    (base : Word) : CodeReq :=
  CodeReq.union (evm_addmod_pow256_prepare_minus_one_mod_args_tail_store_prefix_code base)
  (CodeReq.union (CodeReq.singleton (base + 16) (.LD .x5 .x12 (32 : BitVec 12)))
   (CodeReq.singleton (base + 20) (.SD .x12 .x5 (96 : BitVec 12))))

abbrev evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy1_prefix_code
    (base : Word) : CodeReq :=
  CodeReq.union (evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy0_prefix_code base)
  (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x5 .x12 (40 : BitVec 12)))
   (CodeReq.singleton (base + 28) (.SD .x12 .x5 (104 : BitVec 12))))

abbrev evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy2_prefix_code
    (base : Word) : CodeReq :=
  CodeReq.union (evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy1_prefix_code base)
  (CodeReq.union (CodeReq.singleton (base + 32) (.LD .x5 .x12 (48 : BitVec 12)))
   (CodeReq.singleton (base + 36) (.SD .x12 .x5 (112 : BitVec 12))))

abbrev evm_addmod_pow256_prepare_minus_one_mod_args_tail_full_code
    (base : Word) : CodeReq :=
  CodeReq.union (evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy2_prefix_code base)
  (CodeReq.union (CodeReq.singleton (base + 40) (.LD .x5 .x12 (56 : BitVec 12)))
   (CodeReq.singleton (base + 44) (.SD .x12 .x5 (120 : BitVec 12))))

@[irreducible]
def evmAddModPow256PrepareMinusOneTailStorePrefixPost (sp fill : Word)
    (n0 n1 n2 n3 u0 u1 u2 u3 : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ fill) **
  ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
  ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
  ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
  ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ u0) **
  ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ u1) **
  ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ u2) **
  ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ u3)

@[irreducible]
def evmAddModPow256PrepareMinusOneTailCopy0PrefixPost (sp fill : Word)
    (n0 n1 n2 n3 u1 u2 u3 : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n0) **
  ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
  ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
  ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
  ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
  ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ u1) **
  ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ u2) **
  ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ u3)

@[irreducible]
def evmAddModPow256PrepareMinusOneTailCopy1PrefixPost (sp fill : Word)
    (n0 n1 n2 n3 u2 u3 : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n1) **
  ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
  ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
  ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
  ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
  ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
  ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ u2) **
  ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ u3)

@[irreducible]
def evmAddModPow256PrepareMinusOneTailCopy2PrefixPost (sp fill : Word)
    (n0 n1 n2 n3 u3 : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n2) **
  ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
  ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
  ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
  ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ fill) **
  ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
  ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
  ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
  ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ u3)

theorem evmAddModPow256PrepareMinusOneTailCopy2PrefixPost_unfold
    (sp fill : Word) (n0 n1 n2 n3 u3 : Word) :
    evmAddModPow256PrepareMinusOneTailCopy2PrefixPost sp fill
        n0 n1 n2 n3 u3 =
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n2) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ u3)) := by
  delta evmAddModPow256PrepareMinusOneTailCopy2PrefixPost
  rfl

theorem evmAddModPow256PrepareMinusOneTailCopy1PrefixPost_unfold
    (sp fill : Word) (n0 n1 n2 n3 u2 u3 : Word) :
    evmAddModPow256PrepareMinusOneTailCopy1PrefixPost sp fill
        n0 n1 n2 n3 u2 u3 =
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n1) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ u2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ u3)) := by
  delta evmAddModPow256PrepareMinusOneTailCopy1PrefixPost
  rfl

theorem evmAddModPow256PrepareMinusOneTailCopy0PrefixPost_unfold
    (sp fill : Word) (n0 n1 n2 n3 u1 u2 u3 : Word) :
    evmAddModPow256PrepareMinusOneTailCopy0PrefixPost sp fill
        n0 n1 n2 n3 u1 u2 u3 =
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n0) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ u1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ u2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ u3)) := by
  delta evmAddModPow256PrepareMinusOneTailCopy0PrefixPost
  rfl

theorem evmAddModPow256PrepareMinusOneTailStorePrefixPost_unfold
    (sp fill : Word) (n0 n1 n2 n3 u0 u1 u2 u3 : Word) :
    evmAddModPow256PrepareMinusOneTailStorePrefixPost sp fill
        n0 n1 n2 n3 u0 u1 u2 u3 =
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ fill) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ fill) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ u0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ u1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ u2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ u3)) := by
  delta evmAddModPow256PrepareMinusOneTailStorePrefixPost
  rfl

/-- First store of the overflow-helper MOD-call setup tail. This is a
    reusable building block for the later composed tail proof. -/
theorem evm_addmod_pow256_prepare_minus_one_mod_args_tail_store0_spec_within
    (sp fill base w0 : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SD .x12 .x5 (64 : BitVec 12)))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ fill) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ w0))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ fill) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ fill)) := by
  exact sd_spec_gen_within .x12 .x5 sp fill w0 64 base

/-- Second store of the overflow-helper MOD-call setup tail. -/
theorem evm_addmod_pow256_prepare_minus_one_mod_args_tail_store1_spec_within
    (sp fill base w1 : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SD .x12 .x5 (72 : BitVec 12)))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ fill) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ w1))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ fill) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ fill)) := by
  exact sd_spec_gen_within .x12 .x5 sp fill w1 72 base

/-- Third store of the overflow-helper MOD-call setup tail. -/
theorem evm_addmod_pow256_prepare_minus_one_mod_args_tail_store2_spec_within
    (sp fill base w2 : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SD .x12 .x5 (80 : BitVec 12)))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ fill) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ w2))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ fill) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ fill)) := by
  exact sd_spec_gen_within .x12 .x5 sp fill w2 80 base

/-- Fourth store of the overflow-helper MOD-call setup tail. -/
theorem evm_addmod_pow256_prepare_minus_one_mod_args_tail_store3_spec_within
    (sp fill base w3 : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SD .x12 .x5 (88 : BitVec 12)))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ fill) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ w3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ fill) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ fill)) := by
  exact sd_spec_gen_within .x12 .x5 sp fill w3 88 base

/-- Compose the four stores that fill the overflow-helper dividend window. -/
theorem evm_addmod_pow256_prepare_minus_one_mod_args_tail_store_prefix_spec_within
    (sp fill base : Word) (n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 : Word) :
    cpsTripleWithin 4 base (base + 16)
      (evm_addmod_pow256_prepare_minus_one_mod_args_tail_store_prefix_code base)
      (evmAddModPow256PrepareMinusOneTailPre sp fill
        n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3)
      (evmAddModPow256PrepareMinusOneTailStorePrefixPost sp fill
        n0 n1 n2 n3 u0 u1 u2 u3) := by
  rw [evmAddModPow256PrepareMinusOneTailPre_unfold,
      evmAddModPow256PrepareMinusOneTailStorePrefixPost_unfold]
  have S0 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store0_spec_within
    sp fill base w0
  have S1 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store1_spec_within
    sp fill (base + 4) w1
  have S2 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store2_spec_within
    sp fill (base + 8) w2
  have S3 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store3_spec_within
    sp fill (base + 12) w3
  runBlock S0 S1 S2 S3

/-- Load the low modulus limb while preparing the first overflow-helper MOD call. -/
theorem evm_addmod_pow256_prepare_minus_one_mod_args_tail_load0_spec_within
    (sp fill base n0 : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LD .x5 .x12 (32 : BitVec 12)))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ fill) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n0) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0)) := by
  exact ld_spec_gen_within .x5 .x12 sp fill n0 32 base (by nofun)

/-- Store the low modulus limb into the callable MOD divisor window. -/
theorem evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy0_spec_within
    (sp base n0 u0 : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SD .x12 .x5 (96 : BitVec 12)))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n0) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ u0))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n0) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0)) := by
  exact sd_spec_gen_within .x12 .x5 sp n0 u0 96 base

/-- Compose the dividend fill prefix and the low-modulus-limb copy. -/
theorem evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy0_prefix_spec_within
    (sp fill base : Word) (n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 : Word) :
    cpsTripleWithin 6 base (base + 24)
      (evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy0_prefix_code base)
      (evmAddModPow256PrepareMinusOneTailPre sp fill
        n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3)
      (evmAddModPow256PrepareMinusOneTailCopy0PrefixPost sp fill
        n0 n1 n2 n3 u1 u2 u3) := by
  rw [evmAddModPow256PrepareMinusOneTailPre_unfold,
      evmAddModPow256PrepareMinusOneTailCopy0PrefixPost_unfold]
  have S0 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store0_spec_within
    sp fill base w0
  have S1 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store1_spec_within
    sp fill (base + 4) w1
  have S2 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store2_spec_within
    sp fill (base + 8) w2
  have S3 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store3_spec_within
    sp fill (base + 12) w3
  have L0 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_load0_spec_within
    sp fill (base + 16) n0
  have C0 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy0_spec_within
    sp (base + 20) n0 u0
  runBlock S0 S1 S2 S3 L0 C0

/-- Load the second modulus limb while preparing the first overflow-helper MOD call. -/
theorem evm_addmod_pow256_prepare_minus_one_mod_args_tail_load1_spec_within
    (sp base n0 n1 : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LD .x5 .x12 (40 : BitVec 12)))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n1) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1)) := by
  exact ld_spec_gen_within .x5 .x12 sp n0 n1 40 base (by nofun)

/-- Store the second modulus limb into the callable MOD divisor window. -/
theorem evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy1_spec_within
    (sp base n1 u1 : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SD .x12 .x5 (104 : BitVec 12)))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n1) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ u1))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n1) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1)) := by
  exact sd_spec_gen_within .x12 .x5 sp n1 u1 104 base

/-- Compose through the second modulus-limb copy into the callable MOD divisor window. -/
theorem evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy1_prefix_spec_within
    (sp fill base : Word) (n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 : Word) :
    cpsTripleWithin 8 base (base + 32)
      (evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy1_prefix_code base)
      (evmAddModPow256PrepareMinusOneTailPre sp fill
        n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3)
      (evmAddModPow256PrepareMinusOneTailCopy1PrefixPost sp fill
        n0 n1 n2 n3 u2 u3) := by
  rw [evmAddModPow256PrepareMinusOneTailPre_unfold,
      evmAddModPow256PrepareMinusOneTailCopy1PrefixPost_unfold]
  have S0 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store0_spec_within
    sp fill base w0
  have S1 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store1_spec_within
    sp fill (base + 4) w1
  have S2 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store2_spec_within
    sp fill (base + 8) w2
  have S3 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store3_spec_within
    sp fill (base + 12) w3
  have L0 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_load0_spec_within
    sp fill (base + 16) n0
  have C0 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy0_spec_within
    sp (base + 20) n0 u0
  have L1 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_load1_spec_within
    sp (base + 24) n0 n1
  have C1 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy1_spec_within
    sp (base + 28) n1 u1
  runBlock S0 S1 S2 S3 L0 C0 L1 C1

/-- Load the third modulus limb while preparing the first overflow-helper MOD call. -/
theorem evm_addmod_pow256_prepare_minus_one_mod_args_tail_load2_spec_within
    (sp base n1 n2 : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LD .x5 .x12 (48 : BitVec 12)))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n2) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2)) := by
  exact ld_spec_gen_within .x5 .x12 sp n1 n2 48 base (by nofun)

/-- Store the third modulus limb into the callable MOD divisor window. -/
theorem evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy2_spec_within
    (sp base n2 u2 : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SD .x12 .x5 (112 : BitVec 12)))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n2) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ u2))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n2) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2)) := by
  exact sd_spec_gen_within .x12 .x5 sp n2 u2 112 base

/-- Compose through the third modulus-limb copy into the callable MOD divisor window. -/
theorem evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy2_prefix_spec_within
    (sp fill base : Word) (n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 : Word) :
    cpsTripleWithin 10 base (base + 40)
      (evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy2_prefix_code base)
      (evmAddModPow256PrepareMinusOneTailPre sp fill
        n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3)
      (evmAddModPow256PrepareMinusOneTailCopy2PrefixPost sp fill
        n0 n1 n2 n3 u3) := by
  rw [evmAddModPow256PrepareMinusOneTailPre_unfold,
      evmAddModPow256PrepareMinusOneTailCopy2PrefixPost_unfold]
  have S0 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store0_spec_within
    sp fill base w0
  have S1 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store1_spec_within
    sp fill (base + 4) w1
  have S2 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store2_spec_within
    sp fill (base + 8) w2
  have S3 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store3_spec_within
    sp fill (base + 12) w3
  have L0 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_load0_spec_within
    sp fill (base + 16) n0
  have C0 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy0_spec_within
    sp (base + 20) n0 u0
  have L1 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_load1_spec_within
    sp (base + 24) n0 n1
  have C1 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy1_spec_within
    sp (base + 28) n1 u1
  have L2 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_load2_spec_within
    sp (base + 32) n1 n2
  have C2 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy2_spec_within
    sp (base + 36) n2 u2
  runBlock S0 S1 S2 S3 L0 C0 L1 C1 L2 C2

/-- Load the high modulus limb while preparing the first overflow-helper MOD call. -/
theorem evm_addmod_pow256_prepare_minus_one_mod_args_tail_load3_spec_within
    (sp base n2 n3 : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LD .x5 .x12 (56 : BitVec 12)))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n3) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3)) := by
  exact ld_spec_gen_within .x5 .x12 sp n2 n3 56 base (by nofun)

/-- Store the high modulus limb into the callable MOD divisor window. -/
theorem evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy3_spec_within
    (sp base n3 u3 : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SD .x12 .x5 (120 : BitVec 12)))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n3) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ u3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n3) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)) := by
  exact sd_spec_gen_within .x12 .x5 sp n3 u3 120 base

/-- Compose the full tail that fills the overflow-helper dividend window and
    copies the modulus limbs into the callable MOD divisor window. -/
theorem evm_addmod_pow256_prepare_minus_one_mod_args_tail_full_spec_within
    (sp fill base : Word) (n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 : Word) :
    cpsTripleWithin 12 base (base + 48)
      (evm_addmod_pow256_prepare_minus_one_mod_args_tail_full_code base)
      (evmAddModPow256PrepareMinusOneTailPre sp fill
        n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3)
      (evmAddModPow256PrepareMinusOneTailPost sp fill n0 n1 n2 n3) := by
  rw [evmAddModPow256PrepareMinusOneTailPre_unfold,
      evmAddModPow256PrepareMinusOneTailPost_unfold]
  have S0 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store0_spec_within
    sp fill base w0
  have S1 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store1_spec_within
    sp fill (base + 4) w1
  have S2 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store2_spec_within
    sp fill (base + 8) w2
  have S3 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store3_spec_within
    sp fill (base + 12) w3
  have L0 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_load0_spec_within
    sp fill (base + 16) n0
  have C0 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy0_spec_within
    sp (base + 20) n0 u0
  have L1 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_load1_spec_within
    sp (base + 24) n0 n1
  have C1 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy1_spec_within
    sp (base + 28) n1 u1
  have L2 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_load2_spec_within
    sp (base + 32) n1 n2
  have C2 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy2_spec_within
    sp (base + 36) n2 u2
  have L3 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_load3_spec_within
    sp (base + 40) n2 n3
  have C3 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy3_spec_within
    sp (base + 44) n3 u3
  runBlock S0 S1 S2 S3 L0 C0 L1 C1 L2 C2 L3 C3

abbrev evm_addmod_pow256_call_mod_code (base : Word) (modOff : BitVec 21) : CodeReq :=
  CodeReq.ofProg base (evm_addmod_pow256_call_mod modOff)

abbrev evm_addmod_pow256_call_mod_enter_code (base : Word) (modOff : BitVec 21) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.ADDI .x12 .x12 (64 : BitVec 12)))
    (CodeReq.singleton (base + 4) (.JAL .x1 modOff))

/-- Enter the callable-MOD work window for the pow256 helper and jump to MOD. -/
theorem evm_addmod_pow256_call_mod_enter_spec_within
    (sp x1Old base : Word) (modOff : BitVec 21) :
    cpsTripleWithin 2 base ((base + 4) + signExtend21 modOff)
      (evm_addmod_pow256_call_mod_enter_code base modOff)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ x1Old))
      ((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) ** (.x1 ↦ᵣ ((base + 4) + 4))) := by
  have A := addi_spec_gen_same_within .x12 sp 64 base (by nofun)
  have J := jal_spec_within .x1 x1Old modOff (base + 4) (by nofun)
  have Jf := cpsTripleWithin_frameL
    (.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) (by pcFree) J
  runBlock A Jf

/-- Restore the ADDMOD frame pointer after a callable-MOD return. -/
theorem evm_addmod_pow256_call_mod_restore_spec_within
    (sp base : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.ADDI .x12 .x12 (4000 : BitVec 12)))
      (.x12 ↦ᵣ sp)
      (.x12 ↦ᵣ (sp + signExtend12 (4000 : BitVec 12))) := by
  exact addi_spec_gen_same_within .x12 sp 4000 base (by nofun)

-- ============================================================================
-- evm_addmod_pow256_prepare_plus_one_mod_args
-- ============================================================================

abbrev evm_addmod_pow256_prepare_plus_one_mod_args_low_prefix_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 (96 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.ADDI .x6 .x5 (1 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SLTIU .x7 .x6 (1 : BitVec 12)))
   (CodeReq.singleton (base + 12) (.SD .x12 .x6 (64 : BitVec 12)))))

/-- First four instructions of the plus-one MOD-call setup: load the low
    remainder limb, add one, compute the carry, and store the low dividend limb. -/
theorem evm_addmod_pow256_prepare_plus_one_mod_args_low_prefix_spec_within
    (sp base x5Old x6Old x7Old r0 w0 : Word) :
    cpsTripleWithin 4 base (base + 16)
      (evm_addmod_pow256_prepare_plus_one_mod_args_low_prefix_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ w0))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r0) **
       (.x6 ↦ᵣ (r0 + signExtend12 (1 : BitVec 12))) **
       (.x7 ↦ᵣ (if BitVec.ult (r0 + signExtend12 (1 : BitVec 12))
          (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0)) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ (r0 + signExtend12 (1 : BitVec 12)))) := by
  have L := ld_spec_gen_within .x5 .x12 sp x5Old r0 96 base (by nofun)
  have A := addi_spec_gen_within .x6 .x5 x6Old r0 1 (base + 4) (by nofun)
  have C := sltiu_spec_gen_within .x7 .x6 x7Old
    (r0 + signExtend12 (1 : BitVec 12)) 1 (base + 8) (by nofun)
  have S := sd_spec_gen_within .x12 .x6 sp
    (r0 + signExtend12 (1 : BitVec 12)) w0 64 (base + 12)
  runBlock L A C S

abbrev evm_addmod_pow256_prepare_plus_one_mod_args_limb1_chunk_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 (104 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.ADD .x6 .x5 .x7))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SLTU .x7 .x6 .x7))
   (CodeReq.singleton (base + 12) (.SD .x12 .x6 (72 : BitVec 12)))))

/-- Plus-one MOD-call setup limb 1: add the incoming carry, compute the next
    carry, and store the second dividend limb. -/
theorem evm_addmod_pow256_prepare_plus_one_mod_args_limb1_chunk_spec_within
    (sp base x5Old x6Old carryIn r1 w1 : Word) :
    cpsTripleWithin 4 base (base + 16)
      (evm_addmod_pow256_prepare_plus_one_mod_args_limb1_chunk_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ carryIn) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ w1))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r1) ** (.x6 ↦ᵣ (r1 + carryIn)) **
       (.x7 ↦ᵣ (if BitVec.ult (r1 + carryIn) carryIn then (1 : Word) else 0)) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ (r1 + carryIn))) := by
  have L := ld_spec_gen_within .x5 .x12 sp x5Old r1 104 base (by nofun)
  have A := add_spec_gen_within .x6 .x5 .x7 r1 carryIn x6Old (base + 4) (by nofun)
  have C := sltu_spec_gen_rd_eq_rs2_within .x7 .x6 (r1 + carryIn) carryIn (base + 8) (by nofun)
  have S := sd_spec_gen_within .x12 .x6 sp (r1 + carryIn) w1 72 (base + 12)
  runBlock L A C S

abbrev evm_addmod_pow256_prepare_plus_one_mod_args_limb2_chunk_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 (112 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.ADD .x6 .x5 .x7))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SLTU .x7 .x6 .x7))
   (CodeReq.singleton (base + 12) (.SD .x12 .x6 (80 : BitVec 12)))))

/-- Plus-one MOD-call setup limb 2: add the incoming carry, compute the next
    carry, and store the third dividend limb. -/
theorem evm_addmod_pow256_prepare_plus_one_mod_args_limb2_chunk_spec_within
    (sp base x5Old x6Old carryIn r2 w2 : Word) :
    cpsTripleWithin 4 base (base + 16)
      (evm_addmod_pow256_prepare_plus_one_mod_args_limb2_chunk_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ carryIn) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ w2))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r2) ** (.x6 ↦ᵣ (r2 + carryIn)) **
       (.x7 ↦ᵣ (if BitVec.ult (r2 + carryIn) carryIn then (1 : Word) else 0)) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ (r2 + carryIn))) := by
  have L := ld_spec_gen_within .x5 .x12 sp x5Old r2 112 base (by nofun)
  have A := add_spec_gen_within .x6 .x5 .x7 r2 carryIn x6Old (base + 4) (by nofun)
  have C := sltu_spec_gen_rd_eq_rs2_within .x7 .x6 (r2 + carryIn) carryIn (base + 8) (by nofun)
  have S := sd_spec_gen_within .x12 .x6 sp (r2 + carryIn) w2 80 (base + 12)
  runBlock L A C S

abbrev evm_addmod_pow256_prepare_plus_one_mod_args_limb3_chunk_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 (120 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.ADD .x6 .x5 .x7))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SLTU .x7 .x6 .x7))
   (CodeReq.singleton (base + 12) (.SD .x12 .x6 (88 : BitVec 12)))))

/-- Plus-one MOD-call setup high limb: add the incoming carry, compute the
    discarded final carry, and store the high dividend limb. -/
theorem evm_addmod_pow256_prepare_plus_one_mod_args_limb3_chunk_spec_within
    (sp base x5Old x6Old carryIn r3 w3 : Word) :
    cpsTripleWithin 4 base (base + 16)
      (evm_addmod_pow256_prepare_plus_one_mod_args_limb3_chunk_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ carryIn) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ r3) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ w3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r3) ** (.x6 ↦ᵣ (r3 + carryIn)) **
       (.x7 ↦ᵣ (if BitVec.ult (r3 + carryIn) carryIn then (1 : Word) else 0)) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ r3) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ (r3 + carryIn))) := by
  have L := ld_spec_gen_within .x5 .x12 sp x5Old r3 120 base (by nofun)
  have A := add_spec_gen_within .x6 .x5 .x7 r3 carryIn x6Old (base + 4) (by nofun)
  have C := sltu_spec_gen_rd_eq_rs2_within .x7 .x6 (r3 + carryIn) carryIn (base + 8) (by nofun)
  have S := sd_spec_gen_within .x12 .x6 sp (r3 + carryIn) w3 88 (base + 12)
  runBlock L A C S

/-- Compose the full helper that prepares the first callable MOD arguments for
    the ADDMOD overflow path. -/
theorem evm_addmod_pow256_prepare_minus_one_mod_args_spec_within
    (sp base : Word) (x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 : Word) :
    cpsTripleWithin 13 base (base + 52)
      (evm_addmod_pow256_prepare_minus_one_mod_args_code base)
      (evmAddModPow256PrepareMinusOnePre sp
        x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3)
      (evmAddModPow256PrepareMinusOnePost sp n0 n1 n2 n3) := by
  rw [evmAddModPow256PrepareMinusOnePre_unfold,
      evmAddModPow256PrepareMinusOnePost_unfold]
  have I := evm_addmod_pow256_prepare_minus_one_mod_args_init_spec_within
    base x5Old
  have S0 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store0_spec_within
    sp (signExtend12 (4095 : BitVec 12)) (base + 4) w0
  have S1 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store1_spec_within
    sp (signExtend12 (4095 : BitVec 12)) (base + 8) w1
  have S2 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store2_spec_within
    sp (signExtend12 (4095 : BitVec 12)) (base + 12) w2
  have S3 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_store3_spec_within
    sp (signExtend12 (4095 : BitVec 12)) (base + 16) w3
  have L0 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_load0_spec_within
    sp (signExtend12 (4095 : BitVec 12)) (base + 20) n0
  have C0 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy0_spec_within
    sp (base + 24) n0 u0
  have L1 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_load1_spec_within
    sp (base + 28) n0 n1
  have C1 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy1_spec_within
    sp (base + 32) n1 u1
  have L2 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_load2_spec_within
    sp (base + 36) n1 n2
  have C2 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy2_spec_within
    sp (base + 40) n2 u2
  have L3 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_load3_spec_within
    sp (base + 44) n2 n3
  have C3 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy3_spec_within
    sp (base + 48) n3 u3
  runBlock I S0 S1 S2 S3 L0 C0 L1 C1 L2 C2 L3 C3

end EvmAsm.Evm64
