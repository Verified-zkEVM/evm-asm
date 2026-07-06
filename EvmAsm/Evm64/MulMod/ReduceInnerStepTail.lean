/-
  EvmAsm.Evm64.MulMod.ReduceInnerStepTail

  CPS spec for the loop-tail branch of the MULMOD reducer inner step.
-/

import EvmAsm.Evm64.MulMod.ReduceCompare
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.SyscallSpecs

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The loop-control tail of `evm_mulmod_reduce512_inner_step`. -/
def evm_mulmod_reduce512_inner_step_tail : Program :=
  ADDI .x15 .x15 4095 ;;
  BNE .x15 .x0 (-252 : BitVec 13)

abbrev evm_mulmod_reduce512_inner_step_tail_code (base : Word) : CodeReq :=
  CodeReq.ofProg (base + 248) evm_mulmod_reduce512_inner_step_tail

/-- Folded postcondition for the reducer inner-step loop tail. -/
@[irreducible]
def mulModReduceTailPost (x15 : Word) (done : Bool) : Assertion :=
  let x15New := x15 + signExtend12 (4095 : BitVec 12)
  ((.x15 ↦ᵣ x15New) **
  (.x0 ↦ᵣ (0 : Word))) **
  ⌜if done then x15New = 0 else x15New ≠ 0⌝

theorem evm_mulmod_reduce512_inner_step_tail_spec_within
    (base x15 : Word) :
    cpsBranchWithin 2 (base + 248)
      (evm_mulmod_reduce512_inner_step_tail_code base)
      ((.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word)))
      base (mulModReduceTailPost x15 false)
      (base + 256) (mulModReduceTailPost x15 true) := by
  show cpsBranchWithin 2 (base + 248)
    (CodeReq.ofProg (base + 248) evm_mulmod_reduce512_inner_step_tail) _ _ _ _ _
  rw [show CodeReq.ofProg (base + 248) evm_mulmod_reduce512_inner_step_tail =
      (CodeReq.singleton (base + 248) (.ADDI .x15 .x15 4095)).union
        (CodeReq.singleton (base + 252) (.BNE .x15 .x0 (-252 : BitVec 13))) by
    unfold evm_mulmod_reduce512_inner_step_tail
    show CodeReq.ofProg (base + 248)
        [.ADDI .x15 .x15 4095, .BNE .x15 .x0 (-252 : BitVec 13)] = _
    rw [CodeReq.ofProg_pair]
    rw [show (base + 248 : Word) + 4 = base + 252 by bv_omega]]
  unfold mulModReduceTailPost
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hnext : (base + 248 : Word) + 4 = base + 252 := by bv_omega
  have hfallthrough : (base + 252 : Word) + 4 = base + 256 := by bv_omega
  have hse : signExtend13 ((-252 : BitVec 13)) = (18446744073709551364 : Word) := by
    decide
  have hloop : (base + 252 : Word) + signExtend13 ((-252 : BitVec 13)) = base := by
    rw [hse]
    bv_omega
  have hdisjoint : CodeReq.Disjoint
      (CodeReq.singleton (base + 248) (.ADDI .x15 .x15 4095))
      (CodeReq.singleton (base + 252) (.BNE .x15 .x0 (-252 : BitVec 13))) :=
    CodeReq.Disjoint.singleton (by bv_omega)
  have haddi_raw := addi_spec_gen_same_within .x15 x15 4095 (base + 248) (by decide)
  rw [hnext] at haddi_raw
  have haddi : cpsTripleWithin 1 (base + 248) (base + 252)
      (CodeReq.singleton (base + 248) (.ADDI .x15 .x15 4095))
      ((.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x15 ↦ᵣ (x15 + signExtend12 (4095 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) haddi_raw
  have hbne := bne_spec_gen_within .x15 .x0 (-252 : BitVec 13)
    (x15 + signExtend12 (4095 : BitVec 12)) (0 : Word) (base + 252)
  rw [hloop, hfallthrough] at hbne
  simpa only [Nat.reduceAdd, sepConj_assoc'] using
    (cpsTripleWithin_seq_cpsBranchWithin_with_perm hdisjoint
      (fun _ hp => hp) haddi hbne)

theorem evm_mulmod_reduce512_inner_step_tail_done_spec_within
    (base x15 : Word)
    (h_done : x15 + signExtend12 (4095 : BitVec 12) = 0) :
    cpsTripleWithin 2 (base + 248) (base + 256)
      (evm_mulmod_reduce512_inner_step_tail_code base)
      (((.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word))) **
        ⌜x15 + signExtend12 (4095 : BitVec 12) = 0⌝)
      (mulModReduceTailPost x15 true) := by
  have hbr := evm_mulmod_reduce512_inner_step_tail_spec_within base x15
  have hdone_pre : cpsBranchWithin 2 (base + 248)
      (evm_mulmod_reduce512_inner_step_tail_code base)
      (((.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word))) **
        ⌜x15 + signExtend12 (4095 : BitVec 12) = 0⌝)
      base (mulModReduceTailPost x15 false)
      (base + 256) (mulModReduceTailPost x15 true) :=
    cpsBranchWithin_weaken (fun h hp => ((sepConj_pure_right h).1 hp).1)
      (fun _ hp => hp) (fun _ hp => hp) hbr
  exact cpsBranchWithin_ntakenPath hdone_pre (by
    intro h hp
    unfold mulModReduceTailPost at hp
    simp only [Bool.false_eq_true, ↓reduceIte] at hp
    obtain ⟨hregs, h_ne⟩ := (sepConj_pure_right h).1 hp
    exact h_ne h_done)

theorem evm_mulmod_reduce512_inner_step_tail_loop_spec_within
    (base x15 : Word)
    (h_loop : x15 + signExtend12 (4095 : BitVec 12) ≠ 0) :
    cpsTripleWithin 2 (base + 248) base
      (evm_mulmod_reduce512_inner_step_tail_code base)
      (((.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word))) **
        ⌜x15 + signExtend12 (4095 : BitVec 12) ≠ 0⌝)
      (mulModReduceTailPost x15 false) := by
  have hbr := evm_mulmod_reduce512_inner_step_tail_spec_within base x15
  have hloop_pre : cpsBranchWithin 2 (base + 248)
      (evm_mulmod_reduce512_inner_step_tail_code base)
      (((.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word))) **
        ⌜x15 + signExtend12 (4095 : BitVec 12) ≠ 0⌝)
      base (mulModReduceTailPost x15 false)
      (base + 256) (mulModReduceTailPost x15 true) :=
    cpsBranchWithin_weaken (fun h hp => ((sepConj_pure_right h).1 hp).1)
      (fun _ hp => hp) (fun _ hp => hp) hbr
  exact cpsBranchWithin_takenPath hloop_pre (by
    intro h hp
    unfold mulModReduceTailPost at hp
    simp only [ite_true] at hp
    obtain ⟨hregs, h_eq⟩ := (sepConj_pure_right h).1 hp
    exact h_loop h_eq)

end EvmAsm.Evm64
