/-
  EvmAsm.Evm64.MulMod.ReduceBitLoop

  Loop-facing adapter for the MULMOD 512-bit reducer. The inner-step branch
  spec clobbers and surrenders seven scratch registers
  (`x5/x6/x7/x8/x10/x11/x13`, with `x8` the new carry register), so the
  bit-loop invariant carries them as ownership. This file restates the inner
  step over that loop-carried precondition.
-/

import EvmAsm.Evm64.MulMod.ReduceInnerStepSpecs
import EvmAsm.Evm64.MulMod.ReduceFoldInvariant

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- The non-scratch resources carried unchanged across one reducer bit step:
    the frame pointer, the shifting product word, the bit counter, the carry
    scratch `x19/x20`, and the remainder/modulus memory windows. -/
def bitLoopCommon
    (sp x17Old x15 x19Old x20Old : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x17 ↦ᵣ x17Old) ** (.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x19 ↦ᵣ x19Old) ** (.x20 ↦ᵣ x20Old) **
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 0) **
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

/-- Loop-carried precondition for one reducer bit step: `bitLoopCommon` plus
    ownership of the seven clobbered scratch registers (including the new carry
    register `x8`). -/
@[irreducible]
def mulModReduceBitLoopPre
    (sp x17Old x15 x19Old x20Old : Word) (r n : EvmWord) : Assertion :=
  bitLoopCommon sp x17Old x15 x19Old x20Old r n **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x8 **
  regOwn .x10 ** regOwn .x11 ** regOwn .x13

/-- One reducer bit step restated over the loop-carried precondition that owns
    the six clobbered scratch registers, ready for the bit-loop induction. -/
theorem evm_mulmod_reduce512_bit_loop_step_spec_within
    (sp base x17Old x15 x19Old x20Old : Word) (r n : EvmWord) :
    cpsBranchWithin 66 base
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceBitLoopPre sp x17Old x15 x19Old x20Old r n)
      base (mulModReduceInnerStepPost sp x17Old x15 r n false)
      (base + 264) (mulModReduceInnerStepPost sp x17Old x15 r n true) := by
  have h13 : cpsBranchWithin 66 base
      (evm_mulmod_reduce512_inner_step_code base)
      ((bitLoopCommon sp x17Old x15 x19Old x20Old r n **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x8 ** regOwn .x10 ** regOwn .x11) **
        regOwn .x13)
      base (mulModReduceInnerStepPost sp x17Old x15 r n false)
      (base + 264) (mulModReduceInnerStepPost sp x17Old x15 r n true) := by
    refine cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x13) ?_
    intro v13
    have h11 : cpsBranchWithin 66 base
        (evm_mulmod_reduce512_inner_step_code base)
        ((bitLoopCommon sp x17Old x15 x19Old x20Old r n ** (.x13 ↦ᵣ v13) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x8 ** regOwn .x10) **
          regOwn .x11)
        base (mulModReduceInnerStepPost sp x17Old x15 r n false)
        (base + 264) (mulModReduceInnerStepPost sp x17Old x15 r n true) := by
      refine cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x11) ?_
      intro v11
      have h10 : cpsBranchWithin 66 base
          (evm_mulmod_reduce512_inner_step_code base)
          ((bitLoopCommon sp x17Old x15 x19Old x20Old r n ** (.x13 ↦ᵣ v13) **
              (.x11 ↦ᵣ v11) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x8) **
            regOwn .x10)
          base (mulModReduceInnerStepPost sp x17Old x15 r n false)
          (base + 264) (mulModReduceInnerStepPost sp x17Old x15 r n true) := by
        refine cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x10) ?_
        intro v10
        have h8 : cpsBranchWithin 66 base
            (evm_mulmod_reduce512_inner_step_code base)
            ((bitLoopCommon sp x17Old x15 x19Old x20Old r n ** (.x13 ↦ᵣ v13) **
                (.x11 ↦ᵣ v11) ** (.x10 ↦ᵣ v10) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7) **
              regOwn .x8)
            base (mulModReduceInnerStepPost sp x17Old x15 r n false)
            (base + 264) (mulModReduceInnerStepPost sp x17Old x15 r n true) := by
          refine cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x8) ?_
          intro v8
          have h7 : cpsBranchWithin 66 base
              (evm_mulmod_reduce512_inner_step_code base)
              ((bitLoopCommon sp x17Old x15 x19Old x20Old r n ** (.x13 ↦ᵣ v13) **
                  (.x11 ↦ᵣ v11) ** (.x10 ↦ᵣ v10) ** (.x8 ↦ᵣ v8) ** regOwn .x5 ** regOwn .x6) **
                regOwn .x7)
              base (mulModReduceInnerStepPost sp x17Old x15 r n false)
              (base + 264) (mulModReduceInnerStepPost sp x17Old x15 r n true) := by
            refine cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x7) ?_
            intro v7
            have h6 : cpsBranchWithin 66 base
                (evm_mulmod_reduce512_inner_step_code base)
                ((bitLoopCommon sp x17Old x15 x19Old x20Old r n ** (.x13 ↦ᵣ v13) **
                    (.x11 ↦ᵣ v11) ** (.x10 ↦ᵣ v10) ** (.x8 ↦ᵣ v8) ** (.x7 ↦ᵣ v7) ** regOwn .x5) **
                  regOwn .x6)
                base (mulModReduceInnerStepPost sp x17Old x15 r n false)
                (base + 264) (mulModReduceInnerStepPost sp x17Old x15 r n true) := by
              refine cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x6) ?_
              intro v6
              have h5 : cpsBranchWithin 66 base
                  (evm_mulmod_reduce512_inner_step_code base)
                  ((bitLoopCommon sp x17Old x15 x19Old x20Old r n ** (.x13 ↦ᵣ v13) **
                      (.x11 ↦ᵣ v11) ** (.x10 ↦ᵣ v10) ** (.x8 ↦ᵣ v8) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6)) **
                    regOwn .x5)
                  base (mulModReduceInnerStepPost sp x17Old x15 r n false)
                  (base + 264) (mulModReduceInnerStepPost sp x17Old x15 r n true) := by
                refine cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x5) ?_
                intro v5
                refine cpsBranchWithin_weaken
                  (fun h hp => by
                    unfold bitLoopCommon at hp
                    unfold mulModReduceInnerStepPre mulModReduceInnerStepSubtractPre
                    xperm_hyp hp)
                  (fun _ hp => hp) (fun _ hp => hp)
                  (evm_mulmod_reduce512_inner_step_spec_within
                    sp base x17Old v5 v6 v7 v8 v10 v11 v13 x15 x19Old x20Old r n)
              exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
                (fun _ hp => hp) (fun _ hp => hp) h5
            exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
              (fun _ hp => hp) (fun _ hp => hp) h6
          exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
            (fun _ hp => hp) (fun _ hp => hp) h7
        exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
          (fun _ hp => hp) (fun _ hp => hp) h8
      exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun _ hp => hp) (fun _ hp => hp) h10
    exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ hp => hp) (fun _ hp => hp) h11
  exact cpsBranchWithin_weaken
    (fun h hp => by
      unfold mulModReduceBitLoopPre at hp
      xperm_hyp hp)
    (fun _ hp => hp) (fun _ hp => hp) h13

/-- One iteration's loop-back post is the next iteration's loop-carried
    precondition: the stepped remainder becomes the new `r`, the product word
    shifts, the bit counter decrements, and the carry scratch `x19/x20` carry
    the consumed-bit fields. -/
theorem mulModReduceInnerStepPost_false_to_bitLoopPre
    (sp x17Old x15 : Word) (r n : EvmWord) :
    ∀ h, mulModReduceInnerStepPost sp x17Old x15 r n false h →
      mulModReduceBitLoopPre sp (x17Old <<< 1)
        (x15 + signExtend12 (4095 : BitVec 12))
        (EvmWord.getLimbN r 1 >>> 63) (EvmWord.getLimbN r 2 >>> 63)
        (mulModReduceStepCarry r n (mulModReduceInputBit x17Old)) n h := by
  intro h hp
  unfold mulModReduceInnerStepPost mulModReduceTailPost mulModReduceCompareMem at hp
  simp only [Bool.false_eq_true, ↓reduceIte] at hp
  have hp' := sepConj_mono_left
    (fun _ hq => ((sepConj_pure_right _).1 hq).1) h hp
  unfold mulModReduceBitLoopPre bitLoopCommon
  xperm_hyp hp'

/-- When the decremented bit counter is still nonzero, the bit step takes the
    loop-back exit: a `base → base` triple landing in the loop-back post. -/
theorem evm_mulmod_reduce512_bit_loop_step_loop_path
    (sp base x17Old x15 x19Old x20Old : Word) (r n : EvmWord)
    (hloop : x15 + signExtend12 (4095 : BitVec 12) ≠ 0) :
    cpsTripleWithin 66 base base
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceBitLoopPre sp x17Old x15 x19Old x20Old r n)
      (mulModReduceInnerStepPost sp x17Old x15 r n false) := by
  refine cpsBranchWithin_takenPath
    (evm_mulmod_reduce512_bit_loop_step_spec_within
      sp base x17Old x15 x19Old x20Old r n) ?_
  intro hp hq
  unfold mulModReduceInnerStepPost mulModReduceTailPost at hq
  simp only [↓reduceIte] at hq
  obtain ⟨h1, h2, _, _, htail, _⟩ := hq
  exact hloop ((sepConj_pure_right _).1 htail).2

/-- When the decremented bit counter reaches zero, the bit step takes the done
    exit: a `base → base + 256` triple landing in the done post. -/
theorem evm_mulmod_reduce512_bit_loop_step_done_path
    (sp base x17Old x15 x19Old x20Old : Word) (r n : EvmWord)
    (hdone : x15 + signExtend12 (4095 : BitVec 12) = 0) :
    cpsTripleWithin 66 base (base + 264)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceBitLoopPre sp x17Old x15 x19Old x20Old r n)
      (mulModReduceInnerStepPost sp x17Old x15 r n true) := by
  refine cpsBranchWithin_ntakenPath
    (evm_mulmod_reduce512_bit_loop_step_spec_within
      sp base x17Old x15 x19Old x20Old r n) ?_
  intro hp hq
  unfold mulModReduceInnerStepPost mulModReduceTailPost at hq
  simp only [Bool.false_eq_true, ↓reduceIte] at hq
  obtain ⟨h1, h2, _, _, htail, _⟩ := hq
  exact ((sepConj_pure_right _).1 htail).2 hdone

/-- Clean post-state of the full inner 64-bit bit loop: the remainder window
    holds `result`, the modulus is preserved, the bit counter has reached zero,
    and every scratch/shifted register is surrendered as ownership. -/
@[irreducible]
def mulModReduceBitLoopPost (sp : Word) (result n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x15 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x8 ** regOwn .x10 ** regOwn .x11 **
  regOwn .x13 ** regOwn .x17 ** regOwn .x19 ** regOwn .x20 **
  mulModReduceCompareMem sp result n

/-- The done-exit tail post pins the bit counter to zero. -/
theorem tailPost_true_regs_zero (x15 : Word) :
    ∀ h, mulModReduceTailPost x15 true h →
      ((Reg.x15 ↦ᵣ (0 : Word)) ** (Reg.x0 ↦ᵣ (0 : Word))) h := by
  intro h hq
  unfold mulModReduceTailPost at hq
  simp only [↓reduceIte] at hq
  obtain ⟨hregs, hpure⟩ := (sepConj_pure_right _).1 hq
  rw [hpure] at hregs
  exact hregs

/-- The done-exit inner-step post is the clean bit-loop post. -/
theorem mulModReduceInnerStepPost_true_to_bitLoopPost
    (sp x17Old x15 : Word) (r n : EvmWord) :
    ∀ h, mulModReduceInnerStepPost sp x17Old x15 r n true h →
      mulModReduceBitLoopPost sp
        (mulModReduceStepCarry r n (mulModReduceInputBit x17Old)) n h := by
  intro h hp
  unfold mulModReduceInnerStepPost at hp
  have hp1 := sepConj_mono_left (tailPost_true_regs_zero x15) h hp
  have w3 : ∀ (a b c : Word) (M : Assertion) hh,
      ((Reg.x17 ↦ᵣ a) ** (Reg.x19 ↦ᵣ b) ** (Reg.x20 ↦ᵣ c) ** M) hh →
      (regOwn Reg.x17 ** regOwn Reg.x19 ** regOwn Reg.x20 ** M) hh := by
    intro a b c M hh hq
    have q1 := sepConj_mono_left (regIs_to_regOwn .x17 _) hh hq
    have q2 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x19 _)) hh q1
    exact sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x20 _))) hh q2
  have hp2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (w3 _ _ _ _))))))))) h hp1
  unfold mulModReduceBitLoopPost
  xperm_hyp hp2

/-- Inner 64-bit reducer loop, by induction on the remaining iteration count
    `m` (1 ≤ m ≤ 64): starting with `m` in the counter `x15`, the loop runs `m`
    bit steps and lands in the clean done-state with the remainder folded `m`
    times. -/
private theorem bit_loop_aux (m : Nat) :
    1 ≤ m → m ≤ 64 →
    ∀ (sp base w x19v x20v : Word) (r n : EvmWord),
    cpsTripleWithin (66 * m) base (base + 264)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceBitLoopPre sp w (BitVec.ofNat 64 m) x19v x20v r n)
      (mulModReduceBitLoopPost sp (mulModReduceStepNCarry r n w m) n) := by
  induction m with
  | zero => intro h1 _; omega
  | succ k ih =>
    intro _ h64 sp base w x19v x20v r n
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- base case: one iteration remains (m = 1)
      subst hk0
      have hdone : BitVec.ofNat 64 1 + signExtend12 (4095 : BitVec 12) = 0 :=
        (mulModReduceBitCounter_eq_zero_iff 1 (by omega) (by omega)).mpr rfl
      have hstep := evm_mulmod_reduce512_bit_loop_step_done_path
        sp base w (BitVec.ofNat 64 1) x19v x20v r n hdone
      have hres := cpsTripleWithin_weaken (fun _ hp => hp)
        (mulModReduceInnerStepPost_true_to_bitLoopPost sp w (BitVec.ofNat 64 1) r n)
        hstep
      simpa using hres
    · -- inductive step: m = k + 1 with k ≥ 1
      have hloop : BitVec.ofNat 64 (k + 1) + signExtend12 (4095 : BitVec 12) ≠ 0 := by
        intro hc
        have := (mulModReduceBitCounter_eq_zero_iff (k + 1) (by omega) h64).mp hc
        omega
      have hstep := evm_mulmod_reduce512_bit_loop_step_loop_path
        sp base w (BitVec.ofNat 64 (k + 1)) x19v x20v r n hloop
      have hih := ih hkpos (by omega) sp base (w <<< 1)
        (EvmWord.getLimbN r 1 >>> 63) (EvmWord.getLimbN r 2 >>> 63)
        (mulModReduceStepCarry r n (mulModReduceInputBit w)) n
      have hcomp := cpsTripleWithin_seq_perm_same_cr
        (fun h hp => by
          have hb := mulModReduceInnerStepPost_false_to_bitLoopPre
            sp w (BitVec.ofNat 64 (k + 1)) r n h hp
          rw [mulModReduceBitCounter_decr (k + 1) (by omega) h64] at hb
          exact hb)
        hstep hih
      have hbound : 66 * (k + 1) = 66 + 66 * k := by ring
      rw [hbound, mulModReduceStepNCarry_succ]
      exact hcomp

/-- The inner 64-bit reducer loop, instantiated at the full 64-iteration count
    used by `evm_mulmod_reduce512_loop`. -/
theorem evm_mulmod_reduce512_bit_loop_spec_within
    (sp base w x19v x20v : Word) (r n : EvmWord) :
    cpsTripleWithin (66 * 64) base (base + 264)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceBitLoopPre sp w (BitVec.ofNat 64 64) x19v x20v r n)
      (mulModReduceBitLoopPost sp (mulModReduceStepNCarry r n w 64) n) :=
  bit_loop_aux 64 (by omega) (by omega) sp base w x19v x20v r n

end EvmAsm.Evm64
