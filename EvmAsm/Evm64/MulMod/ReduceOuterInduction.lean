/-
  EvmAsm.Evm64.MulMod.ReduceOuterInduction

  Eight-limb induction for the MULMOD 512-bit reducer outer loop. The outer
  loop walks the eight 64-bit product limbs from high to low (`x16` starts at
  the top limb and decreases by 8 each iteration), folding each into the
  running remainder via the inner bit loop. Unlike the inner loop — whose
  product word is carried in a register and shifted — the outer loop's limbs
  live in memory, so the induction threads a *window* of the not-yet-processed
  limbs (`limbChain`) as a frame across iterations.

  This file builds that window primitive; the induction over
  `evm_mulmod_reduce512_loop_body_loop_path` / `_done_path` follows.
-/

import EvmAsm.Evm64.MulMod.ReduceOuterLoop

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The product-limb memory window: `m` consecutive 64-bit limbs in memory,
    the first at `ptr`, each subsequent one 8 bytes lower (`ptr - 8`, matching
    the outer loop's `ADDI x16, x16, -8` stride). `limbs i` is the value at
    `ptr - 8 * i`; `limbs 0` is the limb the next iteration consumes. The empty
    window (`m = 0`) owns no memory. -/
def limbChain (ptr : Word) (limbs : Nat → Word) : Nat → Assertion
  | 0 => empAssertion
  | m + 1 =>
    ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ limbs 0) **
    limbChain (ptr + signExtend12 (4088 : BitVec 12)) (fun i => limbs (i + 1)) m

@[simp] theorem limbChain_zero (ptr : Word) (limbs : Nat → Word) :
    limbChain ptr limbs 0 = empAssertion := rfl

/-- Peel the head limb off the window: the limb at `ptr` (the next to be
    consumed) splits off, leaving the remaining `m` limbs as a window starting
    8 bytes lower. This is the step the eight-limb induction takes each
    iteration — the body folds `limbs 0`, then the tail becomes the next
    iteration's window. -/
theorem limbChain_succ (ptr : Word) (limbs : Nat → Word) (m : Nat) :
    limbChain ptr limbs (m + 1) =
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ limbs 0) **
        limbChain (ptr + signExtend12 (4088 : BitVec 12)) (fun i => limbs (i + 1)) m) :=
  rfl

/-- The product-limb window constrains only memory, never the program counter,
    so it is a valid frame for `cpsTripleWithin_frameR`. -/
theorem limbChain_pcFree (ptr : Word) (limbs : Nat → Word) (m : Nat) :
    (limbChain ptr limbs m).pcFree := by
  induction m generalizing ptr limbs with
  | zero => exact pcFree_emp
  | succ k ih => exact pcFree_sepConj pcFree_memIs (ih _ _)

/-- Loop-carried state at an outer-loop iteration boundary, minus the product
    cells (those are carried by `limbChain`). It is the bit-loop's clean post
    (`mulModReduceBitLoopPost`) with the limb pointer `x16` and limb counter
    `x18` reintroduced and the bit counter `x15` freed — exactly the shape the
    `regOwn` body adapter consumes once the current product cell is split off. -/
def outerEntryCore (sp ptr c : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x16 ↦ᵣ ptr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x18 ↦ᵣ c) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 ** regOwn .x13 **
  regOwn .x17 ** regOwn .x15 ** regOwn .x19 ** regOwn .x20 **
  mulModReduceCompareMem sp r n

/-- Eight-limb outer reducer loop, by induction on the remaining limb count `m`
    (1 ≤ m ≤ 8): starting with `m` in the limb counter `x18` and the current
    product limb at `x16 = ptr`, the loop folds the `m` product limbs (highest
    first, `limbChain ptr limbs m`) into the remainder and lands at the loop
    exit `base + 276` with the remainder fully reduced over those limbs
    (`mulModReduceOuterFold n limbs r m`). The window limbs are read-only, so
    they are preserved in the postcondition. -/
private theorem outer_aux (m : Nat) :
    1 ≤ m → m ≤ 8 →
    ∀ (sp base ptr : Word) (r n : EvmWord) (limbs : Nat → Word),
    cpsTripleWithin ((2 + 64 * 64 + 2 + 1) * m) base (base + 276)
      (CodeReq.ofProg base evm_mulmod_reduce512_loop)
      (outerEntryCore sp ptr (BitVec.ofNat 64 m) r n ** limbChain ptr limbs m)
      (mulModReduceBitLoopPost sp (mulModReduceOuterFold n limbs r m) n **
        regOwn .x16 ** regOwn .x18 ** limbChain ptr limbs m) := by
  induction m with
  | zero => intro h1 _; omega
  | succ k ih =>
    intro _ h8 sp base ptr r n limbs
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- base case: one limb remains (m = 1)
      subst hk0
      have hdone : BitVec.ofNat 64 1 + signExtend12 (4095 : BitVec 12) = 0 :=
        (mulModReduceBitCounter_eq_zero_iff 1 (by omega) (by omega)).mpr rfl
      have hstep := evm_mulmod_reduce512_loop_body_done_path
        sp base ptr (BitVec.ofNat 64 1) (limbs 0) r n hdone
      rw [show (2 + 64 * 64 + 2 + 1) * 1 = 2 + 64 * 64 + 2 + 1 from by ring,
        show mulModReduceOuterFold n limbs r 1 = mulModReduceStepN r n (limbs 0) 64 from by
          rw [mulModReduceOuterFold_succ, mulModReduceOuterFold_zero]]
      refine cpsTripleWithin_weaken ?_ ?_ hstep
      · intro h hp
        rw [limbChain_succ, limbChain_zero, sepConj_emp_right'] at hp
        unfold outerEntryCore mulModReduceCompareMem at hp
        unfold bodyLoopCommon
        xperm_hyp hp
      · intro h hp
        rw [limbChain_succ, limbChain_zero, sepConj_emp_right']
        -- done post: BitLoopPost ** x16↦.. ** x18↦.. ** mem ** ⌜=0⌝
        -- → BitLoopPost ** regOwn x16 ** regOwn x18 ** mem
        have hp1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x16 _)) h hp
        have hp2 := sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (regIs_to_regOwn .x18 _))) h hp1
        have hp3 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (fun _ hq => ((sepConj_pure_right _).1 hq).1))) h hp2
        xperm_hyp hp3
    · -- inductive step: m = k + 1 with k ≥ 1
      have hloop : BitVec.ofNat 64 (k + 1) + signExtend12 (4095 : BitVec 12) ≠ 0 := by
        intro hc
        have := (mulModReduceBitCounter_eq_zero_iff (k + 1) (by omega) (by omega)).mp hc
        omega
      have hstep := evm_mulmod_reduce512_loop_body_loop_path
        sp base ptr (BitVec.ofNat 64 (k + 1)) (limbs 0) r n hloop
      have hframed_loop := cpsTripleWithin_frameR
        (limbChain (ptr + signExtend12 (4088 : BitVec 12)) (fun i => limbs (i + 1)) k)
        (limbChain_pcFree _ _ _) hstep
      have hih := ih hkpos (by omega) sp base (ptr + signExtend12 (4088 : BitVec 12))
        (mulModReduceStepN r n (limbs 0) 64) n (fun i => limbs (i + 1))
      have hIH' := cpsTripleWithin_frameR
        ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ limbs 0) (by pcFree) hih
      rw [show (2 + 64 * 64 + 2 + 1) * (k + 1)
            = (2 + 64 * 64 + 2 + 1) + (2 + 64 * 64 + 2 + 1) * k from by ring,
        mulModReduceOuterFold_succ]
      refine cpsTripleWithin_weaken ?_ ?_
        (cpsTripleWithin_seq_perm_same_cr ?_ hframed_loop hIH')
      · -- pre(k+1) ⊢ framed loop-path precondition
        intro h hp
        rw [limbChain_succ] at hp
        unfold outerEntryCore mulModReduceCompareMem at hp
        unfold bodyLoopCommon
        xperm_hyp hp
      · -- framed IH postcondition ⊢ post(k+1)
        intro h hp
        rw [limbChain_succ]
        xperm_hyp hp
      · -- bridge: loop-path post ⊢ next-iteration entry (with consumed cell framed)
        intro h hp
        rw [mulModReduceBitCounter_decr (k + 1) (by omega) (by omega)] at hp
        simp only [Nat.add_sub_cancel] at hp
        -- strip the loop-guard pure fact (heap-empty) while `BitLoopPost` is folded
        have hp0 := sepConj_mono_left
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (fun _ hq => ((sepConj_pure_right _).1 hq).1)))) h hp
        unfold mulModReduceBitLoopPost mulModReduceCompareMem at hp0
        -- free the (overwritten-next-iteration) bit counter `x15 = 0` to ownership
        have hp' := sepConj_mono_left
          (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x15 _)))) h hp0
        unfold outerEntryCore mulModReduceCompareMem
        xperm_hyp hp'

/-- The full eight-limb outer reducer loop spec, instantiated at the eight-limb
    count: starting at the top product limb `ptr`, it reduces all eight limbs
    into the remainder. -/
theorem evm_mulmod_reduce512_loop_spec_within
    (sp base ptr : Word) (r n : EvmWord) (limbs : Nat → Word) :
    cpsTripleWithin ((2 + 64 * 64 + 2 + 1) * 8) base (base + 276)
      (CodeReq.ofProg base evm_mulmod_reduce512_loop)
      (outerEntryCore sp ptr (BitVec.ofNat 64 8) r n ** limbChain ptr limbs 8)
      (mulModReduceBitLoopPost sp (mulModReduceOuterFold n limbs r 8) n **
        regOwn .x16 ** regOwn .x18 ** limbChain ptr limbs 8) :=
  outer_aux 8 (by omega) (by omega) sp base ptr r n limbs

end EvmAsm.Evm64
