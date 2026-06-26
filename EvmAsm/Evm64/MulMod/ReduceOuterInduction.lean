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
import EvmAsm.Evm64.MulMod.LimbSpec

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
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x8 ** regOwn .x10 ** regOwn .x11 ** regOwn .x13 **
  regOwn .x17 ** regOwn .x15 ** regOwn .x19 ** regOwn .x20 **
  mulModReduceCompareMem sp r n

/-- Eight-limb outer reducer loop, by induction on the remaining limb count `m`
    (1 ≤ m ≤ 8): starting with `m` in the limb counter `x18` and the current
    product limb at `x16 = ptr`, the loop folds the `m` product limbs (highest
    first, `limbChain ptr limbs m`) into the remainder and lands at the loop
    exit `base + 284` with the remainder fully reduced over those limbs
    (`mulModReduceOuterFoldCarry n limbs r m`). The window limbs are read-only, so
    they are preserved in the postcondition. -/
private theorem outer_aux (m : Nat) :
    1 ≤ m → m ≤ 8 →
    ∀ (sp base ptr : Word) (r n : EvmWord) (limbs : Nat → Word),
    cpsTripleWithin ((2 + 66 * 64 + 2 + 1) * m) base (base + 284)
      (CodeReq.ofProg base evm_mulmod_reduce512_loop)
      (outerEntryCore sp ptr (BitVec.ofNat 64 m) r n ** limbChain ptr limbs m)
      (mulModReduceBitLoopPost sp (mulModReduceOuterFoldCarry n limbs r m) n **
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
      rw [show (2 + 66 * 64 + 2 + 1) * 1 = 2 + 66 * 64 + 2 + 1 from by ring,
        show mulModReduceOuterFoldCarry n limbs r 1 = mulModReduceStepNCarry r n (limbs 0) 64 from by
          rw [mulModReduceOuterFoldCarry_succ, mulModReduceOuterFoldCarry_zero]]
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
        (mulModReduceStepNCarry r n (limbs 0) 64) n (fun i => limbs (i + 1))
      have hIH' := cpsTripleWithin_frameR
        ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ limbs 0) (by pcFree) hih
      rw [show (2 + 66 * 64 + 2 + 1) * (k + 1)
            = (2 + 66 * 64 + 2 + 1) + (2 + 66 * 64 + 2 + 1) * k from by ring,
        mulModReduceOuterFoldCarry_succ]
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
    cpsTripleWithin ((2 + 66 * 64 + 2 + 1) * 8) base (base + 284)
      (CodeReq.ofProg base evm_mulmod_reduce512_loop)
      (outerEntryCore sp ptr (BitVec.ofNat 64 8) r n ** limbChain ptr limbs 8)
      (mulModReduceBitLoopPost sp (mulModReduceOuterFoldCarry n limbs r 8) n **
        regOwn .x16 ** regOwn .x18 ** limbChain ptr limbs 8) :=
  outer_aux 8 (by omega) (by omega) sp base ptr r n limbs

/-- The reducer loop sits at byte offset 24 (after the six-instruction
    `evm_mulmod_reduce512_init` prefix) within the total reducer program
    `evm_mulmod_reduce512 = init ;; loop ;; write_result ;; epilogue`. -/
theorem evm_mulmod_reduce512_loop_code_sub (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + BitVec.ofNat 64 24) evm_mulmod_reduce512_loop) a = some i →
      (CodeReq.ofProg base evm_mulmod_reduce512) a = some i := by
  intro a i h
  refine CodeReq.ofProg_mono_append_right base evm_mulmod_reduce512_init
    (evm_mulmod_reduce512_loop ++
      (evm_mulmod_reduce512_write_result ++ evm_mulmod_epilogue))
    (by decide) a i ?_
  exact CodeReq.ofProg_mono_append_left (base + BitVec.ofNat 64 24)
    evm_mulmod_reduce512_loop
    (evm_mulmod_reduce512_write_result ++ evm_mulmod_epilogue) a i h

/-- The full outer reducer loop, lifted into the total reducer program code:
    from byte offset 24 it folds all eight product limbs into the remainder,
    landing at offset 308 (where `write_result` begins). -/
theorem evm_mulmod_reduce512_loop_total_spec_within
    (sp base ptr : Word) (r n : EvmWord) (limbs : Nat → Word) :
    cpsTripleWithin ((2 + 66 * 64 + 2 + 1) * 8) (base + 24) (base + 24 + 284)
      (CodeReq.ofProg base evm_mulmod_reduce512)
      (outerEntryCore sp ptr (BitVec.ofNat 64 8) r n ** limbChain ptr limbs 8)
      (mulModReduceBitLoopPost sp (mulModReduceOuterFoldCarry n limbs r 8) n **
        regOwn .x16 ** regOwn .x18 ** limbChain ptr limbs 8) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_loop_code_sub base)
    (h := evm_mulmod_reduce512_loop_spec_within sp (base + BitVec.ofNat 64 24) ptr r n limbs)

/-- `evm_mulmod_reduce512_init` is the prefix (byte offset 0) of the total
    reducer program. -/
theorem evm_mulmod_reduce512_init_code_sub (base : Word) :
    ∀ a i, (CodeReq.ofProg base evm_mulmod_reduce512_init) a = some i →
      (CodeReq.ofProg base evm_mulmod_reduce512) a = some i := by
  intro a i h
  exact CodeReq.ofProg_mono_append_left base evm_mulmod_reduce512_init
    (evm_mulmod_reduce512_loop ++
      (evm_mulmod_reduce512_write_result ++ evm_mulmod_epilogue)) a i h

/-- `evm_mulmod_reduce512_write_result` sits at byte offset 308 (after `init`
    and the 71-instruction `loop`) within the total reducer program. -/
theorem evm_mulmod_reduce512_write_result_code_sub (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + BitVec.ofNat 64 308) evm_mulmod_reduce512_write_result) a = some i →
      (CodeReq.ofProg base evm_mulmod_reduce512) a = some i := by
  intro a i h
  refine CodeReq.ofProg_mono_append_right base evm_mulmod_reduce512_init
    (evm_mulmod_reduce512_loop ++
      (evm_mulmod_reduce512_write_result ++ evm_mulmod_epilogue)) (by decide) a i ?_
  refine CodeReq.ofProg_mono_append_right (base + BitVec.ofNat 64 24) evm_mulmod_reduce512_loop
    (evm_mulmod_reduce512_write_result ++ evm_mulmod_epilogue) (by decide) a i ?_
  rw [evm_mulmod_reduce512_loop_length,
    show (base + BitVec.ofNat 64 24) + BitVec.ofNat 64 (4 * 71) = base + BitVec.ofNat 64 308 from by
      bv_omega]
  exact CodeReq.ofProg_mono_append_left (base + BitVec.ofNat 64 308)
    evm_mulmod_reduce512_write_result evm_mulmod_epilogue a i h

/-- `evm_mulmod_epilogue` is the final instruction (byte offset 340) of the
    total reducer program. -/
theorem evm_mulmod_epilogue_code_sub (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + BitVec.ofNat 64 340) evm_mulmod_epilogue) a = some i →
      (CodeReq.ofProg base evm_mulmod_reduce512) a = some i := by
  intro a i h
  refine CodeReq.ofProg_mono_append_right base evm_mulmod_reduce512_init
    (evm_mulmod_reduce512_loop ++
      (evm_mulmod_reduce512_write_result ++ evm_mulmod_epilogue)) (by decide) a i ?_
  refine CodeReq.ofProg_mono_append_right (base + BitVec.ofNat 64 24) evm_mulmod_reduce512_loop
    (evm_mulmod_reduce512_write_result ++ evm_mulmod_epilogue) (by decide) a i ?_
  rw [evm_mulmod_reduce512_loop_length,
    show (base + BitVec.ofNat 64 24) + BitVec.ofNat 64 (4 * 71) = base + BitVec.ofNat 64 308 from by
      bv_omega]
  refine CodeReq.ofProg_mono_append_right (base + BitVec.ofNat 64 308) evm_mulmod_reduce512_write_result
    evm_mulmod_epilogue (by decide) a i ?_
  rw [evm_mulmod_reduce512_write_result_length,
    show (base + BitVec.ofNat 64 308) + BitVec.ofNat 64 (4 * 8) = base + BitVec.ofNat 64 340 from by
      bv_omega]
  exact h

/-- `evm_mulmod_reduce512_init` lifted into the total reducer program code:
    it zeroes the remainder accumulator and arms `x16 = sp - 104` / `x18 = 8`. -/
theorem evm_mulmod_reduce512_init_total_spec_within (sp base : Word)
    (v16Old v18Old r0 r1 r2 r3 : Word) :
    cpsTripleWithin 6 base (base + 24) (CodeReq.ofProg base evm_mulmod_reduce512)
      ((.x12 ↦ᵣ sp) ** (.x16 ↦ᵣ v16Old) ** (.x18 ↦ᵣ v18Old) ** (.x0 ↦ᵣ 0) **
       ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3))
      ((.x12 ↦ᵣ sp) ** (.x16 ↦ᵣ (sp + signExtend12 (3992 : BitVec 12))) **
       (.x18 ↦ᵣ (signExtend12 (8 : BitVec 12))) ** (.x0 ↦ᵣ 0) **
       ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ (0 : Word))) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_init_code_sub base)
    (h := evm_mulmod_reduce512_init_spec_within sp base v16Old v18Old r0 r1 r2 r3)

/-- `evm_mulmod_reduce512_write_result` lifted into the total reducer program
    code (byte offset 308): copies the reduced remainder into the result slots. -/
theorem evm_mulmod_reduce512_write_result_total_spec_within (sp base : Word)
    (v5Old r0 r1 r2 r3 m0 m1 m2 m3 : Word) :
    cpsTripleWithin 8 (base + 308) (base + 308 + 32) (CodeReq.ofProg base evm_mulmod_reduce512)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5Old) **
       ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ m3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ r3)) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_write_result_code_sub base)
    (h := evm_mulmod_reduce512_write_result_spec_within sp (base + BitVec.ofNat 64 308)
      v5Old r0 r1 r2 r3 m0 m1 m2 m3)

/-- `evm_mulmod_epilogue` lifted into the total reducer program code (byte
    offset 340): the final `ADDI x12, x12, 64` restoring the result base. -/
theorem evm_mulmod_epilogue_total_spec_within (sp base : Word) :
    cpsTripleWithin 1 (base + 340) (base + 340 + 4) (CodeReq.ofProg base evm_mulmod_reduce512)
      (.x12 ↦ᵣ sp)
      (.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_epilogue_code_sub base)
    (h := evm_mulmod_epilogue_spec_within sp (base + BitVec.ofNat 64 340))

/-- The reducer prologue and main loop composed: `init` zeroes the accumulator
    and arms the pointer/counter (`x16 = sp - 104`, `x18 = 8`), then the
    eight-limb `loop` folds the product window `limbChain (sp - 104) limbs 8`
    into the remainder, landing at byte offset 308 with the reduced value
    `mulModReduceOuterFoldCarry n limbs 0 8` in the accumulator. The scratch
    registers, modulus, and product window are framed across `init`. -/
theorem evm_mulmod_reduce512_init_loop_spec_within
    (sp base : Word) (v16Old v18Old r0 r1 r2 r3 : Word) (n : EvmWord) (limbs : Nat → Word) :
    cpsTripleWithin (6 + (2 + 66 * 64 + 2 + 1) * 8) base (base + 24 + 284)
      (CodeReq.ofProg base evm_mulmod_reduce512)
      (((.x12 ↦ᵣ sp) ** (.x16 ↦ᵣ v16Old) ** (.x18 ↦ᵣ v18Old) ** (.x0 ↦ᵣ 0) **
        ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3)) **
       ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x8 ** regOwn .x10 ** regOwn .x11 **
         regOwn .x13 ** regOwn .x17 ** regOwn .x15 ** regOwn .x19 ** regOwn .x20 **
         ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
         ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
         ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
         ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)) **
        limbChain (sp + signExtend12 (3992 : BitVec 12)) limbs 8))
      (mulModReduceBitLoopPost sp (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) n **
        regOwn .x16 ** regOwn .x18 **
        limbChain (sp + signExtend12 (3992 : BitVec 12)) limbs 8) := by
  have hframed_init := cpsTripleWithin_frameR
    ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x8 ** regOwn .x10 ** regOwn .x11 **
      regOwn .x13 ** regOwn .x17 ** regOwn .x15 ** regOwn .x19 ** regOwn .x20 **
      ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
      ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
      ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
      ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)) **
      limbChain (sp + signExtend12 (3992 : BitVec 12)) limbs 8)
    (pcFree_sepConj (by pcFree) (limbChain_pcFree _ _ _))
    (evm_mulmod_reduce512_init_total_spec_within sp base v16Old v18Old r0 r1 r2 r3)
  refine cpsTripleWithin_seq_perm_same_cr ?_ hframed_init
    (evm_mulmod_reduce512_loop_total_spec_within sp base
      (sp + signExtend12 (3992 : BitVec 12)) (0 : EvmWord) n limbs)
  intro h hp
  unfold outerEntryCore mulModReduceCompareMem
  rw [show BitVec.ofNat 64 8 = signExtend12 (8 : BitVec 12) from by decide]
  simp only [EvmWord.getLimbN_zero]
  xperm_hyp hp

/-- `write_result` with its scratch register `x5` carried as `regOwn` rather than
    pinned: the phase's first instruction (`LD x5, [x12 + 224]`) overwrites `x5`
    regardless of its incoming value, so the loop's owned `x5` feeds straight in. -/
theorem evm_mulmod_reduce512_write_result_regown_spec_within (sp base : Word)
    (r0 r1 r2 r3 m0 m1 m2 m3 : Word) :
    cpsTripleWithin 8 (base + 308) (base + 308 + 32) (CodeReq.ofProg base evm_mulmod_reduce512)
      (((.x12 ↦ᵣ sp) **
        ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3) **
        ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ m0) **
        ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ m1) **
        ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ m2) **
        ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ m3)) ** regOwn .x5)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ r3)) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn ?_
  intro v5
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hp => hp)
    (evm_mulmod_reduce512_write_result_total_spec_within sp base v5 r0 r1 r2 r3 m0 m1 m2 m3)

/-- Prologue, main loop, and result-writeback composed: after `init ;; loop`
    leaves the reduced value `R = mulModReduceOuterFoldCarry n limbs 0 8` in the
    accumulator window, `write_result` copies its four limbs into the EVM result
    slots `sp + 64 .. sp + 88`. Lands at byte offset 340 (where the epilogue
    begins). The loop's owned scratch registers and the (now-spent) product
    window are framed across `write_result`. -/
theorem evm_mulmod_reduce512_init_loop_wr_spec_within
    (sp base : Word) (v16Old v18Old r0 r1 r2 r3 : Word) (n : EvmWord) (limbs : Nat → Word) :
    cpsTripleWithin (6 + (2 + 66 * 64 + 2 + 1) * 8 + 8) base (base + 308 + 32)
      (CodeReq.ofProg base evm_mulmod_reduce512)
      (((.x12 ↦ᵣ sp) ** (.x16 ↦ᵣ v16Old) ** (.x18 ↦ᵣ v18Old) ** (.x0 ↦ᵣ 0) **
        ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3)) **
       ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x8 ** regOwn .x10 ** regOwn .x11 **
         regOwn .x13 ** regOwn .x17 ** regOwn .x15 ** regOwn .x19 ** regOwn .x20 **
         ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
         ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
         ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
         ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)) **
        limbChain (sp + signExtend12 (3992 : BitVec 12)) limbs 8))
      (((.x12 ↦ᵣ sp) **
        (.x5 ↦ᵣ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 3) **
        ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 0) **
        ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 1) **
        ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 2) **
        ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 3) **
        ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 0) **
        ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 1) **
        ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 2) **
        ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 3)) **
       (((.x15 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
         regOwn .x6 ** regOwn .x7 ** regOwn .x8 ** regOwn .x10 ** regOwn .x11 ** regOwn .x13 **
         regOwn .x17 ** regOwn .x19 ** regOwn .x20 ** regOwn .x16 ** regOwn .x18) **
        limbChain (sp + signExtend12 (3992 : BitVec 12)) limbs 8)) := by
  have hil := evm_mulmod_reduce512_init_loop_spec_within sp base v16Old v18Old r0 r1 r2 r3 n limbs
  rw [show (base : Word) + 24 + 284 = base + 308 from by bv_omega] at hil
  have hwr := cpsTripleWithin_frameR
    (((.x15 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x8 ** regOwn .x10 ** regOwn .x11 ** regOwn .x13 **
      regOwn .x17 ** regOwn .x19 ** regOwn .x20 ** regOwn .x16 ** regOwn .x18) **
      limbChain (sp + signExtend12 (3992 : BitVec 12)) limbs 8)
    (pcFree_sepConj (by pcFree) (limbChain_pcFree _ _ _))
    (evm_mulmod_reduce512_write_result_regown_spec_within sp base
      (EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 0)
      (EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 1)
      (EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 2)
      (EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 3)
      (EvmWord.getLimbN n 0) (EvmWord.getLimbN n 1)
      (EvmWord.getLimbN n 2) (EvmWord.getLimbN n 3))
  refine cpsTripleWithin_seq_perm_same_cr ?_ hil hwr
  intro h hp
  unfold mulModReduceBitLoopPost mulModReduceCompareMem at hp
  xperm_hyp hp

/-- The full 512-bit-by-256-bit MULMOD reducer, end to end. Given the 512-bit
    product as eight 64-bit limbs (`limbChain (sp - 104) limbs 8`) and the
    256-bit modulus `n` in its slots, `evm_mulmod_reduce512` leaves the reduced
    value `R = mulModReduceOuterFoldCarry n limbs 0 8` in the EVM result slots
    `sp + 64 .. sp + 88` and restores the result base pointer (`x12 = sp + 64`). -/
theorem evm_mulmod_reduce512_spec_within
    (sp base : Word) (v16Old v18Old r0 r1 r2 r3 : Word) (n : EvmWord) (limbs : Nat → Word) :
    cpsTripleWithin (6 + (2 + 66 * 64 + 2 + 1) * 8 + 8 + 1) base (base + 344)
      (CodeReq.ofProg base evm_mulmod_reduce512)
      (((.x12 ↦ᵣ sp) ** (.x16 ↦ᵣ v16Old) ** (.x18 ↦ᵣ v18Old) ** (.x0 ↦ᵣ 0) **
        ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3)) **
       ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x8 ** regOwn .x10 ** regOwn .x11 **
         regOwn .x13 ** regOwn .x17 ** regOwn .x15 ** regOwn .x19 ** regOwn .x20 **
         ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
         ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
         ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
         ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)) **
        limbChain (sp + signExtend12 (3992 : BitVec 12)) limbs 8))
      ((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
       (((.x5 ↦ᵣ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 3) **
         ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 0) **
         ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 1) **
         ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 2) **
         ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 3) **
         ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 0) **
         ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 1) **
         ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 2) **
         ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 3)) **
        (((.x15 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x8 ** regOwn .x10 ** regOwn .x11 ** regOwn .x13 **
          regOwn .x17 ** regOwn .x19 ** regOwn .x20 ** regOwn .x16 ** regOwn .x18) **
         limbChain (sp + signExtend12 (3992 : BitVec 12)) limbs 8))) := by
  have hilwr := evm_mulmod_reduce512_init_loop_wr_spec_within sp base v16Old v18Old r0 r1 r2 r3 n limbs
  rw [show (base : Word) + 308 + 32 = base + 340 from by bv_omega] at hilwr
  have hepi := cpsTripleWithin_frameR
    (((.x5 ↦ᵣ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 3) **
      ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 0) **
      ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 1) **
      ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 2) **
      ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 3) **
      ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 0) **
      ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 1) **
      ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 2) **
      ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 3)) **
     (((.x15 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x8 ** regOwn .x10 ** regOwn .x11 ** regOwn .x13 **
       regOwn .x17 ** regOwn .x19 ** regOwn .x20 ** regOwn .x16 ** regOwn .x18) **
      limbChain (sp + signExtend12 (3992 : BitVec 12)) limbs 8))
    (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (limbChain_pcFree _ _ _)))
    (evm_mulmod_epilogue_total_spec_within sp base)
  rw [show (base : Word) + 340 + 4 = base + 344 from by bv_omega] at hepi
  refine cpsTripleWithin_seq_perm_same_cr ?_ hilwr hepi
  intro h hp
  xperm_hyp hp

end EvmAsm.Evm64
