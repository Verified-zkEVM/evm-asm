/-
  EvmAsm.Evm64.DivMod.LoopUnifiedN1

  Bool-parameterized (unified) loop composition for n=1.
  Issue #262: Unify max/call branch paths via Bool parameter.

  For n=1, the loop runs 4 iterations (j=3, j=2, j=1, j=0).
  Structure:
  1. `divK_loop_n1_iter10_unified_spec (bltu_1 bltu_0 : Bool)`:
     Two-iteration (j=1, j=0) composition -- 4 cases.
  2. `divK_loop_n1_max_iter10_spec` / `divK_loop_n1_call_iter10_spec`:
     Compose j=2 (max or call) with the two-iteration intermediate.
  3. `divK_loop_n1_iter210_unified_spec (bltu_2 bltu_1 bltu_0 : Bool)`:
     Three-iteration -- dispatches via cases on bltu_2.
  4. `divK_loop_n1_max_iter210_spec` / `divK_loop_n1_call_iter210_spec`:
     Compose j=3 (max or call) with the three-iteration intermediate.
  5. `divK_loop_n1_unified_spec (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)`:
     Full four-iteration -- dispatches via cases on bltu_3.
-/

import EvmAsm.Evm64.DivMod.LoopComposeN1

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (jpred_1 jpred_2 jpred_3)

-- ============================================================================
-- Double-addback () two-iteration (j=1, j=0) unified composition
-- Same pattern as divK_loop_n1_iter10_unified_spec but with  per-iteration specs
-- ============================================================================

/-- Unified n=1 two-iteration  loop composition for j=1 and j=0,
    parameterized by `(bltu_1 bltu_0 : Bool)`.
    Covers all 4 path combinations (max×max, call×call, max×call, call×max).
    Dispatches to existing  per-iteration specs in LoopComposeN1.lean. -/
theorem divK_loop_n1_iter10_unified_spec (bltu_1 bltu_0 : Bool)
    (sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1_old q0_old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    -- Validity hypotheses
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    -- Unified branch conditions (using iterN1 for j=0)
    (hbltu_1 : bltu_1 = BitVec.ult u1 v0)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN1 bltu_1 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN1Iter10PreWithScratch sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1_old q0_old
        retMem dMem dloMem scratch_un0)
      (loopN1Iter10Post bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratch_un0) := by
  -- Dispatch to per-iteration  specs via case analysis on (bltu_1, bltu_0)
  cases bltu_1 <;> cases bltu_0 <;> simp only [iterN1_true, iterN1_false] at hbltu_0
  · -- (false, false) = max*max
    have hbltu_1' : ¬BitVec.ult u1 v0 := by
      rw [show BitVec.ult u1 v0 = false from hbltu_1.symm]; decide
    have hbltu_0' : ¬BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0 := by
      rw [show BitVec.ult _ v0 = false from hbltu_0.symm]; decide
    delta loopN1Iter10PreWithScratch loopN1Iter10Pre; simp only []
    let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    -- j=1 max  spec
    have J1 := divK_loop_body_n1_max_unified_j1_spec sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop q1_old base

      hbltu_1'
      (hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    intro_lets at J1
    -- Frame j=1 with u0Orig, q0Old, and scratch
    have J1f := cpsTriple_frameR
      (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (by pcFree) J1
    -- Derive j=0 validity via j=1->j=0 address linking
    -- j=0 max  spec (inputs from j=1 via iterN1Max)
    have J0 := divK_loop_body_n1_max_unified_j0_spec sp (1 : Word)
      ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
      ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
      ((iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
      ((iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
      v0 v1 v2 v3
      u0Orig
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
      q0Old base

      hbltu_0'
      (hcarry2 (signExtend12 4095) u0Orig
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    intro_lets at J0
    -- Frame j=0 with j=1's carried atoms and scratch
    have J0f := cpsTriple_frameR
      (((u_base_1 + signExtend12 4064) ↦ₘ (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
       (q_addr_1 ↦ₘ (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (by pcFree) J0
    -- Compose j=1 and j=0 via address rewriting
    have full := cpsTriple_seq_perm_same_cr
      (fun h hp => by
        delta loopIterPostN1Max loopExitPostN1 loopExitPost at hp
        simp only [] at hp ⊢
        have hj' := jpred_1
        rw [hj', u_n1_j1_0_eq_j0_4088 sp, u_n1_j1_4088_eq_j0_4080 sp,
            u_n1_j1_4080_eq_j0_4072 sp, u_n1_j1_4072_eq_j0_4064 sp] at hp
        rw [sepConj_assoc'] at hp
        xperm_hyp hp)
      J1f J0f
    -- Bridge to unified  postcondition
    exact cpsTriple_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        delta loopN1Iter10Post loopIterPostN1
        simp only [iterN1_false, sepConj_emp_right']
        xperm_hyp hp)
      full
  · -- (false, true) = max*call
    have hbltu_1' : ¬BitVec.ult u1 v0 := by
      rw [show BitVec.ult u1 v0 = false from hbltu_1.symm]; decide
    have hbltu_0' : BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0 :=
      hbltu_0.symm ▸ rfl
    delta loopN1Iter10PreWithScratch loopN1Iter10Pre; simp only []
    let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    -- j=1 max  spec
    have J1 := divK_loop_body_n1_max_unified_j1_spec sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop q1_old base

      hbltu_1'
      (hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    intro_lets at J1
    have J1f := cpsTriple_frameR
      (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (by pcFree) J1
    -- j=0 call  spec (includes scratch in pre/post)
    have J0 := divK_loop_body_n1_call_unified_j0_spec sp (1 : Word)
      ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
      ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
      ((iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
      ((iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
      v0 v1 v2 v3
      u0Orig
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
      q0Old retMem dMem dloMem scratch_un0 base
      halign

      hbltu_0'
      (hcarry2 (div128Quot (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 u0Orig v0) u0Orig
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    intro_lets at J0
    -- Frame j=0 with j=1's carried atoms only
    have J0f := cpsTriple_frameR
      (((u_base_1 + signExtend12 4064) ↦ₘ (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
       (q_addr_1 ↦ₘ (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
      (by pcFree) J0
    have full := cpsTriple_seq_perm_same_cr
      (fun h hp => by
        delta loopIterPostN1Max loopExitPostN1 loopExitPost at hp
        simp only [] at hp ⊢
        have hj' := jpred_1
        rw [hj', u_n1_j1_0_eq_j0_4088 sp, u_n1_j1_4088_eq_j0_4080 sp,
            u_n1_j1_4080_eq_j0_4072 sp, u_n1_j1_4072_eq_j0_4064 sp] at hp
        rw [sepConj_assoc'] at hp
        xperm_hyp hp)
      J1f J0f
    exact cpsTriple_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        delta loopN1Iter10Post loopIterPostN1
        simp only [iterN1_false, sepConj_emp_right']
        xperm_hyp hp)
      full
  · -- (true, false) = call*max
    have hbltu_1' : BitVec.ult u1 v0 := hbltu_1.symm ▸ rfl
    have hbltu_0' : ¬BitVec.ult (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0 := by
      rw [show BitVec.ult _ v0 = false from hbltu_0.symm]; decide
    delta loopN1Iter10PreWithScratch loopN1Iter10Pre; simp only []
    let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    -- j=1 call  spec (includes scratch)
    have J1 := divK_loop_body_n1_call_unified_j1_spec sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop q1_old retMem dMem dloMem scratch_un0 base
      halign

      hbltu_1'
      (hcarry2 (div128Quot u1 u0 v0) u0 u1 u2 u3 uTop : isAddbackCarry2NzN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    intro_lets at J1
    -- Frame j=1 with u0Orig, q0Old only (scratch is in call spec)
    have J1f := cpsTriple_frameR
      (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old))
      (by pcFree) J1
    -- j=0 max  spec (no scratch)
    have J0 := divK_loop_body_n1_max_unified_j0_spec sp (1 : Word)
      ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
      ((mulsubN4 (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
      ((iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
      ((iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
      v0 v1 v2 v3
      u0Orig
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
      q0Old base

      hbltu_0'
      (hcarry2 (signExtend12 4095) u0Orig
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    intro_lets at J0
    -- Frame j=0 with j=1's carried atoms + j=1 scratch (persists from call)
    have J0f := cpsTriple_frameR
      (((u_base_1 + signExtend12 4064) ↦ₘ (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
       (q_addr_1 ↦ₘ (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1) **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v0) **
       (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
       (sp + signExtend12 3944 ↦ₘ div128Un0 u0))
      (by pcFree) J0
    have full := cpsTriple_seq_perm_same_cr
      (fun h hp => by
        delta loopIterPostN1Call loopExitPostN1 loopExitPost at hp
        simp only [] at hp ⊢
        have hj' := jpred_1
        rw [hj', u_n1_j1_0_eq_j0_4088 sp, u_n1_j1_4088_eq_j0_4080 sp,
            u_n1_j1_4080_eq_j0_4072 sp, u_n1_j1_4072_eq_j0_4064 sp] at hp
        rw [sepConj_assoc'] at hp
        xperm_hyp hp)
      J1f J0f
    exact cpsTriple_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        delta loopN1Iter10Post loopIterPostN1
        simp only [iterN1_true, sepConj_emp_right']
        xperm_hyp hp)
      full
  · -- (true, true) = call*call
    have hbltu_1' : BitVec.ult u1 v0 := hbltu_1.symm ▸ rfl
    have hbltu_0' : BitVec.ult (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0 :=
      hbltu_0.symm ▸ rfl
    delta loopN1Iter10PreWithScratch loopN1Iter10Pre; simp only []
    let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    -- j=1 call  spec (includes scratch)
    have J1 := divK_loop_body_n1_call_unified_j1_spec sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop q1_old retMem dMem dloMem scratch_un0 base
      halign

      hbltu_1'
      (hcarry2 (div128Quot u1 u0 v0) u0 u1 u2 u3 uTop : isAddbackCarry2NzN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    intro_lets at J1
    -- Frame j=1 with u0Orig, q0Old only
    have J1f := cpsTriple_frameR
      (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old))
      (by pcFree) J1
    -- j=0 call  spec (includes scratch -- j=0 overwrites j=1's scratch)
    have J0 := divK_loop_body_n1_call_unified_j0_spec sp (1 : Word)
      ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
      ((mulsubN4 (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
      ((iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
      ((iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
      v0 v1 v2 v3
      u0Orig
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
      q0Old
      (base + 516) v0 (div128DLo v0) (div128Un0 u0) base
      halign

      hbltu_0'
      (hcarry2 (div128Quot (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 u0Orig v0) u0Orig
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    intro_lets at J0
    -- Frame j=0 with j=1's carried atoms only
    have J0f := cpsTriple_frameR
      (((u_base_1 + signExtend12 4064) ↦ₘ (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
       (q_addr_1 ↦ₘ (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
      (by pcFree) J0
    have full := cpsTriple_seq_perm_same_cr
      (fun h hp => by
        delta loopIterPostN1Call loopExitPostN1 loopExitPost at hp
        simp only [] at hp ⊢
        have hj' := jpred_1
        rw [hj', u_n1_j1_0_eq_j0_4088 sp, u_n1_j1_4088_eq_j0_4080 sp,
            u_n1_j1_4080_eq_j0_4072 sp, u_n1_j1_4072_eq_j0_4064 sp] at hp
        rw [sepConj_assoc'] at hp
        xperm_hyp hp)
      J1f J0f
    exact cpsTriple_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        delta loopN1Iter10Post loopIterPostN1
        simp only [iterN1_true, sepConj_emp_right']
        xperm_hyp hp)
      full

-- ============================================================================
-- Three-iteration : compose j=2 with iter10 -- separate lemmas per case
-- Postcondition uses @[irreducible] loopN1Iter210Post
-- ============================================================================

/-- Three-iteration  composition when j=2 is max (bltu_2 = false).
    Composes j=2  max spec with the 2-iteration iter10 unified  spec. -/
theorem divK_loop_n1_max_iter10_spec (bltu_1 bltu_0 : Bool)
    (sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_1 u0_orig_0
     q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_2 : ¬BitVec.ult u1 v0)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN1Iter210PreWithScratch sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN1Iter210Post false bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 retMem dMem dloMem scratch_un0) := by
  let r2 := iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- j=2 max  spec
  have J2 := divK_loop_body_n1_max_unified_j2_spec sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q2_old base

    hbltu_2
    (hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  intro_lets at J2
  -- Frame j=2 with iter10 extra atoms and scratch
  have J2f := cpsTriple_frameR
    (((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) ** (q_addr_1 ↦ₘ q1Old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) ** (q_addr_0 ↦ₘ q0Old) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) J2
  -- iter10  unified spec (inputs from j=2 max  output)
  have H10 := divK_loop_n1_iter10_unified_spec bltu_1 bltu_0
    sp (2 : Word) ((2 : Word) <<< (3 : BitVec 6).toNat) u_base_2 q_addr_2
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    r2.1 r2.2.2.2.2.1
    v0 v1 v2 v3
    u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    u0_orig_0 q1Old q0Old
    retMem dMem dloMem scratch_un0 base halign



    hbltu_1 hbltu_0 hcarry2
  -- Frame iter10 with j=2 carried atoms
  have H10f := cpsTriple_frameR
    (((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1))
    (by pcFree) H10
  -- Compose j=2 and iter10
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1Max loopExitPostN1 loopExitPost at hp
      delta loopN1Iter10PreWithScratch loopN1Iter10Pre at ⊢
      simp only [] at hp ⊢
      have hj' := jpred_2
      rw [hj', u_n1_j2_0_eq_j1_4088 sp, u_n1_j2_4088_eq_j1_4080 sp,
          u_n1_j2_4080_eq_j1_4072 sp, u_n1_j2_4072_eq_j1_4064 sp] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J2f H10f
  exact cpsTriple_weaken
    (fun h hp => by delta loopN1Iter210PreWithScratch loopN1Iter210Pre at hp; xperm_hyp hp)
    (fun h hp => by
      delta loopN1Iter210Post loopN1Iter10Post at hp ⊢
      simp only [iterN1_false, Bool.false_eq_true, ↓reduceIte] at hp ⊢
      cases bltu_1 <;> cases bltu_0 <;> xperm_hyp hp)
    full

/-- Three-iteration  composition when j=2 is call (bltu_2 = true).
    Composes j=2  call spec with the 2-iteration iter10 unified  spec. -/
theorem divK_loop_n1_call_iter10_spec (bltu_1 bltu_0 : Bool)
    (sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_1 u0_orig_0
     q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_2 : BitVec.ult u1 v0)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN1Iter210PreWithScratch sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN1Iter210Post true bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 retMem dMem dloMem scratch_un0) := by
  let r2 := iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- j=2 call  spec (includes scratch)
  have J2 := divK_loop_body_n1_call_unified_j2_spec sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q2_old retMem dMem dloMem scratch_un0 base halign

    hbltu_2
    (hcarry2 (div128Quot u1 u0 v0) u0 u1 u2 u3 uTop : isAddbackCarry2NzN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  intro_lets at J2
  -- Frame j=2 with iter10 extra atoms only (scratch consumed by call)
  have J2f := cpsTriple_frameR
    (((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) ** (q_addr_1 ↦ₘ q1Old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J2
  -- iter10  unified spec (inputs from j=2 call  output, scratch = j=2 call values)
  have H10 := divK_loop_n1_iter10_unified_spec bltu_1 bltu_0
    sp (2 : Word) ((2 : Word) <<< (3 : BitVec 6).toNat) u_base_2 q_addr_2
    ((mulsubN4 (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    r2.1 r2.2.2.2.2.1
    v0 v1 v2 v3
    u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    u0_orig_0 q1Old q0Old
    (base + 516) v0 (div128DLo v0) (div128Un0 u0) base halign



    hbltu_1 hbltu_0 hcarry2
  -- Frame iter10 with j=2 carried atoms
  have H10f := cpsTriple_frameR
    (((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1))
    (by pcFree) H10
  -- Compose j=2 and iter10
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1Call loopExitPostN1 loopExitPost at hp
      delta loopN1Iter10PreWithScratch loopN1Iter10Pre at ⊢
      simp only [] at hp ⊢
      have hj' := jpred_2
      rw [hj', u_n1_j2_0_eq_j1_4088 sp, u_n1_j2_4088_eq_j1_4080 sp,
          u_n1_j2_4080_eq_j1_4072 sp, u_n1_j2_4072_eq_j1_4064 sp] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J2f H10f
  exact cpsTriple_weaken
    (fun h hp => by delta loopN1Iter210PreWithScratch loopN1Iter210Pre at hp; xperm_hyp hp)
    (fun h hp => by
      delta loopN1Iter210Post loopN1Iter10Post at hp ⊢
      simp only [iterN1_true, ite_true] at hp ⊢
      cases bltu_1 <;> cases bltu_0 <;> xperm_hyp hp)
    full

-- ============================================================================
-- Three-iteration  unified dispatch: cases bltu_2
-- ============================================================================

/-- Unified n=1 three-iteration  loop composition, parameterized by
    `(bltu_2 bltu_1 bltu_0 : Bool)`.  Covers all 8 path combinations.
    Dispatches to divK_loop_n1_max_iter10_spec / divK_loop_n1_call_iter10_spec. -/
theorem divK_loop_n1_iter210_unified_spec (bltu_2 bltu_1 bltu_0 : Bool)
    (sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_1 u0_orig_0
     q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_2 : bltu_2 = BitVec.ult u1 v0)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN1 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN1 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN1Iter210PreWithScratch sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN1Iter210Post bltu_2 bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 retMem dMem dloMem scratch_un0) := by
  cases bltu_2 <;> simp only [iterN1_true, iterN1_false] at hbltu_1 hbltu_0
  · -- bltu_2 = false -> max
    have hbltu_2' : ¬BitVec.ult u1 v0 := by
      rw [show BitVec.ult u1 v0 = false from hbltu_2.symm]; decide
    exact divK_loop_n1_max_iter10_spec bltu_1 bltu_0
      sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2_old q1_old q0_old
      retMem dMem dloMem scratch_un0 base halign




      hbltu_2' hbltu_1 hbltu_0 hcarry2
  · -- bltu_2 = true -> call
    have hbltu_2' : BitVec.ult u1 v0 := hbltu_2.symm ▸ rfl
    exact divK_loop_n1_call_iter10_spec bltu_1 bltu_0
      sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2_old q1_old q0_old
      retMem dMem dloMem scratch_un0 base halign




      hbltu_2' hbltu_1 hbltu_0 hcarry2

-- ============================================================================
-- Full four-iteration : compose j=3 with iter210 -- separate lemmas per case
-- Postcondition uses @[irreducible] loopN1UnifiedPost
-- ============================================================================

/-- Four-iteration  composition when j=3 is max (bltu_3 = false).
    Composes j=3  max spec with the 3-iteration iter210 unified  spec. -/
theorem divK_loop_n1_max_iter210_spec (bltu_2 bltu_1 bltu_0 : Bool)
    (sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_2 u0_orig_1 u0_orig_0
     q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_3 : ¬BitVec.ult u1 v0)
    (hbltu_2 : bltu_2 = BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN1PreWithScratch sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0 q3Old q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN1UnifiedPost false bltu_2 bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0 retMem dMem dloMem scratch_un0) := by
  let r3 := iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- j=3 max  spec
  have J3 := divK_loop_body_n1_max_unified_j3_spec sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q3_old base

    hbltu_3
    (hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  intro_lets at J3
  -- Frame j=3 with iter210 extra atoms and scratch
  have J3f := cpsTriple_frameR
    (((u_base_2 + signExtend12 0) ↦ₘ u0_orig_2) ** (q_addr_2 ↦ₘ q2Old) **
     ((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) ** (q_addr_1 ↦ₘ q1Old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) ** (q_addr_0 ↦ₘ q0Old) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) J3
  -- iter210  unified spec (inputs from j=3 max  output)
  have H210 := divK_loop_n1_iter210_unified_spec bltu_2 bltu_1 bltu_0
    sp (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) u_base_3 q_addr_3
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    r3.1 r3.2.2.2.2.1
    v0 v1 v2 v3
    u0_orig_2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    u0_orig_1 u0_orig_0
    q2Old q1Old q0Old
    retMem dMem dloMem scratch_un0 base halign
    hbltu_2 hbltu_1 hbltu_0 hcarry2
  -- Frame iter210 with j=3 carried atoms
  have H210f := cpsTriple_frameR
    (((u_base_3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) ** (q_addr_3 ↦ₘ r3.1))
    (by pcFree) H210
  -- Compose j=3 and iter210
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1Max loopExitPostN1 loopExitPost at hp
      delta loopN1Iter210PreWithScratch loopN1Iter210Pre at ⊢
      simp only [] at hp ⊢
      have hj' := jpred_3
      rw [hj', u_n1_j3_0_eq_j2_4088 sp, u_n1_j3_4088_eq_j2_4080 sp,
          u_n1_j3_4080_eq_j2_4072 sp, u_n1_j3_4072_eq_j2_4064 sp] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J3f H210f
  exact cpsTriple_weaken
    (fun h hp => by delta loopN1PreWithScratch loopN1Pre at hp; xperm_hyp hp)
    (fun h hp => by
      delta loopN1UnifiedPost loopN1Iter210Post loopN1Iter10Post loopIterPostN1 at hp ⊢
      simp only [iterN1_false, Bool.false_eq_true, ↓reduceIte, sepConj_emp_right'] at hp ⊢
      have hr3 : r3 = iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop := rfl
      have hub3 : u_base_3 = sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat := rfl
      have hqa3 : q_addr_3 = sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat := rfl
      simp only [hr3, hub3, hqa3] at hp
      rw [sepConj_assoc'] at hp
      cases bltu_2 <;> cases bltu_1 <;> cases bltu_0 <;> xperm_hyp hp)
    full

/-- Four-iteration  composition when j=3 is call (bltu_3 = true).
    Composes j=3  call spec with the 3-iteration iter210 unified  spec. -/
theorem divK_loop_n1_call_iter210_spec (bltu_2 bltu_1 bltu_0 : Bool)
    (sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_2 u0_orig_1 u0_orig_0
     q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_3 : BitVec.ult u1 v0)
    (hbltu_2 : bltu_2 = BitVec.ult (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN1PreWithScratch sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0 q3Old q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN1UnifiedPost true bltu_2 bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0 retMem dMem dloMem scratch_un0) := by
  let r3 := iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- j=3 call  spec (includes scratch)
  have J3 := divK_loop_body_n1_call_unified_j3_spec sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q3_old retMem dMem dloMem scratch_un0 base halign
    hbltu_3
    (hcarry2 (div128Quot u1 u0 v0) u0 u1 u2 u3 uTop : isAddbackCarry2NzN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  intro_lets at J3
  -- Frame j=3 with iter210 extra atoms only (scratch consumed by call)
  have J3f := cpsTriple_frameR
    (((u_base_2 + signExtend12 0) ↦ₘ u0_orig_2) ** (q_addr_2 ↦ₘ q2Old) **
     ((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) ** (q_addr_1 ↦ₘ q1Old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J3
  -- iter210  unified spec (inputs from j=3 call  output, scratch = j=3 call values)
  have H210 := divK_loop_n1_iter210_unified_spec bltu_2 bltu_1 bltu_0
    sp (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) u_base_3 q_addr_3
    ((mulsubN4 (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    r3.1 r3.2.2.2.2.1
    v0 v1 v2 v3
    u0_orig_2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    u0_orig_1 u0_orig_0
    q2Old q1Old q0Old
    (base + 516) v0 (div128DLo v0) (div128Un0 u0) base halign
    hbltu_2 hbltu_1 hbltu_0 hcarry2
  -- Frame iter210 with j=3 carried atoms
  have H210f := cpsTriple_frameR
    (((u_base_3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) ** (q_addr_3 ↦ₘ r3.1))
    (by pcFree) H210
  -- Compose j=3 and iter210
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1Call loopExitPostN1 loopExitPost at hp
      delta loopN1Iter210PreWithScratch loopN1Iter210Pre at ⊢
      simp only [] at hp ⊢
      have hj' := jpred_3
      rw [hj', u_n1_j3_0_eq_j2_4088 sp, u_n1_j3_4088_eq_j2_4080 sp,
          u_n1_j3_4080_eq_j2_4072 sp, u_n1_j3_4072_eq_j2_4064 sp] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J3f H210f
  exact cpsTriple_weaken
    (fun h hp => by delta loopN1PreWithScratch loopN1Pre at hp; xperm_hyp hp)
    (fun h hp => by
      delta loopN1UnifiedPost loopN1Iter210Post loopN1Iter10Post loopIterPostN1 at hp ⊢
      simp only [iterN1_true, ite_true, sepConj_emp_right'] at hp ⊢
      have hr3 : r3 = iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := rfl
      have hub3 : u_base_3 = sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat := rfl
      have hqa3 : q_addr_3 = sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat := rfl
      simp only [hr3, hub3, hqa3] at hp
      rw [sepConj_assoc'] at hp
      cases bltu_2 <;> cases bltu_1 <;> cases bltu_0 <;> xperm_hyp hp)
    full

-- ============================================================================
-- Final  unified dispatch: cases bltu_3, delegates to max/call  lemmas
-- ============================================================================

/-- Unified n=1 four-iteration  loop composition, parameterized by
    `(bltu_3 bltu_2 bltu_1 bltu_0 : Bool)`.  Covers all 16 path combinations.
    Dispatches to divK_loop_n1_max_iter210_spec / divK_loop_n1_call_iter210_spec. -/
theorem divK_loop_n1_unified_spec (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_2 u0_orig_1 u0_orig_0
     q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_3 : bltu_3 = BitVec.ult u1 v0)
    (hbltu_2 : bltu_2 = BitVec.ult (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
      (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN1PreWithScratch sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0 q3Old q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0 retMem dMem dloMem scratch_un0) := by
  cases bltu_3 <;> simp only [iterN1_true, iterN1_false] at hbltu_2 hbltu_1 hbltu_0
  · -- bltu_3 = false -> max
    have hbltu_3' : ¬BitVec.ult u1 v0 := by
      rw [show BitVec.ult u1 v0 = false from hbltu_3.symm]; decide
    exact divK_loop_n1_max_iter210_spec bltu_2 bltu_1 bltu_0
      sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0
      q3Old q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 base halign
      hbltu_3' hbltu_2 hbltu_1 hbltu_0 hcarry2
  · -- bltu_3 = true -> call
    have hbltu_3' : BitVec.ult u1 v0 := hbltu_3.symm ▸ rfl
    exact divK_loop_n1_call_iter210_spec bltu_2 bltu_1 bltu_0
      sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0
      q3Old q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 base
      halign
      hbltu_3' hbltu_2 hbltu_1 hbltu_0 hcarry2

end EvmAsm.Evm64
