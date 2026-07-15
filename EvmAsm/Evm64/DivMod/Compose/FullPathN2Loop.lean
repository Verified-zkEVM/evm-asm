/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2Loop

  Preloop+loop composition for n=2 (shift≠0 path).
  Composes:
  - Preloop: evm_div_n2_to_loopSetup_spec_within (base → base+448)
  - Loop: divK_loop_n2_unified_spec_within (base+448 → base+904)

  Follows the pattern of FullPathN3Loop.lean but for n=2.

  Legacy carry note: this lift module still exposes the raw `Carry2NzAll`
  package. It is a compatibility surface for older full-path composition;
  final/public v4 n=2 stack work should use selected/reachable carry wrappers.

  Merged: LoopUnifiedN2 (Bool-parameterized unified loop composition for n=2).
  Issue #262: Unify max/call branch paths via Bool parameter.
  For n=2, the loop runs 3 iterations (j=2, j=1, j=0).
-/

-- `FullPathN4Loop` (5-hop) transitively reaches `FullPathN2` via
-- `LoopIterN4 → LoopBodyN4 → LoopBody → Compose → FullPathN2`.
import EvmAsm.Evm64.DivMod.Compose.FullPathN4Loop
import EvmAsm.Evm64.DivMod.LoopComposeN2

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (bv6_toNat_3 word_shl3_0 jpred_2)

-- ============================================================================
-- Double-addback () two-iteration (j=1, j=0) unified composition
-- Same pattern as divK_loop_n3_unified_spec_within but with n=2 per-iteration specs
-- ============================================================================

/-- Unified n=2 two-iteration  loop composition for j=1 and j=0,
    parameterized by `(bltu_1 bltu_0 : Bool)`.
    Covers all 4 path combinations (max×max, call×call, max×call, call×max).
    Dispatches to existing  per-path specs in LoopComposeN2.lean. -/
theorem divK_loop_n2_iter10_unified_spec_within (bltu_1 bltu_0 : Bool)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    -- Unified branch conditions (using iterN2 for j=0)
    (hbltu_1 : bltu_1 = BitVec.ult u2 v1)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN2 bltu_1 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 404 (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN2Iter10PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN2Iter10Post bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratch_un0) := by
  cases bltu_1 <;> cases bltu_0 <;> simp only [iterN2_true, iterN2_false] at hbltu_0
  · -- (false, false) = max×max
    have hbltu_1' : ¬BitVec.ult u2 v1 := by
      rw [show BitVec.ult u2 v1 = false from hbltu_1.symm]; decide
    have hbltu_0' : ¬BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    have hMM := divK_loop_n2_max_max_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old base
      hbltu_1' hbltu_0' hcarry2
    have hMMF := cpsTripleWithin_frameR
     ((sp + signExtend12 3968 ↦ₘ retMem) **
      (sp + signExtend12 3960 ↦ₘ dMem) **
      (sp + signExtend12 3952 ↦ₘ dloMem) **
      (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1)
      (by pcFree) hMM
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun h hp => by delta loopN2Iter10PreWithScratch at hp; xperm_hyp hp)
      (fun h hp => by delta loopN2Iter10Post; xperm_hyp hp)
      hMMF
  · -- (false, true) = max×call
    have hbltu_1' : ¬BitVec.ult u2 v1 := by
      rw [show BitVec.ult u2 v1 = false from hbltu_1.symm]; decide
    have hbltu_0' : BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 :=
      hbltu_0.symm ▸ rfl
    have hMC := divK_loop_n2_max_call_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 base halign


      hbltu_1' hbltu_0' hcarry2
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by delta loopN2Iter10Post; exact hp)
      hMC
  · -- (true, false) = call×max
    have hbltu_1' : BitVec.ult u2 v1 := hbltu_1.symm ▸ rfl
    have hbltu_0' : ¬BitVec.ult (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    have hCM := divK_loop_n2_call_max_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 base halign


      hbltu_1' hbltu_0' hcarry2
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by delta loopN2Iter10Post; exact hp)
      hCM
  · -- (true, true) = call×call
    have hbltu_1' : BitVec.ult u2 v1 := hbltu_1.symm ▸ rfl
    have hbltu_0' : BitVec.ult (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 :=
      hbltu_0.symm ▸ rfl
    have hCC := divK_loop_n2_call_call_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 base halign


      hbltu_1' hbltu_0' hcarry2
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by delta loopN2Iter10Post; exact hp)
      hCC

/-- No-NOP variant of `divK_loop_n2_iter10_unified_spec_within`. -/
theorem divK_loop_n2_iter10_unified_spec_within_noNop (bltu_1 bltu_0 : Bool)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_1 : bltu_1 = BitVec.ult u2 v1)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN2 bltu_1 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 404 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopN2Iter10PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN2Iter10Post bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratch_un0) := by
  cases bltu_1 <;> cases bltu_0 <;> simp only [iterN2_true, iterN2_false] at hbltu_0
  · have hbltu_1' : ¬BitVec.ult u2 v1 := by
      rw [show BitVec.ult u2 v1 = false from hbltu_1.symm]; decide
    have hbltu_0' : ¬BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    have hMM := divK_loop_n2_max_max_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old base
      hbltu_1' hbltu_0' hcarry2
    have hMMF := cpsTripleWithin_frameR
     ((sp + signExtend12 3968 ↦ₘ retMem) **
      (sp + signExtend12 3960 ↦ₘ dMem) **
      (sp + signExtend12 3952 ↦ₘ dloMem) **
      (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1)
      (by pcFree) hMM
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun h hp => by delta loopN2Iter10PreWithScratch at hp; xperm_hyp hp)
      (fun h hp => by delta loopN2Iter10Post; xperm_hyp hp)
      hMMF
  · have hbltu_1' : ¬BitVec.ult u2 v1 := by
      rw [show BitVec.ult u2 v1 = false from hbltu_1.symm]; decide
    have hbltu_0' : BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 :=
      hbltu_0.symm ▸ rfl
    have hMC := divK_loop_n2_max_call_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 base halign
      hbltu_1' hbltu_0' hcarry2
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by delta loopN2Iter10Post; exact hp)
      hMC
  · have hbltu_1' : BitVec.ult u2 v1 := hbltu_1.symm ▸ rfl
    have hbltu_0' : ¬BitVec.ult (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    have hCM := divK_loop_n2_call_max_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 base halign
      hbltu_1' hbltu_0' hcarry2
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by delta loopN2Iter10Post; exact hp)
      hCM
  · have hbltu_1' : BitVec.ult u2 v1 := hbltu_1.symm ▸ rfl
    have hbltu_0' : BitVec.ult (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 :=
      hbltu_0.symm ▸ rfl
    have hCC := divK_loop_n2_call_call_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 base halign
      hbltu_1' hbltu_0' hcarry2
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by delta loopN2Iter10Post; exact hp)
      hCC

-- ============================================================================
-- Full three-iteration : compose j=2 with iter10
-- Postcondition uses @[irreducible] loopN2UnifiedPost
-- ============================================================================

/-- Three-iteration  composition when j=2 is max (bltu_2 = false).
    Composes j=2  max spec with the 2-iteration iter10 unified  spec. -/
theorem divK_loop_n2_max_iter10_spec_within (bltu_1 bltu_0 : Bool)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_1 u0_orig_0
     q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : ¬BitVec.ult u2 v1)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN2 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 556 (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN2PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN2UnifiedPost false bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 retMem dMem dloMem scratch_un0) := by
  let r2 := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J2 := divK_loop_body_n2_max_unified_j2_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q2Old base

    hbltu_2
    (hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  intro_lets at J2
  have J2f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) ** (q_addr_1 ↦ₘ q1Old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) ** (q_addr_0 ↦ₘ q0Old) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1)
    (by pcFree) J2
  have H10 := divK_loop_n2_iter10_unified_spec_within bltu_1 bltu_0
    sp (2 : Word) ((2 : Word) <<< (3 : BitVec 6).toNat) u_base_2 q_addr_2
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    r2.1 r2.2.2.2.2.1
    v0 v1 v2 v3
    u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    u0_orig_0 q1Old q0Old
    retMem dMem dloMem scratch_un0 base halign


    hbltu_1 hbltu_0 hcarry2
  have H10f := cpsTripleWithin_frameR
    (((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1))
    (by pcFree) H10
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN2Max loopExitPostN2 loopExitPost at hp
      delta loopN2Iter10PreWithScratch loopN2Iter10Pre at ⊢
      simp only [] at hp ⊢
      have hj' := jpred_2
      rw [hj', u_j2_0_eq_j1_4088, u_j2_4088_eq_j1_4080,
          u_j2_4080_eq_j1_4072, u_j2_4072_eq_j1_4064] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J2f H10f
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopN2PreWithScratch loopN2Pre at hp
      rw [loopBodyN2J2Pre_unfold]
      xperm_hyp hp)
    (fun h hp => by
      delta loopN2UnifiedPost loopN2Iter10Post at hp ⊢
      simp only [iterN2_false, Bool.false_eq_true, ↓reduceIte] at hp ⊢
      cases bltu_1 <;> cases bltu_0 <;> xperm_hyp hp)
    full

/-- No-NOP variant of `divK_loop_n2_max_iter10_spec_within`. -/
theorem divK_loop_n2_max_iter10_spec_within_noNop (bltu_1 bltu_0 : Bool)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_1 u0_orig_0
     q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : ¬BitVec.ult u2 v1)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN2 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 556 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopN2PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN2UnifiedPost false bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 retMem dMem dloMem scratch_un0) := by
  let r2 := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J2 := divK_loop_body_n2_max_unified_j2_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q2Old base
    hbltu_2
    (hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  intro_lets at J2
  have J2f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) ** (q_addr_1 ↦ₘ q1Old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) ** (q_addr_0 ↦ₘ q0Old) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1)
    (by pcFree) J2
  have H10 := divK_loop_n2_iter10_unified_spec_within_noNop bltu_1 bltu_0
    sp (2 : Word) ((2 : Word) <<< (3 : BitVec 6).toNat) u_base_2 q_addr_2
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    r2.1 r2.2.2.2.2.1
    v0 v1 v2 v3
    u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    u0_orig_0 q1Old q0Old
    retMem dMem dloMem scratch_un0 base halign
    hbltu_1 hbltu_0 hcarry2
  have H10f := cpsTripleWithin_frameR
    (((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1))
    (by pcFree) H10
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN2Max loopExitPostN2 loopExitPost at hp
      delta loopN2Iter10PreWithScratch loopN2Iter10Pre at ⊢
      simp only [] at hp ⊢
      have hj' := jpred_2
      rw [hj', u_j2_0_eq_j1_4088, u_j2_4088_eq_j1_4080,
          u_j2_4080_eq_j1_4072, u_j2_4072_eq_j1_4064] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J2f H10f
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopN2PreWithScratch loopN2Pre at hp
      rw [loopBodyN2J2Pre_unfold]
      xperm_hyp hp)
    (fun h hp => by
      delta loopN2UnifiedPost loopN2Iter10Post at hp ⊢
      simp only [iterN2_false, Bool.false_eq_true, ↓reduceIte] at hp ⊢
      cases bltu_1 <;> cases bltu_0 <;> xperm_hyp hp)
    full

/-- Three-iteration  composition when j=2 is call (bltu_2 = true).
    Composes j=2  call spec with the 2-iteration iter10 unified  spec. -/
theorem divK_loop_n2_call_iter10_spec_within (bltu_1 bltu_0 : Bool)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_1 u0_orig_0
     q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : BitVec.ult u2 v1)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN2 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 606 (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN2PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN2UnifiedPost true bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 retMem dMem dloMem scratch_un0) := by
  let r2 := iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J2 := divK_loop_body_n2_call_unified_j2_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q2Old retMem dMem dloMem scratch_un0 base halign

    hbltu_2
    (hcarry2 (div128Quot u2 u1 v1) u0 u1 u2 u3 uTop : isAddbackCarry2NzN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  intro_lets at J2
  have J2f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) ** (q_addr_1 ↦ₘ q1Old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J2
  have H10 := divK_loop_n2_iter10_unified_spec_within bltu_1 bltu_0
    sp (2 : Word) ((2 : Word) <<< (3 : BitVec 6).toNat) u_base_2 q_addr_2
    ((mulsubN4 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    r2.1 r2.2.2.2.2.1
    v0 v1 v2 v3
    u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    u0_orig_0 q1Old q0Old
    (base + div128CallRetOff) v1 (div128DLo v1) (div128Un0 u1) base halign


    hbltu_1 hbltu_0 hcarry2
  have H10f := cpsTripleWithin_frameR
    (((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1))
    (by pcFree) H10
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN2Call loopExitPostN2 loopExitPost at hp
      delta loopN2Iter10PreWithScratch loopN2Iter10Pre at ⊢
      simp only [] at hp ⊢
      have hj' := jpred_2
      rw [hj', u_j2_0_eq_j1_4088, u_j2_4088_eq_j1_4080,
          u_j2_4080_eq_j1_4072, u_j2_4072_eq_j1_4064] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J2f H10f
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopN2PreWithScratch loopN2Pre at hp
      rw [loopBodyN2J2CallPre_unfold]
      xperm_hyp hp)
    (fun h hp => by
      delta loopN2UnifiedPost loopN2Iter10Post at hp ⊢
      simp only [iterN2_true, ite_true] at hp ⊢
      cases bltu_1 <;> cases bltu_0 <;> xperm_hyp hp)
    full

/-- No-NOP variant of `divK_loop_n2_call_iter10_spec_within`. -/
theorem divK_loop_n2_call_iter10_spec_within_noNop (bltu_1 bltu_0 : Bool)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_1 u0_orig_0
     q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : BitVec.ult u2 v1)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN2 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 606 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopN2PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN2UnifiedPost true bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 retMem dMem dloMem scratch_un0) := by
  let r2 := iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J2 := divK_loop_body_n2_call_unified_j2_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q2Old retMem dMem dloMem scratch_un0 base halign
    hbltu_2
    (hcarry2 (div128Quot u2 u1 v1) u0 u1 u2 u3 uTop : isAddbackCarry2NzN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  intro_lets at J2
  have J2f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) ** (q_addr_1 ↦ₘ q1Old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J2
  have H10 := divK_loop_n2_iter10_unified_spec_within_noNop bltu_1 bltu_0
    sp (2 : Word) ((2 : Word) <<< (3 : BitVec 6).toNat) u_base_2 q_addr_2
    ((mulsubN4 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    r2.1 r2.2.2.2.2.1
    v0 v1 v2 v3
    u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    u0_orig_0 q1Old q0Old
    (base + div128CallRetOff) v1 (div128DLo v1) (div128Un0 u1) base halign
    hbltu_1 hbltu_0 hcarry2
  have H10f := cpsTripleWithin_frameR
    (((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1))
    (by pcFree) H10
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN2Call loopExitPostN2 loopExitPost at hp
      delta loopN2Iter10PreWithScratch loopN2Iter10Pre at ⊢
      simp only [] at hp ⊢
      have hj' := jpred_2
      rw [hj', u_j2_0_eq_j1_4088, u_j2_4088_eq_j1_4080,
          u_j2_4080_eq_j1_4072, u_j2_4072_eq_j1_4064] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J2f H10f
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopN2PreWithScratch loopN2Pre at hp
      rw [loopBodyN2J2CallPre_unfold]
      xperm_hyp hp)
    (fun h hp => by
      delta loopN2UnifiedPost loopN2Iter10Post at hp ⊢
      simp only [iterN2_true, ite_true] at hp ⊢
      cases bltu_1 <;> cases bltu_0 <;> xperm_hyp hp)
    full

-- ============================================================================
-- Final  unified dispatch: cases bltu_2, delegates to max/call  lemmas
-- ============================================================================

/-- Unified n=2 three-iteration  loop composition, parameterized by
    `(bltu_2 bltu_1 bltu_0 : Bool)`.  Covers all 8 path combinations.
    Dispatches to divK_loop_n2_max_iter10_spec_within / divK_loop_n2_call_iter10_spec_within. -/
theorem divK_loop_n2_unified_spec_within (bltu_2 bltu_1 bltu_0 : Bool)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_1 u0_orig_0
     q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : bltu_2 = BitVec.ult u2 v1)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN2 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 606 (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN2PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN2UnifiedPost bltu_2 bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 retMem dMem dloMem scratch_un0) := by
  cases bltu_2 <;> simp only [iterN2_true, iterN2_false] at hbltu_1 hbltu_0
  · -- bltu_2 = false → max
    have hbltu_2' : ¬BitVec.ult u2 v1 := by
      rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    exact cpsTripleWithin_mono_nSteps (by decide) <| divK_loop_n2_max_iter10_spec_within bltu_1 bltu_0
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 base halign


      hbltu_2' hbltu_1 hbltu_0 hcarry2
  · -- bltu_2 = true → call
    have hbltu_2' : BitVec.ult u2 v1 := hbltu_2.symm ▸ rfl
    exact divK_loop_n2_call_iter10_spec_within bltu_1 bltu_0
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 base halign


      hbltu_2' hbltu_1 hbltu_0 hcarry2

/-- No-NOP variant of `divK_loop_n2_unified_spec_within`. -/
theorem divK_loop_n2_unified_spec_within_noNop (bltu_2 bltu_1 bltu_0 : Bool)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_1 u0_orig_0
     q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : bltu_2 = BitVec.ult u2 v1)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN2 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 606 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopN2PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN2UnifiedPost bltu_2 bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 retMem dMem dloMem scratch_un0) := by
  cases bltu_2 <;> simp only [iterN2_true, iterN2_false] at hbltu_1 hbltu_0
  · have hbltu_2' : ¬BitVec.ult u2 v1 := by
      rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    exact cpsTripleWithin_mono_nSteps (by decide) <| divK_loop_n2_max_iter10_spec_within_noNop bltu_1 bltu_0
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 base halign
      hbltu_2' hbltu_1 hbltu_0 hcarry2
  · have hbltu_2' : BitVec.ult u2 v1 := hbltu_2.symm ▸ rfl
    exact divK_loop_n2_call_iter10_spec_within_noNop bltu_1 bltu_0
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 base halign
      hbltu_2' hbltu_1 hbltu_0 hcarry2

-- ============================================================================
-- Address normalization lemmas for n=2 preloop+loop composition
-- Maps uBase(j)/qAddr(j) relative offsets to flat sp+signExtend12 offsets.
-- signExtend12/<<</>> → concrete values via simp, then bv_omega.
-- bv_addr only handles (a+k1)+k2=a+k3; these involve subtraction and shifts,
-- so bv_omega is required. Pattern matches FullPathN3Loop.lean:69.
-- ============================================================================

/-- signExtend12(4) - 2 = 2, for x1 register in loopSetupPost at n=2. -/
theorem x1_val_n2 : signExtend12 (4 : BitVec 12) - (2 : Word) = (2 : Word) := by decide

-- uBase(2) = sp + se(4056) - 16.  Offsets map to flat addresses:
-- uBase(2)+0     = sp+se(4040)  [u0 at iteration j=2]
-- uBase(2)-8     = sp+se(4032)  [u1]
-- uBase(2)-16    = sp+se(4024)  [u2]
-- uBase(2)-24    = sp+se(4016)  [u3]
-- uBase(2)-32    = sp+se(4008)  [uTop]

theorem n2_ub2_off0 {sp : Word} :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) =
    sp + signExtend12 4040 := by
  divmod_addr
theorem n2_ub2_off4088 {sp : Word} :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 =
    sp + signExtend12 4032 := by
  divmod_addr
theorem n2_ub2_off4080 {sp : Word} :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 =
    sp + signExtend12 4024 := by
  divmod_addr
theorem n2_ub2_off4072 {sp : Word} :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 =
    sp + signExtend12 4016 := by
  divmod_addr
theorem n2_ub2_off4064 {sp : Word} :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 =
    sp + signExtend12 4008 := by
  divmod_addr

-- uBase(1)+0 = sp+se(4048), already covered by n3_ub1_off0 (same addresses)
-- uBase(0)+0 = sp+se(4056), already covered by n3_ub0_off0

-- qAddr(j) = sp + se(4088) - j<<<3
theorem n2_qa2 {sp : Word} :
    sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4072 := by
  divmod_addr
-- n2_qa1 = n3_qa1 (same: sp + se(4088) - 8 = sp + se(4080))
-- n2_qa0 = n3_qa0 (same: sp + se(4088) - 0 = sp + se(4088))

-- ============================================================================
-- loopExitPostN2 at j=0: concrete address specialization
-- ============================================================================

/-- Specialize `loopExitPostN2` at `j=0`: all uBase/qAddr offsets become
    flat `sp + signExtend12 K` addresses. Uses the shared u_base_off*_j0 lemmas. -/
theorem loopExitPostN2_j0_eq (sp q_f c3 un0F un1F un2F un3F u4F
    v0 v1 v2 v3 : Word) :
    loopExitPostN2 sp (0 : Word) q_f c3 un0F un1F un2F un3F u4F v0 v1 v2 v3 =
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ signExtend12 4095) **
     (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ sp + signExtend12 4056) **
     (.x7 ↦ᵣ sp + signExtend12 4088) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_f) **
     (.x2 ↦ᵣ un3F) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ un0F) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ un1F) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ un2F) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ un3F) **
     ((sp + signExtend12 4024) ↦ₘ u4F) **
     ((sp + signExtend12 4088) ↦ₘ q_f)) := by
  simp only [loopExitPost_unfold]
  rw [u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
      u_base_off4072_j0, u_base_off4064_j0, u_base_j0, q_addr_j0]
  simp only [bv6_toNat_3, word_shl3_0]
  rw [show (0 : Word) + signExtend12 4095 = signExtend12 4095 from BitVec.zero_add _]

-- ============================================================================
-- Lift unified n=2  loop from sharedDivModCode to divCode
-- ============================================================================

/-- Lift the unified n=2 3-iteration loop spec from sharedDivModCode to divCode.

    Legacy compatibility surface: this still consumes the raw `Carry2NzAll`
    package. New v4 n=2 work should route through selected carry evidence. -/
theorem divK_loop_n2_unified_divCode (bltu_2 bltu_1 bltu_0 : Bool)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_1 u0_orig_0
     q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : bltu_2 = BitVec.ult u2 v1)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN2 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 606 (base + loopBodyOff) (base + denormOff) (divCode base)
      (loopN2PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN2UnifiedPost bltu_2 bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 retMem dMem dloMem scratch_un0) :=
  cpsTripleWithin_mono_nSteps (by decide) <|
  cpsTripleWithin_extend_code (hmono := sharedDivModCode_sub_divCode)
    (divK_loop_n2_unified_spec_within bltu_2 bltu_1 bltu_0
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 base halign


      hbltu_2 hbltu_1 hbltu_0 hcarry2)

end EvmAsm.Evm64
