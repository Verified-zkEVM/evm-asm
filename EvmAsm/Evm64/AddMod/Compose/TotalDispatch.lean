/-
  EvmAsm.Evm64.AddMod.Compose.TotalDispatch

  Phase-3 M5 for total ADDMOD (issue #9704): the three-way dispatch.

  Composes the dispatch prefix (`prologue ;; phase1_carry ;; n_zero_test`)
  with the three proven branch arms (zero / no-carry / carry) into the
  UNCONDITIONAL top-level triple `evm_addmod_total_stack_spec_within`
  (byte 0 → 864 over the common region `C`): from the ADDMOD dispatch entry
  (`x12 = sp`, operands `a`/`b`/`N` on the EVM stack) to
  `addmodLdResultOwned (sp+32) (EvmWord.addmod a b N)`, with no domain
  hypotheses beyond the code/alignment/disjointness side conditions.

  The two runtime branch points are resolved by meta-level case analysis
  (`by_cases` on `N = 0` and on the 257-bit add overflow): in each case the
  dead branch arm carries a contradictory pure fact, so
  `cpsBranchWithin_takenPath` / `_ntakenPath` collapse the branch into a
  plain triple that chains with the surviving arm.
-/

import EvmAsm.Evm64.AddMod.Compose.ZeroNoCarryArms

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64

-- ============================================================================
-- Pure helpers: the OR-fold N-zero test vs the fromLimbs modulus
-- ============================================================================

/-- If the 4-limb OR-fold is zero, every limb is zero. -/
theorem or4_eq_zero {n0 n1 n2 n3 : Word}
    (h : n0 ||| n1 ||| n2 ||| n3 = 0) :
    n0 = 0 ∧ n1 = 0 ∧ n2 = 0 ∧ n3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i _
    have hb := congrArg (fun w => BitVec.getLsbD w i) h
    simp only [BitVec.getLsbD_or] at hb
    rw [show BitVec.getLsbD (0 : Word) i = false from by simp] at hb ⊢
    rcases Bool.or_eq_false_iff.mp hb with ⟨h012, h3⟩
    rcases Bool.or_eq_false_iff.mp h012 with ⟨h01, h2⟩
    rcases Bool.or_eq_false_iff.mp h01 with ⟨h0, h1⟩
    first | exact h0 | exact h1 | exact h2 | exact h3

/-- If the 4-limb OR-fold is nonzero, the assembled modulus is nonzero. -/
theorem fromLimbs_ne_zero_of_or4 {n0 n1 n2 n3 : Word}
    (h : ¬(n0 ||| n1 ||| n2 ||| n3 = 0)) :
    EvmWord.fromLimbs ![n0, n1, n2, n3] ≠ 0 := by
  intro hzero
  apply h
  have h0 : n0 = 0 := by
    have := congrArg (fun w => EvmWord.getLimbN w 0) hzero
    simpa [EvmWord.getLimbN_fromLimbs_gen_0] using this
  have h1 : n1 = 0 := by
    have := congrArg (fun w => EvmWord.getLimbN w 1) hzero
    simpa [EvmWord.getLimbN_fromLimbs_gen_1] using this
  have h2 : n2 = 0 := by
    have := congrArg (fun w => EvmWord.getLimbN w 2) hzero
    simpa [EvmWord.getLimbN_fromLimbs_gen_2] using this
  have h3 : n3 = 0 := by
    have := congrArg (fun w => EvmWord.getLimbN w 3) hzero
    simpa [EvmWord.getLimbN_fromLimbs_gen_3] using this
  rw [h0, h1, h2, h3]
  decide

-- ============================================================================
-- Dispatch prefix: prologue ;; phase1_carry (byte 0 → 124) over C
-- ============================================================================

/-- The 257-bit overflow bit of `a + b` (the value `evm_add` leaves in `x5`,
    folded via `evm_add_stack_carry3_eq_overflow`). -/
def addmodOverflowBit (a b : EvmWord) : Word :=
  if a.toNat + b.toNat ≥ 2 ^ 256 then (1 : Word) else 0

/-- The dispatch prefix over `C`: the 4-limb add prologue followed by the
    carry-parking `MV x7, x5`. Lands `x12 = sp+32`, the truncated sum at
    `sp+32..56`, the overflow bit in `x5` AND `x7` (the latter with the raw
    `+ signExtend12 0` shape phase1 produces), `x11` at the limb-3 partial
    carry, and `x6` shed to owned (its junk carry-chain value dies at the
    N-zero test). -/
theorem evm_addmod_dispatch_prefix_spec_within
    (bt sp : Word) (x5v x6v x7v x11v : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word)
    (a b : EvmWord) :
    cpsTripleWithin (30 + 1) bt (bt + 124)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ x7v) ** (.x6 ↦ᵣ x6v) ** (.x5 ↦ᵣ x5v) **
       (.x11 ↦ᵣ x11v) ** evmWordIs sp a ** evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x6 **
       (.x5 ↦ᵣ addmodOverflowBit a b) **
       (.x7 ↦ᵣ (addmodOverflowBit a b + signExtend12 (0 : BitVec 12))) **
       (.x11 ↦ᵣ (if BitVec.ult (a.getLimbN 3 + b.getLimbN 3) (b.getLimbN 3)
                 then (1 : Word) else 0)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a + b)) := by
  -- prologue over C (bt → bt+120)
  have hprol := carry_block_in_C
    (totalCode := evm_addmod_total_program_code bt mo1 mo2 mo3 moNC)
    (calleeCode := evm_mod_callable_code_v5 calleeEntry)
    (fun ad i h => evm_addmod_total_program_code_prologue_sub ad i h)
    (evm_addmod_prologue_stack_named_spec_within sp bt a b x7v x6v x5v x11v)
  -- phase1 over C (bt+120 → bt+124), with the dead incoming x7 owned
  have hph1 : cpsTripleWithin 1 (bt + 120) ((bt + 120) + 4)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (regOwn .x7 ** (.x5 ↦ᵣ addmodOverflowBit a b))
      ((.x5 ↦ᵣ addmodOverflowBit a b) **
       (.x7 ↦ᵣ (addmodOverflowBit a b + signExtend12 (0 : BitVec 12)))) := by
    refine cpsTripleWithin_pre_regOwn (fun vOld => ?_)
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
      (carry_block_in_C
        (totalCode := evm_addmod_total_program_code bt mo1 mo2 mo3 moNC)
        (calleeCode := evm_mod_callable_code_v5 calleeEntry)
        (fun ad i h => evm_addmod_total_program_code_phase1_carry_sub ad i h)
        (evm_addmod_phase1_carry_spec_within (addmodOverflowBit a b) vOld (bt + 120)))
  rw [show (bt + 120) + 4 = bt + 124 from by bv_omega] at hph1
  -- frame phase1 with everything it does not touch
  have hph1F := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x6 **
     (.x11 ↦ᵣ (if BitVec.ult (a.getLimbN 3 + b.getLimbN 3) (b.getLimbN 3)
               then (1 : Word) else 0)) **
     evmWordIs sp a ** evmWordIs (sp + 32) (a + b))
    (by unfold evmWordIs; pcFree)
    hph1
  -- the carry3 chain the prologue leaves in x5 equals the overflow bit
  have hov := evm_add_stack_carry3_eq_overflow a b
  simp only at hov
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?post)
    (cpsTripleWithin_seq_perm_same_cr ?mid hprol hph1F)
  case mid =>
    intro h hp
    simp only [evmAddModPrologueStackPost_unfold] at hp
    rw [hov] at hp
    rw [show (if a.toNat + b.toNat ≥ 2 ^ 256 then (1 : Word) else 0)
        = addmodOverflowBit a b from rfl] at hp
    exact sepConj_mono
      (sepConj_mono (regIs_implies_regOwn .x7) (fun _ x => x))
      (sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn .x6)
          (fun _ x => x)))
      h (by xperm_hyp hp)
  case post =>
    xperm_hyp hq

-- ============================================================================
-- The ADDMOD dispatch entry state and the post-prefix frame
-- ============================================================================

/-- The full ADDMOD dispatch entry state (byte 0): `x12 = sp`, the operands
    `a`/`b` on the EVM stack and the modulus limbs at `sp+64..88`, generic
    dispatcher registers, the S1/S2/S3 park cells, and the MOD-callable
    scratch cells below `sp` (the band's top four cells at `sp..sp+24` are
    the `a` word itself). All cells are stated relative `F = sp + 32`, the
    post-prologue frame pointer, to match the branch-arm preconditions. -/
def addmodTotalEntry (sp : Word)
    (x1v x2v x5v x6v x7v x9v x10v x11v : Word) (a b : EvmWord)
    (n0 n1 n2 n3 : Word)
    (sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3 : Word)
    (u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
     scratch_un0 scratchMem : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1v) ** (.x2 ↦ᵣ x2v) **
  (.x5 ↦ᵣ x5v) ** (.x6 ↦ᵣ x6v) ** (.x7 ↦ᵣ x7v) ** (.x9 ↦ᵣ x9v) **
  (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) **
  evmWordIs sp a ** evmWordIs (sp + 32) b **
  (((sp + 32) + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
  (((sp + 32) + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
  (((sp + 32) + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
  (((sp + 32) + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
  (((sp + 32) + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
  (((sp + 32) + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
  (((sp + 32) + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
  (((sp + 32) + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
  (((sp + 32) + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
  (((sp + 32) + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
  (((sp + 32) + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
  (((sp + 32) + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3) **
  (((sp + 32) + signExtend12 (3840 : BitVec 12)) ↦ₘ sm0) **
  (((sp + 32) + signExtend12 (3848 : BitVec 12)) ↦ₘ sm1) **
  (((sp + 32) + signExtend12 (3856 : BitVec 12)) ↦ₘ sm2) **
  (((sp + 32) + signExtend12 (3864 : BitVec 12)) ↦ₘ sm3) **
  (((sp + 32) + signExtend12 (4056 : BitVec 12)) ↦ₘ u0) **
  (((sp + 32) + signExtend12 (4048 : BitVec 12)) ↦ₘ u1) **
  (((sp + 32) + signExtend12 (4040 : BitVec 12)) ↦ₘ u2) **
  (((sp + 32) + signExtend12 (4032 : BitVec 12)) ↦ₘ u3) **
  (((sp + 32) + signExtend12 (4024 : BitVec 12)) ↦ₘ u4) **
  (((sp + 32) + signExtend12 (4016 : BitVec 12)) ↦ₘ u5) **
  (((sp + 32) + signExtend12 (4008 : BitVec 12)) ↦ₘ u6) **
  (((sp + 32) + signExtend12 (4000 : BitVec 12)) ↦ₘ u7) **
  (((sp + 32) + signExtend12 (3992 : BitVec 12)) ↦ₘ shiftMem) **
  (((sp + 32) + signExtend12 (3984 : BitVec 12)) ↦ₘ nMem) **
  (((sp + 32) + signExtend12 (3976 : BitVec 12)) ↦ₘ jMem) **
  (((sp + 32) + signExtend12 (3968 : BitVec 12)) ↦ₘ retMem) **
  (((sp + 32) + signExtend12 (3960 : BitVec 12)) ↦ₘ dMem) **
  (((sp + 32) + signExtend12 (3952 : BitVec 12)) ↦ₘ dloMem) **
  (((sp + 32) + signExtend12 (3944 : BitVec 12)) ↦ₘ scratch_un0) **
  (((sp + 32) + signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)

theorem addmodTotalEntry_pcFree (sp : Word)
    (x1v x2v x5v x6v x7v x9v x10v x11v : Word) (a b : EvmWord)
    (n0 n1 n2 n3 : Word)
    (sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3 : Word)
    (u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
     scratch_un0 scratchMem : Word) :
    (addmodTotalEntry sp x1v x2v x5v x6v x7v x9v x10v x11v a b
      n0 n1 n2 n3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
      u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
      scratch_un0 scratchMem).pcFree := by
  unfold addmodTotalEntry evmWordIs
  pcFree

/-- Everything the N-zero test does not touch, in the post-prefix state:
    the untouched dispatcher registers, `x7`/`x11` at their post-prefix
    values, the `a` word and the truncated sum, and all park/scratch cells. -/
def addmodPostPrefixRest (sp : Word)
    (x1v x2v x9v x10v : Word) (a b : EvmWord)
    (sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3 : Word)
    (u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
     scratch_un0 scratchMem : Word) : Assertion :=
  (.x1 ↦ᵣ x1v) ** (.x2 ↦ᵣ x2v) ** (.x9 ↦ᵣ x9v) ** (.x10 ↦ᵣ x10v) **
  (.x7 ↦ᵣ (addmodOverflowBit a b + signExtend12 (0 : BitVec 12))) **
  (.x11 ↦ᵣ (if BitVec.ult (a.getLimbN 3 + b.getLimbN 3) (b.getLimbN 3)
            then (1 : Word) else 0)) **
  evmWordIs sp a ** evmWordIs (sp + 32) (a + b) **
  (((sp + 32) + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
  (((sp + 32) + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
  (((sp + 32) + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
  (((sp + 32) + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
  (((sp + 32) + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
  (((sp + 32) + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
  (((sp + 32) + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
  (((sp + 32) + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3) **
  (((sp + 32) + signExtend12 (3840 : BitVec 12)) ↦ₘ sm0) **
  (((sp + 32) + signExtend12 (3848 : BitVec 12)) ↦ₘ sm1) **
  (((sp + 32) + signExtend12 (3856 : BitVec 12)) ↦ₘ sm2) **
  (((sp + 32) + signExtend12 (3864 : BitVec 12)) ↦ₘ sm3) **
  (((sp + 32) + signExtend12 (4056 : BitVec 12)) ↦ₘ u0) **
  (((sp + 32) + signExtend12 (4048 : BitVec 12)) ↦ₘ u1) **
  (((sp + 32) + signExtend12 (4040 : BitVec 12)) ↦ₘ u2) **
  (((sp + 32) + signExtend12 (4032 : BitVec 12)) ↦ₘ u3) **
  (((sp + 32) + signExtend12 (4024 : BitVec 12)) ↦ₘ u4) **
  (((sp + 32) + signExtend12 (4016 : BitVec 12)) ↦ₘ u5) **
  (((sp + 32) + signExtend12 (4008 : BitVec 12)) ↦ₘ u6) **
  (((sp + 32) + signExtend12 (4000 : BitVec 12)) ↦ₘ u7) **
  (((sp + 32) + signExtend12 (3992 : BitVec 12)) ↦ₘ shiftMem) **
  (((sp + 32) + signExtend12 (3984 : BitVec 12)) ↦ₘ nMem) **
  (((sp + 32) + signExtend12 (3976 : BitVec 12)) ↦ₘ jMem) **
  (((sp + 32) + signExtend12 (3968 : BitVec 12)) ↦ₘ retMem) **
  (((sp + 32) + signExtend12 (3960 : BitVec 12)) ↦ₘ dMem) **
  (((sp + 32) + signExtend12 (3952 : BitVec 12)) ↦ₘ dloMem) **
  (((sp + 32) + signExtend12 (3944 : BitVec 12)) ↦ₘ scratch_un0) **
  (((sp + 32) + signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)

theorem addmodPostPrefixRest_pcFree (sp : Word)
    (x1v x2v x9v x10v : Word) (a b : EvmWord)
    (sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3 : Word)
    (u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
     scratch_un0 scratchMem : Word) :
    (addmodPostPrefixRest sp x1v x2v x9v x10v a b
      sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
      u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
      scratch_un0 scratchMem).pcFree := by
  unfold addmodPostPrefixRest evmWordIs
  pcFree

/-- The N-zero-test post cells (common to both branch targets), at `F = sp+32`:
    the OR-fold in `x6`, the last modulus limb in `x5`, and the modulus cells. -/
def addmodNZeroCells (sp : Word) (n0 n1 n2 n3 : Word) : Assertion :=
  (.x12 ↦ᵣ (sp + 32)) ** (.x6 ↦ᵣ (n0 ||| n1 ||| n2 ||| n3)) ** (.x5 ↦ᵣ n3) **
  (.x0 ↦ᵣ (0 : Word)) **
  (((sp + 32) + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
  (((sp + 32) + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
  (((sp + 32) + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
  (((sp + 32) + signExtend12 (56 : BitVec 12)) ↦ₘ n3)

/-- Dispatch prefix + N-zero test as a two-way branch over `C` (byte 0 →
    {844 with `N = 0`, 156 with `N ≠ 0`}), from the full ADDMOD entry. The
    pure branch fact leads each target post so the dead arm is refutable by
    direct destructuring. -/
theorem evm_addmod_dispatch_branch_spec_within
    (bt sp : Word)
    (x1v x2v x5v x6v x7v x9v x10v x11v : Word) (a b : EvmWord)
    (n0 n1 n2 n3 : Word)
    (sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3 : Word)
    (u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
     scratch_un0 scratchMem : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word) :
    cpsBranchWithin ((30 + 1) + 8) bt
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (addmodTotalEntry sp x1v x2v x5v x6v x7v x9v x10v x11v a b
        n0 n1 n2 n3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
        u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
        scratch_un0 scratchMem)
      (bt + 844)
        ((⌜n0 ||| n1 ||| n2 ||| n3 = 0⌝ ** addmodNZeroCells sp n0 n1 n2 n3) **
         addmodPostPrefixRest sp x1v x2v x9v x10v a b
           sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
           u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
           scratch_un0 scratchMem)
      (bt + 156)
        ((⌜¬(n0 ||| n1 ||| n2 ||| n3 = 0)⌝ ** addmodNZeroCells sp n0 n1 n2 n3) **
         addmodPostPrefixRest sp x1v x2v x9v x10v a b
           sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
           u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
           scratch_un0 scratchMem) := by
  -- the prefix, framed with the untouched remainder of the entry
  have hpre := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1v) ** (.x2 ↦ᵣ x2v) ** (.x9 ↦ᵣ x9v) **
     (.x10 ↦ᵣ x10v) **
     (((sp + 32) + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
     (((sp + 32) + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
     (((sp + 32) + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
     (((sp + 32) + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
     (((sp + 32) + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
     (((sp + 32) + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
     (((sp + 32) + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
     (((sp + 32) + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
     (((sp + 32) + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
     (((sp + 32) + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
     (((sp + 32) + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
     (((sp + 32) + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3) **
     (((sp + 32) + signExtend12 (3840 : BitVec 12)) ↦ₘ sm0) **
     (((sp + 32) + signExtend12 (3848 : BitVec 12)) ↦ₘ sm1) **
     (((sp + 32) + signExtend12 (3856 : BitVec 12)) ↦ₘ sm2) **
     (((sp + 32) + signExtend12 (3864 : BitVec 12)) ↦ₘ sm3) **
     (((sp + 32) + signExtend12 (4056 : BitVec 12)) ↦ₘ u0) **
     (((sp + 32) + signExtend12 (4048 : BitVec 12)) ↦ₘ u1) **
     (((sp + 32) + signExtend12 (4040 : BitVec 12)) ↦ₘ u2) **
     (((sp + 32) + signExtend12 (4032 : BitVec 12)) ↦ₘ u3) **
     (((sp + 32) + signExtend12 (4024 : BitVec 12)) ↦ₘ u4) **
     (((sp + 32) + signExtend12 (4016 : BitVec 12)) ↦ₘ u5) **
     (((sp + 32) + signExtend12 (4008 : BitVec 12)) ↦ₘ u6) **
     (((sp + 32) + signExtend12 (4000 : BitVec 12)) ↦ₘ u7) **
     (((sp + 32) + signExtend12 (3992 : BitVec 12)) ↦ₘ shiftMem) **
     (((sp + 32) + signExtend12 (3984 : BitVec 12)) ↦ₘ nMem) **
     (((sp + 32) + signExtend12 (3976 : BitVec 12)) ↦ₘ jMem) **
     (((sp + 32) + signExtend12 (3968 : BitVec 12)) ↦ₘ retMem) **
     (((sp + 32) + signExtend12 (3960 : BitVec 12)) ↦ₘ dMem) **
     (((sp + 32) + signExtend12 (3952 : BitVec 12)) ↦ₘ dloMem) **
     (((sp + 32) + signExtend12 (3944 : BitVec 12)) ↦ₘ scratch_un0) **
     (((sp + 32) + signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem))
    (by pcFree)
    (evm_addmod_dispatch_prefix_spec_within bt sp x5v x6v x7v x11v
      mo1 mo2 mo3 moNC calleeEntry a b)
  -- the N-zero test as a branch over C, with the dead incoming x6 owned and
  -- the pure fact moved to the front of each target post
  have hnz : cpsBranchWithin 8 (bt + 124)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ addmodOverflowBit a b) **
        (.x0 ↦ᵣ (0 : Word)) **
        (((sp + 32) + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        (((sp + 32) + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        (((sp + 32) + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        (((sp + 32) + signExtend12 (56 : BitVec 12)) ↦ₘ n3)) ** regOwn .x6)
      ((bt + 124) + 28 + signExtend13 (692 : BitVec 13))
        (⌜n0 ||| n1 ||| n2 ||| n3 = 0⌝ ** addmodNZeroCells sp n0 n1 n2 n3)
      ((bt + 124) + 32)
        (⌜¬(n0 ||| n1 ||| n2 ||| n3 = 0)⌝ ** addmodNZeroCells sp n0 n1 n2 n3) := by
    refine cpsBranchWithin_of_forall_regIs_to_regOwn (fun v6Old => ?_)
    have hraw := evm_addmod_phase2_n_zero_test_spec_within
      (sp + 32) (addmodOverflowBit a b) v6Old n0 n1 n2 n3 (bt + 124) 692
    simp only at hraw
    have hC := cpsBranchWithin_extend_code
      (cr' := addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (hmono := fun ad i h =>
        CodeReq.union_mono_left ad i
          (evm_addmod_total_program_code_n_zero_test_sub ad i h))
      hraw
    refine cpsBranchWithin_weaken (fun h hp => ?_) (fun h hq => ?_) (fun h hq => ?_) hC
    · xperm_hyp hp
    · unfold addmodNZeroCells
      xperm_hyp hq
    · unfold addmodNZeroCells
      xperm_hyp hq
  rw [show (bt + 124) + 28 + signExtend13 (692 : BitVec 13) = bt + 844 from by
    rw [show signExtend13 (692 : BitVec 13) = (692 : Word) from by decide]
    bv_omega] at hnz
  rw [show (bt + 124) + 32 = bt + 156 from by bv_omega] at hnz
  -- frame the branch with the post-prefix remainder
  have hnzF := cpsBranchWithin_frameR
    (addmodPostPrefixRest sp x1v x2v x9v x10v a b
      sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
      u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
      scratch_un0 scratchMem)
    (addmodPostPrefixRest_pcFree sp x1v x2v x9v x10v a b
      sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 sm0 sm1 sm2 sm3
      u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem
      scratch_un0 scratchMem)
    hnz
  refine cpsBranchWithin_weaken (fun h hp => ?pre) (fun _ hq => hq) (fun _ hq => hq)
    (cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr ?mid hpre hnzF)
  case pre =>
    unfold addmodTotalEntry at hp
    xperm_hyp hp
  case mid =>
    intro h hp
    unfold addmodPostPrefixRest
    xperm_hyp hp

end EvmAsm.Evm64.AddMod.Compose
