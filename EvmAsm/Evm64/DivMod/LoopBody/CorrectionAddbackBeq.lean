/-
  EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddbackBeq

  Extracted from `LoopBody.lean` (Section 10c).

  Combined `mulsub + correction_addback + BEQ` spec for both addback-carry
  outcomes (single-addback fall-through and double-addback back-branch).

  Uses public helpers from `LoopBody.lean`:
  - `divK_mulsub_correction_addback_spec_within`
  - `divK_mulsub_correction_addback_named_880_spec_within`
  - `divK_double_addback_beq_named_spec_within`
-/

module

public import EvmAsm.Evm64.DivMod.LoopBody.MulsubCorrectionAddback
public import EvmAsm.Evm64.DivMod.LoopBody.DoubleAddbackBeq
public import EvmAsm.Evm64.DivMod.LoopBody.DoubleAddbackBeqV4NoNop

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Mulsub + correction_addback + BEQ (both carry outcomes)
-- Combined spec: base+516 → base+884 with case-split on addback carry.
-- Uses iterWithDoubleAddback-style postcondition.
-- ============================================================================

/-- Mulsub + correction with addback + BEQ at [108]: when borrow ≠ 0, performs
    first addback and then handles the BEQ:
    - carry ≠ 0 (single addback): BEQ falls through to base+884
    - carry = 0 (double addback): BEQ takes backward branch, second addback, then falls through
    Entry: base+516, Exit: base+884. -/
theorem divK_mulsub_correction_addback_beq_spec_within
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (v1Old v5Old v6Old v7Old v10Old v2Old : Word)
    (base : Word) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
    let c3 := ms.2.2.2.2
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
    -- Double-addback results (only used when carry = 0)
    let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
    -- Final values depend on carry
    let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
                 else qHat + signExtend12 4095
    let un0Out := if carry = 0 then ab'.1 else ab.1
    let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
    let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
    let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
    let u4_out := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
    let carryOut := if carry = 0 then
        addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3
      else carry
    -- Hypothesis: second addback carry nonzero (only needed if first carry = 0)
    (carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) →
    -- Hypothesis: borrow ≠ 0
    (if BitVec.ult uTop c3 then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 130 (base + div128CallRetOff) (base + storeLoopOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x9 ↦ᵣ v1Old) ** (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x2 ↦ᵣ v2Old) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_out) **
       (.x9 ↦ᵣ j) ** (.x5 ↦ᵣ u4_out) ** (.x6 ↦ᵣ uBase) **
       (.x7 ↦ᵣ carryOut) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3Out) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0Out) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1Out) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2Out) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3Out) **
       ((uBase + signExtend12 4064) ↦ₘ u4_out)) := by
  intro uBase ms c3 carry ab ab' q_out un0Out un1Out un2Out un3Out u4_out carryOut
        hcarry2_nz hborrow
  -- 1. Mulsub + first addback (base+516 → base+880)
  have MCA := divK_mulsub_correction_addback_spec_within sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    v1Old v5Old v6Old v7Old v10Old v2Old base

  intro_lets at MCA
  have MCA0 := MCA hborrow
  -- 2. Case split on carry
  by_cases hcarry : carry = 0
  · -- carry = 0: double addback path
    have hq : q_out = qHat + signExtend12 4095 + signExtend12 4095 := if_pos hcarry
    have h0 : un0Out = ab'.1 := if_pos hcarry
    have h1 : un1Out = ab'.2.1 := if_pos hcarry
    have h2 : un2Out = ab'.2.2.1 := if_pos hcarry
    have h3 : un3Out = ab'.2.2.2.1 := if_pos hcarry
    have h4 : u4_out = ab'.2.2.2.2 := if_pos hcarry
    have hc : carryOut = addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 := if_pos hcarry
    rw [hq, h0, h1, h2, h3, h4, hc]
    -- Use named 880 spec (→880 with addbackN4_carry in postcondition)
    have MCA_N := (divK_mulsub_correction_addback_named_880_spec_within sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
      v1Old v5Old v6Old v7Old v10Old v2Old base) hborrow
    simp only [n4McaNamed880Post_unfold] at MCA_N
    -- Rewrite carry to 0
    rw [show addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3 = (0 : Word) from hcarry] at MCA_N
    -- Use named DA spec (880→884 with addbackN4 projections in postcondition)
    have hcarry2 : addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0 :=
      hcarry2_nz hcarry
    have DA := divK_double_addback_beq_named_spec_within sp uBase
      (qHat + signExtend12 4095) v0 v1 v2 v3
      ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2
      base hcarry2
    simp only [n4DoubleAddbackNamedPost_unfold] at DA
    -- Frame DA with extra atoms from MCA_N postcondition
    have DAf := cpsTripleWithin_frameR
      ((.x9 ↦ᵣ j) ** (.x10 ↦ᵣ c3) **
       (sp + signExtend12 3976 ↦ₘ j))
      (by pcFree) DA
    -- Compose MCA_N(→880) with DAf(880→884)
    have full := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) MCA_N DAf
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => by xperm_hyp hp)
        (fun h hp => by
          rw [sepConj_assoc'] at hp
          xperm_hyp hp)
        full
  · -- carry ≠ 0: single addback path (BEQ passthrough)
    have hq : q_out = qHat + signExtend12 4095 := if_neg hcarry
    have h0 : un0Out = ab.1 := if_neg hcarry
    have h1 : un1Out = ab.2.1 := if_neg hcarry
    have h2 : un2Out = ab.2.2.1 := if_neg hcarry
    have h3 : un3Out = ab.2.2.2.1 := if_neg hcarry
    have h4 : u4_out = ab.2.2.2.2 := if_neg hcarry
    have hc : carryOut = carry := if_neg hcarry
    rw [hq, h0, h1, h2, h3, h4, hc]
    -- Use the existing MCA0 (which includes BEQ passthrough) with carry ≠ 0
    exact cpsTripleWithin_mono_nSteps (by decide) (MCA0 hcarry)

/-- No-NOP variant of `divK_mulsub_correction_addback_beq_spec_within`. -/
theorem divK_mulsub_correction_addback_beq_spec_within_noNop
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (v1Old v5Old v6Old v7Old v10Old v2Old : Word)
    (base : Word) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
    let c3 := ms.2.2.2.2
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
    -- Double-addback results (only used when carry = 0)
    let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
    -- Final values depend on carry
    let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
                 else qHat + signExtend12 4095
    let un0Out := if carry = 0 then ab'.1 else ab.1
    let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
    let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
    let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
    let u4_out := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
    let carryOut := if carry = 0 then
        addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3
      else carry
    -- Hypothesis: second addback carry nonzero (only needed if first carry = 0)
    (carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) →
    -- Hypothesis: borrow ≠ 0
    (if BitVec.ult uTop c3 then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 130 (base + div128CallRetOff) (base + storeLoopOff) (divCode_noNop base)
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x9 ↦ᵣ v1Old) ** (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x2 ↦ᵣ v2Old) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_out) **
       (.x9 ↦ᵣ j) ** (.x5 ↦ᵣ u4_out) ** (.x6 ↦ᵣ uBase) **
       (.x7 ↦ᵣ carryOut) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3Out) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0Out) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1Out) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2Out) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3Out) **
       ((uBase + signExtend12 4064) ↦ₘ u4_out)) := by
  intro uBase ms c3 carry ab ab' q_out un0Out un1Out un2Out un3Out u4_out carryOut
        hcarry2_nz hborrow
  -- 1. Mulsub + first addback (base+516 -> base+880)
  have MCA := divK_mulsub_correction_addback_spec_within_noNop sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    v1Old v5Old v6Old v7Old v10Old v2Old base

  intro_lets at MCA
  have MCA0 := MCA hborrow
  -- 2. Case split on carry
  by_cases hcarry : carry = 0
  · -- carry = 0: double addback path
    have hq : q_out = qHat + signExtend12 4095 + signExtend12 4095 := if_pos hcarry
    have h0 : un0Out = ab'.1 := if_pos hcarry
    have h1 : un1Out = ab'.2.1 := if_pos hcarry
    have h2 : un2Out = ab'.2.2.1 := if_pos hcarry
    have h3 : un3Out = ab'.2.2.2.1 := if_pos hcarry
    have h4 : u4_out = ab'.2.2.2.2 := if_pos hcarry
    have hc : carryOut = addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 := if_pos hcarry
    rw [hq, h0, h1, h2, h3, h4, hc]
    -- Use named 880 spec (->880 with addbackN4_carry in postcondition)
    have MCA_N := (divK_mulsub_correction_addback_named_880_spec_within_noNop sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
      v1Old v5Old v6Old v7Old v10Old v2Old base) hborrow
    simp only [n4McaNamed880Post_unfold] at MCA_N
    -- Rewrite carry to 0
    rw [show addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3 = (0 : Word) from hcarry] at MCA_N
    -- Use named DA spec (880->884 with addbackN4 projections in postcondition)
    have hcarry2 : addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0 :=
      hcarry2_nz hcarry
    have DA := divK_double_addback_beq_named_spec_within_noNop sp uBase
      (qHat + signExtend12 4095) v0 v1 v2 v3
      ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2
      base hcarry2
    rw [n4DoubleAddbackNamedPost_unfold] at DA
    -- Frame DA with extra atoms from MCA_N postcondition
    have DAf := cpsTripleWithin_frameR
      ((.x9 ↦ᵣ j) ** (.x10 ↦ᵣ c3) **
       (sp + signExtend12 3976 ↦ₘ j))
      (by pcFree) DA
    -- Compose MCA_N(->880) with DAf(880->884)
    have full := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) MCA_N DAf
    exact cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      full
  · -- carry ≠ 0: single addback path (BEQ passthrough)
    have hq : q_out = qHat + signExtend12 4095 := if_neg hcarry
    have h0 : un0Out = ab.1 := if_neg hcarry
    have h1 : un1Out = ab.2.1 := if_neg hcarry
    have h2 : un2Out = ab.2.2.1 := if_neg hcarry
    have h3 : un3Out = ab.2.2.2.1 := if_neg hcarry
    have h4 : u4_out = ab.2.2.2.2 := if_neg hcarry
    have hc : carryOut = carry := if_neg hcarry
    rw [hq, h0, h1, h2, h3, h4, hc]
    -- Use the existing MCA0 (which includes BEQ passthrough) with carry ≠ 0
    exact cpsTripleWithin_mono_nSteps (by decide) (MCA0 hcarry)

/-- v4 no-NOP variant of `divK_mulsub_correction_addback_beq_spec_within`. -/
theorem divK_mulsub_correction_addback_beq_v4_spec_within_noNop
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (v1Old v5Old v6Old v7Old v10Old v2Old : Word)
    (base : Word) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
    let c3 := ms.2.2.2.2
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
    let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
    let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
                 else qHat + signExtend12 4095
    let un0Out := if carry = 0 then ab'.1 else ab.1
    let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
    let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
    let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
    let u4_out := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
    let carryOut := if carry = 0 then
        addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3
      else carry
    (carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) →
    (if BitVec.ult uTop c3 then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 130 (base + div128CallRetOff) (base + storeLoopOff) (sharedDivModCodeNoNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x9 ↦ᵣ v1Old) ** (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x2 ↦ᵣ v2Old) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_out) **
       (.x9 ↦ᵣ j) ** (.x5 ↦ᵣ u4_out) ** (.x6 ↦ᵣ uBase) **
       (.x7 ↦ᵣ carryOut) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3Out) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0Out) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1Out) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2Out) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3Out) **
       ((uBase + signExtend12 4064) ↦ₘ u4_out)) := by
  intro uBase ms c3 carry ab ab' q_out un0Out un1Out un2Out un3Out u4_out carryOut
        hcarry2_nz hborrow
  by_cases hcarry : carry = 0
  · have hq : q_out = qHat + signExtend12 4095 + signExtend12 4095 := if_pos hcarry
    have h0 : un0Out = ab'.1 := if_pos hcarry
    have h1 : un1Out = ab'.2.1 := if_pos hcarry
    have h2 : un2Out = ab'.2.2.1 := if_pos hcarry
    have h3 : un3Out = ab'.2.2.2.1 := if_pos hcarry
    have h4 : u4_out = ab'.2.2.2.2 := if_pos hcarry
    have hc : carryOut = addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 := if_pos hcarry
    rw [hq, h0, h1, h2, h3, h4, hc]
    have MCA_N := (divK_mulsub_correction_addback_named_880_v4_spec_within_noNop sp qHat j
      v0 v1 v2 v3 u0 u1 u2 u3 uTop v1Old v5Old v6Old v7Old v10Old v2Old base) hborrow
    simp only [n4McaNamed880Post_unfold] at MCA_N
    rw [show addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3 = (0 : Word) from hcarry] at MCA_N
    have hcarry2 : addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0 :=
      hcarry2_nz hcarry
    have DA := divK_double_addback_beq_named_v4_spec_within_noNop sp uBase
      (qHat + signExtend12 4095) v0 v1 v2 v3
      ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2
      base hcarry2
    simp only [n4DoubleAddbackNamedPost_unfold] at DA
    have DAf := cpsTripleWithin_frameR
      ((.x9 ↦ᵣ j) ** (.x10 ↦ᵣ c3) **
       (sp + signExtend12 3976 ↦ₘ j))
      (by pcFree) DA
    have full := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) MCA_N DAf
    exact cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      full
  · have hq : q_out = qHat + signExtend12 4095 := if_neg hcarry
    have h0 : un0Out = ab.1 := if_neg hcarry
    have h1 : un1Out = ab.2.1 := if_neg hcarry
    have h2 : un2Out = ab.2.2.1 := if_neg hcarry
    have h3 : un3Out = ab.2.2.2.1 := if_neg hcarry
    have h4 : u4_out = ab.2.2.2.2 := if_neg hcarry
    have hc : carryOut = carry := if_neg hcarry
    rw [hq, h0, h1, h2, h3, h4, hc]
    have MCA_N := (divK_mulsub_correction_addback_named_880_v4_spec_within_noNop sp qHat j
      v0 v1 v2 v3 u0 u1 u2 u3 uTop v1Old v5Old v6Old v7Old v10Old v2Old base) hborrow
    simp only [n4McaNamed880Post_unfold] at MCA_N
    have BEQ := divK_beq_passthrough_v4_spec_within_noNop base hcarry
    have BEQf := cpsTripleWithin_frameR
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat + signExtend12 4095) **
       (.x9 ↦ᵣ j) ** (.x5 ↦ᵣ ab.2.2.2.2) ** (.x6 ↦ᵣ uBase) **
       (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ ab.2.2.2.1) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ ab.1) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ ab.2.1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ ab.2.2.1) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ ab.2.2.2.1) **
       ((uBase + signExtend12 4064) ↦ₘ ab.2.2.2.2))
      (by pcFree) BEQ
    have full := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) MCA_N BEQf
    have full130 :
        cpsTripleWithin 130 (base + div128CallRetOff) (base + storeLoopOff) (sharedDivModCodeNoNop_v4 base)
          ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
           (.x9 ↦ᵣ v1Old) ** (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
           (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x2 ↦ᵣ v2Old) **
           (.x0 ↦ᵣ 0) **
           (sp + signExtend12 3976 ↦ₘ j) **
           ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
           ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
           ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
           ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
           ((uBase + signExtend12 4064) ↦ₘ uTop))
          (((.x7 ↦ᵣ carry) ** (.x0 ↦ᵣ (0 : Word))) **
           (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat + signExtend12 4095) **
           (.x9 ↦ᵣ j) ** (.x5 ↦ᵣ ab.2.2.2.2) ** (.x6 ↦ᵣ uBase) **
           (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ ab.2.2.2.1) **
           (sp + signExtend12 3976 ↦ₘ j) **
           ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ ab.1) **
           ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ ab.2.1) **
           ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ ab.2.2.1) **
           ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ ab.2.2.2.1) **
           ((uBase + signExtend12 4064) ↦ₘ ab.2.2.2.2)) :=
      cpsTripleWithin_mono_nSteps (by decide) full
    exact cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        rw [sepConj_assoc'] at hp
        xperm_hyp hp)
      full130

end EvmAsm.Evm64
