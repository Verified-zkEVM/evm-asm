/-
  EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddbackBeq

  Extracted from `LoopBody.lean` (Section 10c).

  Combined `mulsub + correction_addback + BEQ` spec for both addback-carry
  outcomes (single-addback fall-through and double-addback back-branch).

  Uses public helpers from `LoopBody.lean`:
  - `divK_mulsub_correction_addback_spec`
  - `divK_mulsub_correction_addback_named_880_spec`
  - `divK_double_addback_beq_named_spec`
-/

import EvmAsm.Evm64.DivMod.LoopBody
import EvmAsm.Evm64.DivMod.LoopBody.MulsubCorrectionAddback

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
theorem divK_mulsub_correction_addback_beq_spec
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
    cpsTriple (base + 516) (base + 884) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x1 ↦ᵣ v1Old) ** (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x2 ↦ᵣ v2Old) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_out) **
       (.x1 ↦ᵣ j) ** (.x5 ↦ᵣ u4_out) ** (.x6 ↦ᵣ uBase) **
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
  have MCA := divK_mulsub_correction_addback_spec sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
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
    have MCA_N := (divK_mulsub_correction_addback_named_880_spec sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
      v1Old v5Old v6Old v7Old v10Old v2Old base) hborrow
    -- Rewrite carry to 0
    rw [show addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3 = (0 : Word) from hcarry] at MCA_N
    -- Use named DA spec (880→884 with addbackN4 projections in postcondition)
    have hcarry2 : addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0 :=
      hcarry2_nz hcarry
    have DA := divK_double_addback_beq_named_spec sp uBase
      (qHat + signExtend12 4095) v0 v1 v2 v3
      ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2
      base hcarry2
    -- Frame DA with extra atoms from MCA_N postcondition
    have DAf := cpsTriple_frameR
      ((.x1 ↦ᵣ j) ** (.x10 ↦ᵣ c3) **
       (sp + signExtend12 3976 ↦ₘ j))
      (by pcFree) DA
    -- Compose MCA_N(→880) with DAf(880→884)
    have full := cpsTriple_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) MCA_N DAf
    exact cpsTriple_weaken
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
    exact MCA0 hcarry

end EvmAsm.Evm64
