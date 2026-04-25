/-
  EvmAsm.Evm64.DivMod.LoopBody.MulsubCorrectionSkip

  Extracted from `LoopBody.lean` (Section 10).

  Mulsub + correction_skip composition (borrow = 0 path):
  when mulsub produces borrow=0, skip addback. Takes borrow as an explicit
  parameter (not let-bound) to enable rw.

  Uses public helpers from `LoopBody.lean`:
  - `divK_mulsub_full_spec`
  - `divK_correction_skip_spec`
-/

import EvmAsm.Evm64.DivMod.LoopBody.CorrectionSkip

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Mulsub + correction skip: when mulsub produces borrow=0, skip addback.
    Takes borrow as explicit parameter to avoid let-binding expansion issues.
    Entry: base+516, Exit: base+880, CodeReq: sharedDivModCode base. -/
theorem divK_mulsub_correction_skip_spec
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (v1Old v5Old v6Old v7Old v10Old v2Old : Word)
    (base : Word) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    -- Mulsub intermediates
    let p0_lo := qHat * v0; let p0_hi := rv64_mulhu qHat v0
    let fs0 := p0_lo + (signExtend12 0 : Word)
    let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
    let pc0 := ba0 + p0_hi
    let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
    let un0 := u0 - fs0; let c0 := pc0 + bs0
    let p1_lo := qHat * v1; let p1_hi := rv64_mulhu qHat v1
    let fs1 := p1_lo + c0
    let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
    let pc1 := ba1 + p1_hi
    let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
    let un1 := u1 - fs1; let c1 := pc1 + bs1
    let p2_lo := qHat * v2; let p2_hi := rv64_mulhu qHat v2
    let fs2 := p2_lo + c1
    let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
    let pc2 := ba2 + p2_hi
    let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
    let un2 := u2 - fs2; let c2 := pc2 + bs2
    let p3_lo := qHat * v3; let p3_hi := rv64_mulhu qHat v3
    let fs3 := p3_lo + c2
    let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
    let pc3 := ba3 + p3_hi
    let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
    let un3 := u3 - fs3; let c3 := pc3 + bs3
    let u4_new := uTop - c3
    -- Hypothesis: mulsub borrow = 0
    (if BitVec.ult uTop c3 then (1 : Word) else 0) = (0 : Word) →
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
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x1 ↦ᵣ j) ** (.x5 ↦ᵣ u4_new) ** (.x6 ↦ᵣ uBase) **
       (.x7 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3) **
       ((uBase + signExtend12 4064) ↦ₘ u4_new)) := by
  intro uBase
        p0_lo p0_hi fs0 ba0 pc0 bs0 un0 c0
        p1_lo p1_hi fs1 ba1 pc1 bs1 un1 c1
        p2_lo p2_hi fs2 ba2 pc2 bs2 un2 c2
        p3_lo p3_hi fs3 ba3 pc3 bs3 un3 c3 u4_new
        hborrow
  -- 1. Mulsub full (base+516 → base+728)
  have MS := divK_mulsub_full_spec sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    v1Old v5Old v6Old v7Old v10Old v2Old base

  dsimp only [] at MS hborrow
  -- 2. Rewrite borrow to 0 in mulsub postcondition
  rw [hborrow] at MS
  -- 3. Correction skip (base+728 → base+884)
  have CS := divK_correction_skip_spec sp uBase qHat v0 v1 v2 v3 un0 un1 un2 un3 u4_new
    u4_new un3 base
  -- 4. Compose mulsub(borrow=0) + correction_skip
  seqFrame MS CS
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    MSCS

end EvmAsm.Evm64
