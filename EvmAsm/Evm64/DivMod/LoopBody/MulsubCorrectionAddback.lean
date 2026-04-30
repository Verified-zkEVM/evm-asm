/-
  EvmAsm.Evm64.DivMod.LoopBody.MulsubCorrectionAddback

  Extracted from `LoopBody.lean` (Section 10b).

  Mulsub + correction_addback composition (borrow ≠ 0 path):
  combines `divK_mulsub_full_spec_within` with `divK_correction_addback_spec_within`,
  with optional BEQ passthrough for the single-addback case.

  Three theorems (all public):
  - `divK_mulsub_correction_addback_880_spec` — base+516 → base+880
  - `divK_mulsub_correction_addback_named_880_spec` — same with named pre/post
  - `divK_mulsub_correction_addback_spec` — base+516 → base+884 (with BEQ)

  Uses public helpers from `LoopBody.lean`:
  - `divK_mulsub_full_spec_within`
  - `divK_correction_addback_spec_within`
-/

import EvmAsm.Evm64.DivMod.LoopBody

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Section 10b: Mulsub + correction_addback composition (borrow ≠ 0 path)
-- ============================================================================

theorem lb_beq_back_ntaken_local {base : Word} : (base + 880 : Word) + 4 = base + 884 := by
  bv_addr

/-- BEQ passthrough at [108]: when carry (x7) != 0, BEQ falls through from
    base+880 to base+884. -/
theorem divK_beq_passthrough_spec_within {carry : Word} (base : Word) (hne : carry ≠ 0) :
    cpsTripleWithin 1 (base + 880) (base + 884) (sharedDivModCode base)
      ((.x7 ↦ᵣ carry) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ carry) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x7 .x0 (8044 : BitVec 13) carry 0 (base + 880)
  rw [lb_beq_back_ntaken_local] at hbeq
  have hbeq_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub 108 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  have ntaken := cpsBranchWithin_ntakenPath hbeq_ext (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
    exact hne hpure)
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    ntaken

/-- v2 mirror of `divK_beq_passthrough_spec_within`. -/
theorem divK_beq_passthrough_v2_spec_within {carry : Word} (base : Word) (hne : carry ≠ 0) :
    cpsTripleWithin 1 (base + 880) (base + 884) (sharedDivModCode_v2 base)
      ((.x7 ↦ᵣ carry) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ carry) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x7 .x0 (8044 : BitVec 13) carry 0 (base + 880)
  rw [lb_beq_back_ntaken_local] at hbeq
  have hbeq_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub_v2 108 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  have ntaken := cpsBranchWithin_ntakenPath hbeq_ext (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
    exact hne hpure)
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    ntaken

theorem divK_mulsub_correction_addback_880_spec_within
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (v1Old v5Old v6Old v7Old v10Old v2Old : Word)
    (base : Word) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    -- Mulsub intermediates (same as in addback spec)
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
    -- Addback intermediates
    let upc0 := un0 + (signExtend12 0 : Word)
    let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
    let aun0 := upc0 + v0
    let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
    let aco0 := ac1_0 ||| ac2_0
    let upc1 := un1 + aco0
    let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
    let aun1 := upc1 + v1
    let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
    let aco1 := ac1_1 ||| ac2_1
    let upc2 := un2 + aco1
    let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
    let aun2 := upc2 + v2
    let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
    let aco2 := ac1_2 ||| ac2_2
    let upc3 := un3 + aco2
    let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
    let aun3 := upc3 + v3
    let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
    let aco3 := ac1_3 ||| ac2_3
    let aun4 := u4_new + aco3
    let qHat' := qHat + signExtend12 4095
    -- Hypothesis: borrow ≠ 0
    (if BitVec.ult uTop c3 then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 91 (base + 516) (base + 880) (sharedDivModCode base)
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
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat') **
       (.x1 ↦ᵣ j) ** (.x5 ↦ᵣ aun4) ** (.x6 ↦ᵣ uBase) **
       (.x7 ↦ᵣ aco3) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ aun3) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ aun0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ aun1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ aun2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ aun3) **
       ((uBase + signExtend12 4064) ↦ₘ aun4)) := by
  intro uBase
        p0_lo p0_hi fs0 ba0 pc0 bs0 un0 c0
        p1_lo p1_hi fs1 ba1 pc1 bs1 un1 c1
        p2_lo p2_hi fs2 ba2 pc2 bs2 un2 c2
        p3_lo p3_hi fs3 ba3 pc3 bs3 un3 c3 u4_new
        upc0 ac1_0 aun0 ac2_0 aco0 upc1 ac1_1 aun1 ac2_1 aco1
        upc2 ac1_2 aun2 ac2_2 aco2 upc3 ac1_3 aun3 ac2_3 aco3 aun4 qHat'
        hborrow
  -- 1. Mulsub full (base+516 → base+728)
  have MS := divK_mulsub_full_spec_within sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    v1Old v5Old v6Old v7Old v10Old v2Old base

  dsimp only [] at MS hborrow
  -- 2. Correction addback (base+728 → base+880) with borrow ≠ 0
  have CA := divK_correction_addback_spec_within sp uBase
    (if BitVec.ult uTop c3 then (1 : Word) else 0)
    qHat v0 v1 v2 v3 un0 un1 un2 un3 u4_new
    u4_new un3 base hborrow

  -- 3. Compose mulsub + correction_addback
  seqFrame MS CA
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    MSCA

def divK_mulsub_correction_addback_880_spec
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (v1Old v5Old v6Old v7Old v10Old v2Old : Word)
    (base : Word) :=
  divK_mulsub_correction_addback_880_spec_within sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    v1Old v5Old v6Old v7Old v10Old v2Old base

/-- Mulsub + correction addback (→880), named postcondition variant.
    Uses addbackN4/addbackN4_carry in postcondition for rewritability. -/
theorem divK_mulsub_correction_addback_named_880_spec_within
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (v1Old v5Old v6Old v7Old v10Old v2Old : Word)
    (base : Word) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
    let c3 := ms.2.2.2.2
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
    let qHat' := qHat + signExtend12 4095
    -- Hypothesis: borrow ≠ 0
    (if BitVec.ult uTop c3 then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 91 (base + 516) (base + 880) (sharedDivModCode base)
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
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat') **
       (.x1 ↦ᵣ j) ** (.x5 ↦ᵣ ab.2.2.2.2) ** (.x6 ↦ᵣ uBase) **
       (.x7 ↦ᵣ addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ ab.2.2.2.1) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ ab.1) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ ab.2.1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ ab.2.2.1) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ ab.2.2.2.1) **
       ((uBase + signExtend12 4064) ↦ₘ ab.2.2.2.2)) := by
  intro uBase ms c3 ab qHat' hborrow
  exact (divK_mulsub_correction_addback_880_spec_within sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    v1Old v5Old v6Old v7Old v10Old v2Old base) hborrow

def divK_mulsub_correction_addback_named_880_spec
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (v1Old v5Old v6Old v7Old v10Old v2Old : Word)
    (base : Word) :=
  divK_mulsub_correction_addback_named_880_spec_within sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    v1Old v5Old v6Old v7Old v10Old v2Old base

/-- Mulsub + correction addback + BEQ passthrough: when mulsub produces borrow≠0,
    run addback, then BEQ falls through (carry ≠ 0).
    Entry: base+516, Exit: base+884, CodeReq: sharedDivModCode base. -/
theorem divK_mulsub_correction_addback_spec_within
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
    -- Addback intermediates
    let upc0 := un0 + (signExtend12 0 : Word)
    let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
    let aun0 := upc0 + v0
    let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
    let aco0 := ac1_0 ||| ac2_0
    let upc1 := un1 + aco0
    let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
    let aun1 := upc1 + v1
    let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
    let aco1 := ac1_1 ||| ac2_1
    let upc2 := un2 + aco1
    let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
    let aun2 := upc2 + v2
    let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
    let aco2 := ac1_2 ||| ac2_2
    let upc3 := un3 + aco2
    let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
    let aun3 := upc3 + v3
    let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
    let aco3 := ac1_3 ||| ac2_3
    let aun4 := u4_new + aco3
    let qHat' := qHat + signExtend12 4095
    -- Hypothesis: borrow ≠ 0
    (if BitVec.ult uTop c3 then (1 : Word) else 0) ≠ (0 : Word) →
    -- Hypothesis: addback carry ≠ 0 (single addback sufficient)
    aco3 ≠ 0 →
    cpsTripleWithin 92 (base + 516) (base + 884) (sharedDivModCode base)
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
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat') **
       (.x1 ↦ᵣ j) ** (.x5 ↦ᵣ aun4) ** (.x6 ↦ᵣ uBase) **
       (.x7 ↦ᵣ aco3) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ aun3) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ aun0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ aun1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ aun2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ aun3) **
       ((uBase + signExtend12 4064) ↦ₘ aun4)) := by
  intro uBase
        p0_lo p0_hi fs0 ba0 pc0 bs0 un0 c0
        p1_lo p1_hi fs1 ba1 pc1 bs1 un1 c1
        p2_lo p2_hi fs2 ba2 pc2 bs2 un2 c2
        p3_lo p3_hi fs3 ba3 pc3 bs3 un3 c3 u4_new
        upc0 ac1_0 aun0 ac2_0 aco0 upc1 ac1_1 aun1 ac2_1 aco1
        upc2 ac1_2 aun2 ac2_2 aco2 upc3 ac1_3 aun3 ac2_3 aco3 aun4 qHat'
        hborrow hcarry
  -- 1. Mulsub + correction addback (base+516 → base+880) with borrow ≠ 0.
  have MSCA := (divK_mulsub_correction_addback_880_spec_within
    sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    v1Old v5Old v6Old v7Old v10Old v2Old base) hborrow
  -- 3. BEQ passthrough (base+880 → base+884) with carry ≠ 0
  have BEQ := divK_beq_passthrough_spec_within base hcarry
  -- 2. Frame BEQ with remaining atoms and compose (880→884)
  have BEQf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat') **
     (.x1 ↦ᵣ j) ** (.x5 ↦ᵣ aun4) ** (.x6 ↦ᵣ uBase) **
     (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ aun3) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ aun0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ aun1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ aun2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ aun3) **
     ((uBase + signExtend12 4064) ↦ₘ aun4))
    (by pcFree) BEQ
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) MSCA BEQf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    full

def divK_mulsub_correction_addback_spec
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (v1Old v5Old v6Old v7Old v10Old v2Old : Word)
    (base : Word) :=
  divK_mulsub_correction_addback_spec_within sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    v1Old v5Old v6Old v7Old v10Old v2Old base

end EvmAsm.Evm64
