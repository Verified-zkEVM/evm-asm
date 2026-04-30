/-
  EvmAsm.Evm64.DivMod.LoopBodyN2

  Fixed loop body compositions for n=2 (2-limb divisor).
  Eliminates the uAddr/window-cell and vtop/v1 overlaps in the generic spec.

  For n=2, three address overlaps exist:
  1. uAddr = uBase + signExtend12 4080  (both refer to u[j+2])
  2. uAddr + 8 = uBase + signExtend12 4088  (both refer to u[j+1])
  3. vtopBase + signExtend12 32 = sp + signExtend12 40  (both refer to v[1])

  This file eliminates these overlaps by:
  - Expanding the trial spec's let-bindings via dsimp
  - Rewriting uAddr and vtopBase to canonical uBase-relative form
  - Framing only with cells NOT already in the trial spec
  - Composing without cell duplication in any separating conjunction
-/

import EvmAsm.Evm64.DivMod.LoopBody.TrialCall
import EvmAsm.Evm64.DivMod.LoopBody.TrialMax
import EvmAsm.Evm64.DivMod.LoopBody.StoreLoop
import EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddbackBeq
import EvmAsm.Evm64.DivMod.LoopBody.MulsubCorrectionSkip

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Address rewriting lemmas for n=2 (no let-bindings, suitable for rw)
-- ============================================================================

/-- For n=2: uAddr = uBase + signExtend12 4080 -/
theorem u_addr_eq_n2 {sp j : Word} :
    sp + signExtend12 4056 - (j + (2 : Word)) <<< (3 : BitVec 6).toNat =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4080 := by
  divmod_addr

/-- For n=2: (uBase + signExtend12 4080) + 8 = uBase + signExtend12 4088 -/
theorem u_addr8_eq_n2 {sp j : Word} :
    ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4080) + 8 =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088 := by
  divmod_addr

/-- For n=2: vtopBase + signExtend12 32 = sp + signExtend12 40 -/
theorem vtop_eq_v1_n2 {sp : Word} :
    (sp + ((2 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat) + signExtend12 32 =
    sp + signExtend12 40 := by
  divmod_addr

-- ============================================================================
-- Section 12n2: Full loop body cpsBranchWithin for n=2, BLTU not-taken + BEQ skip
-- Non-vacuous: no overlapping cells in precondition.
-- ============================================================================

/-- Full loop body (BLTU ntaken + BEQ skip) for n=2.
    No overlapping cells: uHi=u2, uLo=u1, vTop=v1.
    Entry: base+448, cpsBranchWithin to base+448/904. -/
theorem divK_loop_body_n2_max_skip_spec_within
    (sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u2 v1) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let qHat : Word := signExtend12 4095  -- MAX64
    let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    -- Hypothesis: borrow = 0
    (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word) →
    cpsBranchWithin 76 (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld))
      (base + loopBodyOff) (loopBodyN2SkipPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop)
      (base + denormOff) (loopBodyN2SkipPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qHat qAddr hborrow
  -- Expand mulsub computation locally for intermediate steps
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
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
  let j' := j + signExtend12 4095
  -- Abbreviation for vtopBase (register value, not a memory address)
  let vtopBase := sp + ((2 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  -- 1. Trial max full (base+448 → base+516), instantiated with n=2, uHi=u2, uLo=u1, vTop=v1
  have TF := divK_trial_max_full_spec_within sp j (2 : Word) jOld v5Old v6Old v7Old v10Old v11Old
    u2 u1 v1 base hbltu
  -- Expand let-bindings in TF to expose raw address expressions
  dsimp only [] at TF
  -- Rewrite uAddr → uBase + signExtend12 4080, and (uAddr+8) → uBase + signExtend12 4088
  rw [u_addr_eq_n2] at TF
  rw [u_addr8_eq_n2] at TF
  -- Rewrite vtopBase + signExtend12 32 → sp + signExtend12 40
  rw [vtop_eq_v1_n2] at TF
  -- 2. Mulsub + correction skip (base+516 → base+880)
  have MCS := divK_mulsub_correction_skip_spec_within sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    j u1 vtopBase u2 v1 v2Old base

  intro_lets at MCS
  have MCS0 := MCS hborrow
  -- 3. Store loop cpsBranchWithin (base+880 → base+448/904)
  have SL := divK_store_loop_spec_within sp j qHat u4_new (0 : Word) qOld base
  intro_lets at SL
  -- 4. Frame TF with mulsub cells that DON'T overlap
  --    (uBase+4080 ↦ₘ u2, uBase+4088 ↦ₘ u1, sp+40 ↦ₘ v1 are already in TF)
  have TFf := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ v2Old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld))
    (by pcFree) TF
  -- 5. Compose TF + MCS0
  seqFrame TFf MCS0
  -- 6. Frame store_loop with remaining atoms
  have SLf := cpsBranchWithin_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3) **
     ((uBase + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (2 : Word)))
    (by pcFree) SL
  -- 7. Compose pre_store (cpsTripleWithin) with SLf (cpsBranchWithin), then permute to match target
  exact cpsBranchWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN2SkipPost loopBodySkipPost mulsubN4 loopExitPostN2 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    (fun h hp => by delta loopBodyN2SkipPost loopBodySkipPost mulsubN4 loopExitPostN2 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
      (cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
        (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0 SLf)

theorem divK_loop_body_n2_max_addback_spec_within
    (sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u2 v1) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let qHat : Word := signExtend12 4095  -- MAX64
    let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - ms.2.2.2.2) v0 v1 v2 v3
    -- Hypothesis: second addback carry nonzero (only needed if first carry = 0)
    (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3 = 0 →
      addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) →
    -- Hypothesis: borrow ≠ 0
    (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsBranchWithin 152 (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld))
      (base + loopBodyOff) (loopBodyN2AddbackBeqPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop)
      (base + denormOff) (loopBodyN2AddbackBeqPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qHat qAddr ms ab hcarry2_nz hborrow
  -- Local lets matching beq_spec structure
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
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
  let vtopBase := sp + ((2 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  -- 1. Trial max full (base+448 → base+516)
  have TF := divK_trial_max_full_spec_within sp j (2 : Word) jOld v5Old v6Old v7Old v10Old v11Old
    u2 u1 v1 base hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n2] at TF
  rw [u_addr8_eq_n2] at TF
  rw [vtop_eq_v1_n2] at TF
  -- 2. Mulsub + correction addback + BEQ (base+516 → base+884)
  have MCA := divK_mulsub_correction_addback_beq_spec_within sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    j u1 vtopBase u2 v1 v2Old base

  intro_lets at MCA
  have MCA0 := MCA hcarry2_nz hborrow
  -- 3. Store loop cpsBranchWithin (base+880 → base+448/904)
  have SL := divK_store_loop_spec_within sp j q_out u4_out carryOut qOld base
  intro_lets at SL
  -- 4. Frame TF with non-overlapping cells
  have TFf := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ v2Old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld))
    (by pcFree) TF
  -- 5. Compose TF + MCA0
  seqFrame TFf MCA0
  -- 6. Frame store_loop
  have SLf := cpsBranchWithin_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3Out) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0Out) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1Out) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2Out) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3Out) **
     ((uBase + signExtend12 4064) ↦ₘ u4_out) **
     (sp + signExtend12 3984 ↦ₘ (2 : Word)))
    (by pcFree) SL
  -- 7. Compose
  exact cpsBranchWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN2AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN2 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    (fun h hp => by delta loopBodyN2AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN2 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    (cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf)

theorem divK_loop_body_n2_call_skip_spec_within
    (sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u2 v1) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    -- div128 intermediates
    let dHi := v1 >>> (32 : BitVec 6).toNat
    let dLo := (v1 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u1 >>> (32 : BitVec 6).toNat
    let div_un0 := (u1 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u2 dHi
    let rhat := u2 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    let qHat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    -- Hypothesis: borrow = 0
    (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word) →
    cpsBranchWithin 126 (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (base + loopBodyOff)
      (loopBodyN2SkipPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v1) **
       (sp + signExtend12 3952 ↦ₘ dLo) **
       (sp + signExtend12 3944 ↦ₘ div_un0))
      (base + denormOff)
      (loopBodyN2SkipPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v1) **
       (sp + signExtend12 3952 ↦ₘ dLo) **
       (sp + signExtend12 3944 ↦ₘ div_un0)) := by
  intro uBase
        dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0' qHat
        qAddr hborrow
  let q0Dlo := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
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
  let j' := j + signExtend12 4095
  let vtopBase := sp + ((2 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  -- 1. Trial call full (base+448 → base+516)
  have TF := divK_trial_call_full_spec_within sp j (2 : Word) jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u2 u1 v1 retMem dMem dloMem scratch_un0 base
    halign hbltu
  unfold divKTrialCallFullPost at TF
  dsimp only [] at TF
  rw [u_addr_eq_n2] at TF
  rw [u_addr8_eq_n2] at TF
  rw [vtop_eq_v1_n2] at TF
  -- 2. Mulsub + correction skip (base+516 → base+880)
  have MCS := divK_mulsub_correction_skip_spec_within sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x1Exit q0' dHi x7Exit q1' (base + 516) base

  intro_lets at MCS
  have MCS0 := MCS hborrow
  -- 3. Store loop cpsBranchWithin (base+880 → base+448/904)
  have SL := divK_store_loop_spec_within sp j qHat u4_new (0 : Word) qOld base
  intro_lets at SL
  -- 4. Frame TF (trial_call includes scratch memory, so don't add those to frame)
  --    For n=2: uBase+4080 ↦ u2, uBase+4088 ↦ u1, sp+40 ↦ v1 are in the trial
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld))
    (by pcFree) TF
  -- 5. Compose TF + MCS0
  have MCS0u := MCS0
  seqFrame TFf MCS0u
  -- 6. Frame store_loop
  have SLf := cpsBranchWithin_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3) **
     ((uBase + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v1) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) SL
  -- 7. Compose
  exact cpsBranchWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN2SkipPost loopBodySkipPost mulsubN4 loopExitPostN2 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    (fun h hp => by delta loopBodyN2SkipPost loopBodySkipPost mulsubN4 loopExitPostN2 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    (cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0u SLf)

-- ============================================================================
-- Section 15n2: Full loop body cpsBranchWithin for n=2, BLTU taken + BEQ addback
-- ============================================================================

/-- Full loop body (BLTU taken + BEQ addback) for n=2.
    No overlapping cells: uHi=u2, uLo=u1, vTop=v1.
    Entry: base+448, cpsBranchWithin to base+448/904. -/
theorem divK_loop_body_n2_call_addback_spec_within
    (sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u2 v1) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    -- div128 intermediates
    let dHi := v1 >>> (32 : BitVec 6).toNat
    let dLo := (v1 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u1 >>> (32 : BitVec 6).toNat
    let div_un0 := (u1 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u2 dHi
    let rhat := u2 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    let qHat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - ms.2.2.2.2) v0 v1 v2 v3
    -- Hypothesis: second addback carry nonzero (only needed if first carry = 0)
    (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3 = 0 →
      addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) →
    -- Hypothesis: borrow ≠ 0
    (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsBranchWithin 202 (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (base + loopBodyOff)
      (loopBodyN2AddbackBeqPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v1) **
       (sp + signExtend12 3952 ↦ₘ dLo) **
       (sp + signExtend12 3944 ↦ₘ div_un0))
      (base + denormOff)
      (loopBodyN2AddbackBeqPost sp j qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v1) **
       (sp + signExtend12 3952 ↦ₘ dLo) **
       (sp + signExtend12 3944 ↦ₘ div_un0)) := by
  intro uBase
        dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0' qHat
        qAddr ms ab hcarry2_nz hborrow
  let q0Dlo := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  -- Local lets matching beq_spec structure
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
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
  let vtopBase := sp + ((2 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  -- 1. Trial call full (base+448 → base+516)
  have TF := divK_trial_call_full_spec_within sp j (2 : Word) jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u2 u1 v1 retMem dMem dloMem scratch_un0 base
    halign hbltu
  unfold divKTrialCallFullPost at TF
  dsimp only [] at TF
  rw [u_addr_eq_n2] at TF
  rw [u_addr8_eq_n2] at TF
  rw [vtop_eq_v1_n2] at TF
  -- 2. Mulsub + correction addback + BEQ (base+516 → base+884)
  have MCA := divK_mulsub_correction_addback_beq_spec_within sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x1Exit q0' dHi x7Exit q1' (base + 516) base

  intro_lets at MCA
  have MCA0 := MCA hcarry2_nz hborrow
  -- 3. Store loop cpsBranchWithin (base+880 → base+448/904)
  have SL := divK_store_loop_spec_within sp j q_out u4_out carryOut qOld base
  intro_lets at SL
  -- 4. Frame TF
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld))
    (by pcFree) TF
  -- 5. Compose TF + MCA0
  seqFrame TFf MCA0
  -- 6. Frame store_loop
  have SLf := cpsBranchWithin_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3Out) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0Out) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1Out) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2Out) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3Out) **
     ((uBase + signExtend12 4064) ↦ₘ u4_out) **
     (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v1) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) SL
  -- 7. Compose
  exact cpsBranchWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN2AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN2 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    (fun h hp => by delta loopBodyN2AddbackBeqPost loopBodyAddbackBeqPost loopExitPostN2 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    (cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf)

def loopBodyPostN2
    (sp j v0 v1 v2 v3 : Word)
    (x2v x10v x11v : Word)
    (un0v un1v un2v un3v u4v qv : Word)
    (retv dv dlov sunv : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let j' := j + signExtend12 4095
  let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
  (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ uBase) **
  (.x7 ↦ᵣ qAddr) ** (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) **
  (.x2 ↦ᵣ x2v) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0v) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1v) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2v) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3v) **
  ((uBase + signExtend12 4064) ↦ₘ u4v) **
  (qAddr ↦ₘ qv) **
  (sp + signExtend12 3968 ↦ₘ retv) **
  (sp + signExtend12 3960 ↦ₘ dv) **
  (sp + signExtend12 3952 ↦ₘ dlov) **
  (sp + signExtend12 3944 ↦ₘ sunv)


-- ============================================================================
-- Unified max-path loop body
-- ============================================================================

/-- Unified loop body (BLTU ntaken) for n=2, parameterized by borrow condition.
    `borrow_zero = true` → skip path; `borrow_zero = false` → addback+BEQ path.
    Entry: base+loopBodyOff, cpsBranchWithin to base+loopBodyOff/denormOff. -/
theorem divK_loop_body_n2_max_unified_spec_within
    (borrow_zero : Bool)
    (sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry : ¬borrow_zero →
      let ms := mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - ms.2.2.2.2) v0 v1 v2 v3
      addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3 = 0 →
      addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0)
    (hborrow : if borrow_zero
               then (if BitVec.ult uTop
                        (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                     then (1 : Word) else 0) = (0 : Word)
               else (if BitVec.ult uTop
                        (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                     then (1 : Word) else 0) ≠ (0 : Word)) :
    cpsBranchWithin 152 (base + loopBodyOff) (sharedDivModCode base)
      (loopBodyPre (2 : Word) sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (base + loopBodyOff)
      (loopBodyUnifiedPostN2 borrow_zero sp j (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop)
      (base + denormOff)
      (loopBodyUnifiedPostN2 borrow_zero sp j (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  cases borrow_zero
  · -- false (addback+BEQ path)
    rw [if_neg (by decide)] at hborrow
    simp only [loopBodyUnifiedPostN2, loopBodyUnifiedPost_false]
    exact cpsBranchWithin_weaken
      (fun _ hp => by delta loopBodyPre at hp; xperm_hyp hp)
      (fun _ hp => hp)
      (fun _ hp => hp)
      (divK_loop_body_n2_max_addback_spec_within
        sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu (hcarry (by decide)) hborrow)
  · -- true (skip path)
    rw [if_pos rfl] at hborrow
    simp only [loopBodyUnifiedPostN2, loopBodyUnifiedPost_true]
    exact cpsBranchWithin_weaken
      (fun _ hp => by delta loopBodyPre at hp; xperm_hyp hp)
      (fun _ hp => hp)
      (fun _ hp => hp)
      (cpsBranchWithin_mono_nSteps (by decide) <| divK_loop_body_n2_max_skip_spec_within
        sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu hborrow)

/-- Unified loop body (BLTU taken, call path) for n=2, parameterized by borrow condition.
    `borrow_zero = true` → skip path; `borrow_zero = false` → addback+BEQ path.
    Includes div128 scratch cells in postcondition. -/
theorem divK_loop_body_n2_call_unified_spec_within
    (borrow_zero : Bool)
    (sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u2 v1)
    (hcarry : ¬borrow_zero →
      let ms := mulsubN4 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - ms.2.2.2.2) v0 v1 v2 v3
      addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3 = 0 →
      addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0)
    (hborrow : if borrow_zero
               then (if BitVec.ult uTop
                        (mulsubN4_c3 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
                     then (1 : Word) else 0) = (0 : Word)
               else (if BitVec.ult uTop
                        (mulsubN4_c3 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
                     then (1 : Word) else 0) ≠ (0 : Word)) :
    cpsBranchWithin 202 (base + loopBodyOff) (sharedDivModCode base)
      (loopBodyPreWithScratch (2 : Word) sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratch_un0)
      (base + loopBodyOff)
      (loopBodyUnifiedPostN2 borrow_zero sp j (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v1) **
       (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
       (sp + signExtend12 3944 ↦ₘ div128Un0 u1))
      (base + denormOff)
      (loopBodyUnifiedPostN2 borrow_zero sp j (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v1) **
       (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
       (sp + signExtend12 3944 ↦ₘ div128Un0 u1)) := by
  cases borrow_zero
  · -- false (addback+BEQ path)
    rw [if_neg (by decide)] at hborrow
    simp only [loopBodyUnifiedPostN2, loopBodyUnifiedPost_false]
    exact cpsBranchWithin_weaken
      (fun _ hp => by delta loopBodyPreWithScratch loopBodyPre at hp; xperm_hyp hp)
      (fun _ hp => hp)
      (fun _ hp => hp)
      (divK_loop_body_n2_call_addback_spec_within
        sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0
        base halign hbltu (hcarry (by decide)) hborrow)
  · -- true (skip path)
    rw [if_pos rfl] at hborrow
    simp only [loopBodyUnifiedPostN2, loopBodyUnifiedPost_true]
    exact cpsBranchWithin_weaken
      (fun _ hp => by delta loopBodyPreWithScratch loopBodyPre at hp; xperm_hyp hp)
      (fun _ hp => hp)
      (fun _ hp => hp)
      (cpsBranchWithin_mono_nSteps (by decide) <| divK_loop_body_n2_call_skip_spec_within
        sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0
        base halign hbltu hborrow)

end EvmAsm.Evm64
