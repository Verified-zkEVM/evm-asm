/-
  EvmAsm.Evm64.DivMod.Compose.PreloopV5Mod

  v5 preloop bricks re-pointed at `modCode_noNop_v5` (the MOD code surface).

  The preloop blocks (phase-A, CLZ, phase-C2, normB, normA, copyAU, loopSetup)
  live in the shared blocks 0–9 of the v5 code surface and never touch the
  epilogue (block 10), so each one's body extends to the MOD surface via the
  `sharedNoNop_v5_b*_mod` block subsumptions — exactly as the DIV bricks
  (`PhaseAV5.lean`, …) extend via `sharedNoNop_v5_b*_div`.

  WHY this is needed (bead `evm-asm-wbc4i.10.3.2.4.5`): a `cpsTripleWithin` over
  `divCode_noNop_v5` requires `divCode_noNop_v5.SatisfiedBy s`, i.e. the state's
  code must contain the DIV epilogue — so a DIV-surface preloop/loop spec is
  unusable for a MOD path (a MOD state lacks the DIV epilogue and there is no
  `divCode ⊆ modCode`).  Re-pointing the preloop+loop onto `modCode_noNop_v5`
  (or a shared surface) is the only sound fix; these MOD bricks are the first
  pieces.  This file accumulates them brick by brick.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.PhaseABV4NoNop
public import EvmAsm.Evm64.DivMod.Compose.CLZ
public import EvmAsm.Evm64.DivMod.Compose.Norm
public import EvmAsm.Evm64.DivMod.Compose.NormA
public import EvmAsm.Evm64.DivMod.LimbSpec.CopyAU
public import EvmAsm.Evm64.DivMod.Compose.V5NoNop

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (se12_0 se12_8 se12_16 se12_24 se12_32 se12_40 se12_48 se12_56)

private theorem divK_phaseA_code_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (divK_phaseA_code base) a = some i → (modCode_noNop_v5 base) a = some i := by
  unfold divK_phaseA_code
  intro a i h
  exact sharedNoNop_v5_b0_mod a i h

private theorem beq_singleton_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + phaseABeqOff) (.BEQ .x5 .x0 1020)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact sharedNoNop_v5_b0_mod a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup base (divK_phaseA 1020) 7
      (by decide) (by decide)) a i h)

/-- v5 phase-A (b ≠ 0) over `modCode_noNop_v5`: OR-reduce b limbs, BEQ not taken →
    phase-B.  MOD mirror of `evm_div_phaseA_ntaken_spec_within_v5_noNop`
    (`PhaseAV5.lean`); phase-A doesn't touch the epilogue, so the body is
    identical apart from the `_mod` block subsumption. -/
theorem evm_mod_phaseA_ntaken_spec_within_v5_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0) :
    cpsTripleWithin 8 base (base + phaseBOff) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)) := by
  have hbody := cpsTripleWithin_extend_code divK_phaseA_code_sub_modCode_noNop_v5
    (divK_phaseA_body_spec_within sp base b0 b1 b2 b3 v5 v10)
  have hbeq_raw := beq_spec_gen_within .x5 .x0 1020 (b0 ||| b1 ||| b2 ||| b3) (0 : Word) (base + phaseABeqOff)
  rw [show (base + phaseABeqOff : Word) + signExtend13 1020 = base + zeroPathOff from by rv64_addr,
      show (base + phaseABeqOff : Word) + 4 = base + phaseBOff from by bv_addr] at hbeq_raw
  have hbeq_clean := cpsBranchWithin_ntakenStripPure2 hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _).mp h_rest).2 hbnz)
  have hbeq := cpsTripleWithin_extend_code beq_singleton_sub_modCode_noNop_v5 hbeq_clean
  have hbeq_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq
  have hAB := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hAB

-- ============================================================================
-- Brick 2: count-leading-zeros (clzOff → phaseC2Off) over modCode_noNop_v5.
-- MOD mirror of `divK_clz_spec_within_v5_noNop` (CLZV5.lean), `_div` → `_mod`.
-- ============================================================================

/-- CLZ block instructions are subsumed by `modCode_noNop_v5`. -/
private theorem divK_clz_code_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + clzOff) divK_clz) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact sharedNoNop_v5_b2_mod a i h

private theorem clz_stage_sub_modCode_noNop_v5 {base : Word}
    (K M_s : BitVec 6) (M_a : BitVec 12) (k : Nat)
    (hk : k + (divK_clz_stage_prog K M_s M_a).length ≤ divK_clz.length)
    (hslice : (divK_clz.drop k).take (divK_clz_stage_prog K M_s M_a).length =
      divK_clz_stage_prog K M_s M_a)
    (hbound : 4 * divK_clz.length < 2 ^ 64) :
    ∀ a i, (divK_clz_stage_code K M_s M_a ((base + clzOff) + BitVec.ofNat 64 (4 * k))) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_modCode_noNop_v5 a i
    (CodeReq.ofProg_mono_sub (base + clzOff) _ divK_clz _ k
      rfl hslice hk hbound a i h)

private theorem clz_last_sub_modCode_noNop_v5 {base : Word} (k : Nat)
    (hk : k + divK_clz_last_prog.length ≤ divK_clz.length)
    (hslice : (divK_clz.drop k).take divK_clz_last_prog.length = divK_clz_last_prog)
    (hbound : 4 * divK_clz.length < 2 ^ 64) :
    ∀ a i, (divK_clz_last_code ((base + clzOff) + BitVec.ofNat 64 (4 * k))) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_modCode_noNop_v5 a i
    (CodeReq.ofProg_mono_sub (base + clzOff) _ divK_clz _ k
      rfl hslice hk hbound a i h)

private theorem clz_init_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + clzOff) (.ADDI .x6 .x0 0)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_modCode_noNop_v5 a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup (base + clzOff) divK_clz 0
      (by decide) (by decide)) a i (by rwa [show (base + clzOff : Word) =
        base + clzOff + BitVec.ofNat 64 (4 * 0) from by bv_addr] at h))

/-- v5 count-leading-zeros full brick over `modCode_noNop_v5`.  MOD mirror of
    `divK_clz_spec_within_v5_noNop`. -/
theorem divK_clz_spec_within_v5_noNop_modCode (val v6Old v7Old : Word) (base : Word) :
    cpsTripleWithin 24 (base + clzOff) (base + phaseC2Off) (modCode_noNop_v5 base)
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ v6Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (clzResult val).2) ** (.x6 ↦ᵣ (clzResult val).1) **
       (.x7 ↦ᵣ (clzResult val).2 >>> (63 : Nat)) ** (.x0 ↦ᵣ (0 : Word))) := by
  unfold clzResult
  have I := divK_clz_init_spec_within v6Old (base + clzOff)
  have Ie := cpsTripleWithin_extend_code (hmono := clz_init_sub_modCode_noNop_v5) I
  have Ief := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ val) ** (.x7 ↦ᵣ v7Old)) (by pcFree) Ie
  have S0 := divK_clz_stage_combined_within 32 32 32 val (signExtend12 0) v7Old
    ((base + clzOff) + BitVec.ofNat 64 (4 * 1))
  dsimp only [] at S0
  have S0e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_modCode_noNop_v5 32 32 32 1
    (by decide) (by decide) (by decide)) S0
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 1) = base + clzOff + 4 from by bv_addr] at S0e
  rw [clz_addr1] at S0e
  seqFrame Ief S0e
  let v0 := if val >>> (32 : BitVec 6).toNat ≠ 0 then val else val <<< (32 : BitVec 6).toNat
  let c0 := if val >>> (32 : BitVec 6).toNat ≠ 0 then signExtend12 (0 : BitVec 12)
    else signExtend12 (0 : BitVec 12) + signExtend12 (32 : BitVec 12)
  have S1 := divK_clz_stage_combined_within 48 16 16 v0 c0 (val >>> (32 : BitVec 6).toNat)
    ((base + clzOff) + BitVec.ofNat 64 (4 * 5))
  dsimp only [] at S1
  have S1e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_modCode_noNop_v5 48 16 16 5
    (by decide) (by decide) (by decide)) S1
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 5) = base + clzOff + 20 from by bv_addr] at S1e
  rw [clz_addr2] at S1e
  seqFrame IefS0e S1e
  let v1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then v0 else v0 <<< (16 : BitVec 6).toNat
  let c1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then c0 else c0 + signExtend12 (16 : BitVec 12)
  have S2 := divK_clz_stage_combined_within 56 8 8 v1 c1 (v0 >>> (48 : BitVec 6).toNat)
    ((base + clzOff) + BitVec.ofNat 64 (4 * 9))
  dsimp only [] at S2
  have S2e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_modCode_noNop_v5 56 8 8 9
    (by decide) (by decide) (by decide)) S2
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 9) = base + clzOff + 36 from by bv_addr] at S2e
  rw [clz_addr3] at S2e
  seqFrame IefS0eS1e S2e
  let v2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then v1 else v1 <<< (8 : BitVec 6).toNat
  let c2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then c1 else c1 + signExtend12 (8 : BitVec 12)
  have S3 := divK_clz_stage_combined_within 60 4 4 v2 c2 (v1 >>> (56 : BitVec 6).toNat)
    ((base + clzOff) + BitVec.ofNat 64 (4 * 13))
  dsimp only [] at S3
  have S3e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_modCode_noNop_v5 60 4 4 13
    (by decide) (by decide) (by decide)) S3
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 13) = base + clzOff + 52 from by bv_addr] at S3e
  rw [clz_addr4] at S3e
  seqFrame IefS0eS1eS2e S3e
  let v3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then v2 else v2 <<< (4 : BitVec 6).toNat
  let c3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then c2 else c2 + signExtend12 (4 : BitVec 12)
  have S4 := divK_clz_stage_combined_within 62 2 2 v3 c3 (v2 >>> (60 : BitVec 6).toNat)
    ((base + clzOff) + BitVec.ofNat 64 (4 * 17))
  dsimp only [] at S4
  have S4e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_modCode_noNop_v5 62 2 2 17
    (by decide) (by decide) (by decide)) S4
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 17) = base + clzOff + 68 from by bv_addr] at S4e
  rw [clz_addr5] at S4e
  seqFrame IefS0eS1eS2eS3e S4e
  let v4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then v3 else v3 <<< (2 : BitVec 6).toNat
  let c4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then c3 else c3 + signExtend12 (2 : BitVec 12)
  have S5 := divK_clz_last_combined_within v4 c4 (v3 >>> (62 : BitVec 6).toNat)
    ((base + clzOff) + BitVec.ofNat 64 (4 * 21))
  dsimp only [] at S5
  have S5e := cpsTripleWithin_extend_code (hmono := clz_last_sub_modCode_noNop_v5 21
    (by decide) (by decide) (by decide)) S5
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 21) = base + clzOff + 84 from by bv_addr] at S5e
  rw [clz_addr6] at S5e
  seqFrame IefS0eS1eS2eS3eS4e S5e
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    IefS0eS1eS2eS3eS4eS5e

-- ============================================================================
-- Brick 3: phase-C2 (phaseC2Off → normBOff / copyAUOff) over modCode_noNop_v5.
-- MOD mirror of `divK_phaseC2_{ntaken,taken}_spec_within_v5_noNop` (PhaseC2V5.lean).
-- ============================================================================

/-- Phase-C2 block instructions are subsumed by `modCode_noNop_v5`. -/
private theorem divK_phaseC2_code_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (divK_phaseC2_code 172 (base + phaseC2Off)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  unfold divK_phaseC2_code
  intro a i h
  exact sharedNoNop_v5_b3_mod a i h

/-- BEQ x6 x0 172 singleton subsumed by `modCode_noNop_v5`. -/
private theorem beq_shift_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + phaseC2Off + 12) (.BEQ .x6 .x0 172)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseC2Off) (divK_phaseC2 172) 3
    (by decide) (by decide)
  rw [show (BitVec.ofNat 64 (4 * 3) : Word) = (12 : Word) from by decide] at hlookup
  exact divK_phaseC2_code_sub_modCode_noNop_v5 a i
    (CodeReq.singleton_mono hlookup a i h)

private theorem divK_phaseC2_body_modCode_noNop_v5_within
    (sp shift v2 shiftMem : Word) (base : Word) :
    cpsTripleWithin 3 (base + phaseC2Off) (base + phaseC2Off + 12) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hbody := divK_phaseC2_body_spec_within sp shift v2 shiftMem 172 (base + phaseC2Off)
  exact cpsTripleWithin_extend_code divK_phaseC2_code_sub_modCode_noNop_v5 hbody

/-- v5 phase-C2 (shift ≠ 0) over `modCode_noNop_v5`: BEQ not taken → normB. -/
theorem divK_phaseC2_ntaken_spec_within_v5_noNop_modCode (sp shift v2 shiftMem : Word) (base : Word)
    (hshift_nz : shift ≠ 0) :
    cpsTripleWithin 4 (base + phaseC2Off) (base + normBOff) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hbody := divK_phaseC2_body_modCode_noNop_v5_within sp shift v2 shiftMem base
  have hbeq_raw := beq_spec_gen_within .x6 .x0 172 shift (0 : Word) (base + phaseC2Off + 12)
  rw [show (base + phaseC2Off + 12 : Word) + signExtend13 172 = base + copyAUOff from by rv64_addr,
      show (base + phaseC2Off + 12 : Word) + 4 = base + normBOff from by bv_addr] at hbeq_raw
  have hbeq_clean := cpsBranchWithin_ntakenStripPure2 hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _).mp h_rest).2 (show shift ≠ (0 : Word) from hshift_nz))
  have hbeq := cpsTripleWithin_extend_code beq_shift_sub_modCode_noNop_v5 hbeq_clean
  have hbeqf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq
  have hC2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbeqf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hC2

/-- v5 phase-C2 (shift = 0) over `modCode_noNop_v5`: BEQ taken → copyAU. -/
theorem divK_phaseC2_taken_spec_within_v5_noNop_modCode (sp shift v2 shiftMem : Word) (base : Word)
    (hshift_z : shift = 0) :
    cpsTripleWithin 4 (base + phaseC2Off) (base + copyAUOff) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hbody := divK_phaseC2_body_modCode_noNop_v5_within sp shift v2 shiftMem base
  have hbeq_raw := beq_spec_gen_within .x6 .x0 172 shift (0 : Word) (base + phaseC2Off + 12)
  rw [show (base + phaseC2Off + 12 : Word) + signExtend13 172 = base + copyAUOff from by rv64_addr,
      show (base + phaseC2Off + 12 : Word) + 4 = base + normBOff from by bv_addr] at hbeq_raw
  have hbeq_clean := cpsBranchWithin_takenStripPure2 hbeq_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd hshift_z ((sepConj_pure_right _).mp h_rest).2)
  have hbeq := cpsTripleWithin_extend_code beq_shift_sub_modCode_noNop_v5 hbeq_clean
  have hbeqf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq
  have hC2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbeqf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hC2

-- ============================================================================
-- Brick 4: normalize-B (normBOff → normAOff) over modCode_noNop_v5.
-- MOD mirror of `divK_normB_full_spec_within_v5_noNop` (NormBV5.lean), `_b4_mod`.
-- ============================================================================

/-- The normB block instructions are subsumed by `modCode_noNop_v5`. -/
private theorem divK_normB_code_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + normBOff) divK_normB) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact sharedNoNop_v5_b4_mod a i h

private theorem divK_normB_half1_within_v5_noNop_modCode
    (sp b0 b1 b2 b3 v5 v7 shift antiShift : Word) (base : Word) :
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
    cpsTripleWithin 12 (base + normBOff) (base + normBOff + 48) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b2') ** (.x7 ↦ᵣ (b1 >>> (antiShift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3')) := by
  intro b3' b2'
  have hm1 := divK_normB_merge_spec_within 56 48 sp b3 b2 v5 v7 shift antiShift (base + normBOff)
  simp only [se12_56, se12_48] at hm1
  have hm1e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normB_code_sub_modCode_noNop_v5 a i
      (CodeReq.ofProg_mono_sub (base + normBOff) (base + normBOff) divK_normB
        (divK_normB_merge_prog 56 48) 0
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hm1
  have hm1ef := cpsTripleWithin_frameR
    (((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1))
    (by pcFree) hm1e
  have hm2 := divK_normB_merge_spec_within 48 40 sp b2 b1 b3' (b2 >>> (antiShift.toNat % 64))
    shift antiShift (base + normBOff + 24)
  simp only [se12_48, se12_40] at hm2
  rw [show (base + normBOff + 24 : Word) + 24 = base + normBOff + 48 from by bv_addr] at hm2
  have hm2e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normB_code_sub_modCode_noNop_v5 a i
      (CodeReq.ofProg_mono_sub (base + normBOff) (base + normBOff + 24) divK_normB
        (divK_normB_merge_prog 48 40) 6
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hm2
  have hm2ef := cpsTripleWithin_frameR
    (((sp + 32) ↦ₘ b0) ** ((sp + 56) ↦ₘ b3'))
    (by pcFree) hm2e
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hm1ef hm2ef
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12

private theorem divK_normB_half2_within_v5_noNop_modCode
    (sp b0 b1 b2' b3' shift antiShift : Word) (base : Word) :
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    cpsTripleWithin 9 (base + normBOff + 48) (base + normAOff) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b2') ** (.x7 ↦ᵣ (b1 >>> (antiShift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3'))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0') ** (.x7 ↦ᵣ (b0 >>> (antiShift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
       ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3')) := by
  intro b1' b0'
  have hm3 := divK_normB_merge_spec_within 40 32 sp b1 b0
    b2' (b1 >>> (antiShift.toNat % 64)) shift antiShift (base + normBOff + 48)
  simp only [se12_40, se12_32] at hm3
  rw [show (base + normBOff + 48 : Word) + 24 = base + normBOff + 72 from by bv_addr] at hm3
  have hm3e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normB_code_sub_modCode_noNop_v5 a i
      (CodeReq.ofProg_mono_sub (base + normBOff) (base + normBOff + 48) divK_normB
        (divK_normB_merge_prog 40 32) 12
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hm3
  have hm3ef := cpsTripleWithin_frameR
    (((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3'))
    (by pcFree) hm3e
  have hl := divK_normB_last_spec_within 32 sp b0 b1' shift (base + normBOff + 72)
  simp only [se12_32] at hl
  rw [show (base + normBOff + 72 : Word) + 12 = base + normAOff from by bv_addr] at hl
  have hle := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normB_code_sub_modCode_noNop_v5 a i
      (CodeReq.ofProg_mono_sub (base + normBOff) (base + normBOff + 72) divK_normB
        (divK_normB_last_prog 32) 18
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hl
  have hlef := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (b0 >>> (antiShift.toNat % 64))) ** (.x2 ↦ᵣ antiShift) **
     ((sp + 40) ↦ₘ b1') ** ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3'))
    (by pcFree) hle
  have h34 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hm3ef hlef
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h34

/-- v5 normalize-B full brick over `modCode_noNop_v5`.  MOD mirror of
    `divK_normB_full_spec_within_v5_noNop`. -/
theorem divK_normB_full_spec_within_v5_noNop_modCode
    (sp b0 b1 b2 b3 v5 v7 shift antiShift : Word) (base : Word) :
    cpsTripleWithin 21 (base + normBOff) (base + normAOff) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (normBFullPost sp b0 b1 b2 b3 shift antiShift) := by
  rw [normBFullPost_unfold]
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  have h1 := divK_normB_half1_within_v5_noNop_modCode sp b0 b1 b2 b3 v5 v7 shift antiShift base
  have h2 := divK_normB_half2_within_v5_noNop_modCode sp b0 b1 b2' b3' shift antiShift base
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) h1 h2)

-- ============================================================================
-- Brick 5: normalize-A (normAOff → loopSetupOff) over modCode_noNop_v5.
-- MOD mirror of `divK_normA_full_spec_within_v5_noNop` (NormAV5.lean), `_b5_mod`.
-- ============================================================================

/-- The normA block instructions are subsumed by `modCode_noNop_v5`. -/
private theorem divK_normA_code_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + normAOff) (divK_normA 40)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact sharedNoNop_v5_b5_mod a i h

/-- v5 normalize-A full brick over `modCode_noNop_v5`.  MOD mirror of
    `divK_normA_full_spec_within_v5_noNop`. -/
theorem divK_normA_full_spec_within_v5_noNop_modCode (sp a0 a1 a2 a3 v5 v7 v10 shift antiShift : Word)
    (u0Old u1Old u2Old u3Old u4Old : Word) (base : Word) :
    cpsTripleWithin 21 (base + normAOff) (base + loopSetupOff) (modCode_noNop_v5 base)
      (divKNormAFullPreNoNop sp v5 v7 v10 shift antiShift
        a0 a1 a2 a3 u0Old u1Old u2Old u3Old u4Old)
      (normAFullPost sp a0 a1 a2 a3 shift antiShift) := by
  rw [divKNormAFullPreNoNop_unfold, normAFullPost_unfold]
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  have htop := divK_normA_top_spec_within 24 4024 sp a3 v5 v7 antiShift u4Old (base + normAOff)
  simp only [se12_24] at htop
  have htope := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_modCode_noNop_v5 a i
      (CodeReq.ofProg_mono_sub (base + normAOff) (base + normAOff) (divK_normA 40)
        (divK_normA_top_prog 24 4024) 0
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) htop
  have htopef := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ v10) ** (.x6 ↦ᵣ shift) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) **
     ((sp + signExtend12 4032) ↦ₘ u3Old) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4056) ↦ₘ u0Old))
    (by pcFree) htope
  have hma1 := divK_normA_mergeA_spec_within 16 4032 sp a3 a2 u4 v10 shift antiShift u3Old (base + normAOff + 12)
  simp only [se12_16] at hma1
  rw [show (base + normAOff + 12 : Word) + 20 = base + normAOff + 32 from by bv_addr] at hma1
  have hma1e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_modCode_noNop_v5 a i
      (CodeReq.ofProg_mono_sub (base + normAOff) (base + normAOff + 12) (divK_normA 40)
        (divK_normA_mergeA_prog 16 4032) 3
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hma1
  have hma1ef := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4056) ↦ₘ u0Old))
    (by pcFree) hma1e
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) htopef hma1ef
  have hmb := divK_normA_mergeB_spec_within 8 4040 sp a2 a1 u3 (a2 >>> (antiShift.toNat % 64))
    shift antiShift u2Old (base + normAOff + 32)
  simp only [se12_8] at hmb
  rw [show (base + normAOff + 32 : Word) + 20 = base + normAOff + 52 from by bv_addr] at hmb
  have hmbe := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_modCode_noNop_v5 a i
      (CodeReq.ofProg_mono_sub (base + normAOff) (base + normAOff + 32) (divK_normA 40)
        (divK_normA_mergeB_prog 8 4040) 8
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hmb
  have hmbef := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4048) ↦ₘ u1Old) ** ((sp + signExtend12 4056) ↦ₘ u0Old))
    (by pcFree) hmbe
  have h123 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12 hmbef
  have hma2 := divK_normA_mergeA_spec_within 0 4048 sp a1 a0 u2 (a1 >>> (antiShift.toNat % 64))
    shift antiShift u1Old (base + normAOff + 52)
  simp only [se12_0] at hma2
  rw [show (base + normAOff + 52 : Word) + 20 = base + normAOff + 72 from by bv_addr] at hma2
  have hma2e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_modCode_noNop_v5 a i
      (CodeReq.ofProg_mono_sub (base + normAOff) (base + normAOff + 52) (divK_normA 40)
        (divK_normA_mergeA_prog 0 4048) 13
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hma2
  have hma2ef := cpsTripleWithin_frameR
    (((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4056) ↦ₘ u0Old))
    (by pcFree) hma2e
  have h1234 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123 hma2ef
  have hlast := divK_normA_last_spec_within 4056 sp a0 shift u0Old (base + normAOff + 72)
  rw [show (base + normAOff + 72 : Word) + 8 = base + normAOff + 80 from by bv_addr] at hlast
  have hlaste := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_modCode_noNop_v5 a i
      (CodeReq.ofProg_mono_sub (base + normAOff) (base + normAOff + 72) (divK_normA 40)
        (divK_normA_last_prog 4056) 18
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hlast
  have hlastef := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ u1) ** (.x10 ↦ᵣ (a0 >>> (antiShift.toNat % 64))) ** (.x2 ↦ᵣ antiShift) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1))
    (by pcFree) hlaste
  have h12345 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1234 hlastef
  have hjal := jal_x0_spec_gen_within 40 (base + normAOff + 80)
  rw [show (base + normAOff + 80 : Word) + signExtend21 40 = base + loopSetupOff from by rv64_addr] at hjal
  have hjale := cpsTripleWithin_extend_code (hmono := by
    intro a i h
    exact divK_normA_code_sub_modCode_noNop_v5 a i
      (CodeReq.singleton_mono (by
        have hlookup := CodeReq.ofProg_lookup (base + normAOff) (divK_normA 40) 20
          (by decide) (by decide)
        rw [show (base + normAOff : Word) + BitVec.ofNat 64 (4 * 20) = base + normAOff + 80 from by bv_addr]
          at hlookup
        exact hlookup) a i h)) hjal
  let postAll := (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ u1) ** (.x7 ↦ᵣ u0) **
    (.x10 ↦ᵣ (a0 >>> (antiShift.toNat % 64))) **
    (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
    ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
    ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
    ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1) **
    ((sp + signExtend12 4056) ↦ₘ u0)
  have hjalef := cpsTripleWithin_frameR postAll (by pcFree) hjale
  have hjal_clean : cpsTripleWithin 1 (base + normAOff + 80) (base + loopSetupOff) (modCode_noNop_v5 base) postAll postAll :=
    cpsTripleWithin_weaken
      (fun h hp => by show (empAssertion ** postAll) h; rw [sepConj_emp_left']; exact hp)
      (fun h hp => by rw [sepConj_emp_left'] at hp; exact hp)
      hjalef
  have h123456 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12345 hjal_clean
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h123456

-- ============================================================================
-- Brick 6: copy-AU (copyAUOff → loopSetupOff, shift = 0 path) over modCode_noNop_v5.
-- MOD mirror of `divK_copyAU_spec_within_v5_noNop` (CopyAUV5.lean), `_b6_mod`.
-- ============================================================================

/-- v5 copy-AU (shift = 0) over `modCode_noNop_v5`: copy `a[0..3]` into `u[0..3]`,
    zero `u[4]`.  MOD mirror of `divK_copyAU_spec_within_v5_noNop`. -/
theorem divK_copyAU_spec_within_v5_noNop_modCode (sp base : Word)
    (a0 a1 a2 a3 u0 u1 u2 u3 u4 v5 : Word) :
    cpsTripleWithin 9 (base + copyAUOff) (base + loopSetupOff) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ u4))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ a3) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ a0) ** ((sp + signExtend12 4048) ↦ₘ a1) **
       ((sp + signExtend12 4040) ↦ₘ a2) ** ((sp + signExtend12 4032) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ (0 : Word))) := by
  have hbody := divK_copyAU_spec_within sp (base + copyAUOff)
    a0 a1 a2 a3 u0 u1 u2 u3 u4 v5
  simp only [divK_copyAU_code] at hbody
  rw [show (base + copyAUOff) + 36 = base + loopSetupOff from by
    simp only [copyAUOff, loopSetupOff]; bv_addr] at hbody
  exact cpsTripleWithin_extend_code sharedNoNop_v5_b6_mod hbody

-- ============================================================================
-- Brick 7: loop-setup (loopSetupOff → loopBodyOff) over modCode_noNop_v5.
-- MOD mirror of `divK_loopSetup_ntaken_spec_within_v5_noNop` (LoopSetupV5.lean), `_b7_mod`.
-- ============================================================================

/-- The loop-setup block instructions are subsumed by `modCode_noNop_v5`. -/
private theorem divK_loopSetup_code_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (divK_loopSetup_code 464 (base + loopSetupOff)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact sharedNoNop_v5_b7_mod a i h

/-- BLT singleton at base+loopSetupOff+12 is subsumed by `modCode_noNop_v5`. -/
private theorem blt_loopSetup_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + loopSetupOff + 12) (.BLT .x9 .x0 464)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + loopSetupOff) (divK_loopSetup 464) 3
    (by decide) (by decide)
  rw [show (BitVec.ofNat 64 (4 * 3) : Word) = (12 : Word) from by decide] at hlookup
  exact divK_loopSetup_code_sub_modCode_noNop_v5 a i
    (CodeReq.singleton_mono hlookup a i h)

/-- LoopSetup (m ≥ 0, n ≤ 4) over `modCode_noNop_v5`: falls through to the loop
    body.  MOD mirror of `divK_loopSetup_ntaken_spec_within_v5_noNop`. -/
theorem divK_loopSetup_ntaken_spec_within_v5_noNop_modCode (sp n v1 v5 : Word) (base : Word)
    (hm_ge : ¬BitVec.slt (signExtend12 (4 : BitVec 12) - n) (0 : Word)) :
    let m := signExtend12 (4 : BitVec 12) - n
    cpsTripleWithin 4 (base + loopSetupOff) (base + loopBodyOff) (modCode_noNop_v5 base)
      (divKLoopSetupNtakenPreNoNop sp v5 v1 n)
      (divKLoopSetupNtakenPostNoNop sp n m) := by
  intro m
  rw [divKLoopSetupNtakenPreNoNop_unfold, divKLoopSetupNtakenPostNoNop_unfold]
  have hbody := divK_loopSetup_body_spec_within sp n v1 v5 464 (base + loopSetupOff)
  have hbodye := cpsTripleWithin_extend_code divK_loopSetup_code_sub_modCode_noNop_v5 hbody
  have hblt_raw := blt_spec_gen_within .x9 .x0 464 m (0 : Word) (base + loopSetupOff + 12)
  rw [show (base + loopSetupOff + 12 : Word) + signExtend13 464 = base + denormOff from by rv64_addr,
      show (base + loopSetupOff + 12 : Word) + 4 = base + loopBodyOff from by bv_addr] at hblt_raw
  have hblt_clean := cpsBranchWithin_ntakenStripPure2 hblt_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _).mp h_rest).2 hm_ge)
  have hblte := cpsTripleWithin_extend_code blt_loopSetup_sub_modCode_noNop_v5 hblt_clean
  have hbltef := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) ** ((sp + signExtend12 3984) ↦ₘ n))
    (by pcFree) hblte
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbodye hbltef
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12

end EvmAsm.Evm64
