/-
  EvmAsm.Evm64.DivMod.Compose.FastPrefixV6Mod

  MOD v6 fast-path prefix, over `modCodeV6` (Brick 1 of the MOD v6 fast arm).
  The fast-path prefix blocks (clz, fastSetup, normA, copyAU) are the SAME
  instructions at the SAME offsets in `modCodeV6` as in `divCodeV6`; only the
  block *list* differs (mod inserts `divK_fastDenorm` + `divK_mod_epilogue` and
  shifts div128/v5).  So each prefix spec is a verbatim mirror of the DIV
  `divK_*_spec_within_v6` proof, swapping the code-subsumption extension lemmas
  `_sub_divCodeV6 → _sub_modCodeV6` (built here) and the code surface
  `divCodeV6 → modCodeV6`.  The underlying bare-program specs and the
  `clz_addr_v6_*` address lemmas are shared verbatim (offsets identical).
-/

import EvmAsm.Evm64.DivMod.Compose.CLZV6
import EvmAsm.Evm64.DivMod.Compose.FastSetupV6
import EvmAsm.Evm64.DivMod.Compose.NormAV6

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (se12_0 se12_8 se12_16 se12_24)
open EvmAsm.Rv64.AddrNorm (bv64_4mul_3)

-- ============================================================================
-- V6-MOD-aware skipBlock: the base `skipBlockV6` simp set plus the mod-only
-- block offsets/lengths (`modV6*Off`, `divK_fastDenorm`, `divK_mod_epilogue`),
-- so disjointness `bv_omega` closes even when peeling the mod-only blocks.
-- ============================================================================

theorem divK_fastDenorm_len' : divK_fastDenorm.length = 7 := by rfl
theorem divK_mod_epilogue_len' (off : BitVec 21) :
    (divK_mod_epilogue off).length = 10 := by unfold divK_mod_epilogue; rfl

macro "skipBlockV6Mod" : tactic =>
  `(tactic| apply CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
        simp only [divK_dispatchN1_length, divK_clz_len, divK_fastSetup_length,
          divK_normA_len, divK_copyAU_len, divK_fastDigit_length,
          divK_div_epilogue_len', divK_div128_v5_len,
          divK_fastDenorm_len', divK_mod_epilogue_len',
          dispatchN1Off, v6ClzOff, v6SetupOff, v6NormAOff, v6CopyAUOff,
          v6Digit3Off, v6Digit2Off, v6Digit1Off, v6Digit0Off,
          modV6DenormOff, modV6EpilogueOff, modV6Div128Off] at hk1 hk2
        bv_omega)))

-- ============================================================================
-- Code-subsumption of each prefix block by `modCodeV6`.
-- (block indices in modCodeV6: dispatch=0, clz=1, setup=2, normA=3, copyAU=4)
-- ============================================================================

private theorem divK_clz_code_sub_modCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + v6ClzOff) divK_clz) a = some i →
      (modCodeV6 base) a = some i := by
  unfold modCodeV6; simp only [CodeReq.unionAll_cons]
  skipBlockV6Mod
  exact CodeReq.union_mono_left

private theorem clz_stage_sub_modCodeV6 {base : Word}
    (K M_s : BitVec 6) (M_a : BitVec 12) (k : Nat)
    (hk : k + (divK_clz_stage_prog K M_s M_a).length ≤ divK_clz.length)
    (hslice : (divK_clz.drop k).take (divK_clz_stage_prog K M_s M_a).length =
      divK_clz_stage_prog K M_s M_a)
    (hbound : 4 * divK_clz.length < 2 ^ 64) :
    ∀ a i, (divK_clz_stage_code K M_s M_a ((base + v6ClzOff) + BitVec.ofNat 64 (4 * k))) a = some i →
      (modCodeV6 base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_modCodeV6 a i
    (CodeReq.ofProg_mono_sub (base + v6ClzOff) _ divK_clz _ k
      rfl hslice hk hbound a i h)

private theorem clz_last_sub_modCodeV6 {base : Word} (k : Nat)
    (hk : k + divK_clz_last_prog.length ≤ divK_clz.length)
    (hslice : (divK_clz.drop k).take divK_clz_last_prog.length = divK_clz_last_prog)
    (hbound : 4 * divK_clz.length < 2 ^ 64) :
    ∀ a i, (divK_clz_last_code ((base + v6ClzOff) + BitVec.ofNat 64 (4 * k))) a = some i →
      (modCodeV6 base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_modCodeV6 a i
    (CodeReq.ofProg_mono_sub (base + v6ClzOff) _ divK_clz _ k
      rfl hslice hk hbound a i h)

private theorem clz_init_sub_modCodeV6 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + v6ClzOff) (.ADDI .x6 .x0 0)) a = some i →
      (modCodeV6 base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_modCodeV6 a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup (base + v6ClzOff) divK_clz 0
      (by decide) (by decide)) a i (by rwa [show (base + v6ClzOff : Word) =
        base + v6ClzOff + BitVec.ofNat 64 (4 * 0) from by bv_addr] at h))

-- ============================================================================
-- CLZ full brick over `modCodeV6` (24 steps, v6ClzOff → v6SetupOff).
-- Verbatim mirror of `divK_clz_spec_within_v6` (CLZV6.lean:107).
-- ============================================================================

theorem divK_clz_spec_within_v6_mod (val v6Old v7Old : Word) (base : Word) :
    cpsTripleWithin 24 (base + v6ClzOff) (base + v6SetupOff) (modCodeV6 base)
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ v6Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (clzResult val).2) ** (.x6 ↦ᵣ (clzResult val).1) **
       (.x7 ↦ᵣ (clzResult val).2 >>> (63 : Nat)) ** (.x0 ↦ᵣ (0 : Word))) := by
  unfold clzResult
  have I := divK_clz_init_spec_within v6Old (base + v6ClzOff)
  have Ie := cpsTripleWithin_extend_code (hmono := clz_init_sub_modCodeV6) I
  have Ief := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ val) ** (.x7 ↦ᵣ v7Old)) (by pcFree) Ie
  have S0 := divK_clz_stage_combined_within 32 32 32 val (signExtend12 0) v7Old
    ((base + v6ClzOff) + BitVec.ofNat 64 (4 * 1))
  dsimp only [] at S0
  have S0e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_modCodeV6 32 32 32 1
    (by decide) (by decide) (by decide)) S0
  rw [show (base + v6ClzOff : Word) + BitVec.ofNat 64 (4 * 1) = base + v6ClzOff + 4 from by bv_addr] at S0e
  rw [clz_addr_v6_1] at S0e
  seqFrame Ief S0e
  let v0 := if val >>> (32 : BitVec 6).toNat ≠ 0 then val else val <<< (32 : BitVec 6).toNat
  let c0 := if val >>> (32 : BitVec 6).toNat ≠ 0 then signExtend12 (0 : BitVec 12)
    else signExtend12 (0 : BitVec 12) + signExtend12 (32 : BitVec 12)
  have S1 := divK_clz_stage_combined_within 48 16 16 v0 c0 (val >>> (32 : BitVec 6).toNat)
    ((base + v6ClzOff) + BitVec.ofNat 64 (4 * 5))
  dsimp only [] at S1
  have S1e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_modCodeV6 48 16 16 5
    (by decide) (by decide) (by decide)) S1
  rw [show (base + v6ClzOff : Word) + BitVec.ofNat 64 (4 * 5) = base + v6ClzOff + 20 from by bv_addr] at S1e
  rw [clz_addr_v6_2] at S1e
  seqFrame IefS0e S1e
  let v1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then v0 else v0 <<< (16 : BitVec 6).toNat
  let c1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then c0 else c0 + signExtend12 (16 : BitVec 12)
  have S2 := divK_clz_stage_combined_within 56 8 8 v1 c1 (v0 >>> (48 : BitVec 6).toNat)
    ((base + v6ClzOff) + BitVec.ofNat 64 (4 * 9))
  dsimp only [] at S2
  have S2e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_modCodeV6 56 8 8 9
    (by decide) (by decide) (by decide)) S2
  rw [show (base + v6ClzOff : Word) + BitVec.ofNat 64 (4 * 9) = base + v6ClzOff + 36 from by bv_addr] at S2e
  rw [clz_addr_v6_3] at S2e
  seqFrame IefS0eS1e S2e
  let v2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then v1 else v1 <<< (8 : BitVec 6).toNat
  let c2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then c1 else c1 + signExtend12 (8 : BitVec 12)
  have S3 := divK_clz_stage_combined_within 60 4 4 v2 c2 (v1 >>> (56 : BitVec 6).toNat)
    ((base + v6ClzOff) + BitVec.ofNat 64 (4 * 13))
  dsimp only [] at S3
  have S3e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_modCodeV6 60 4 4 13
    (by decide) (by decide) (by decide)) S3
  rw [show (base + v6ClzOff : Word) + BitVec.ofNat 64 (4 * 13) = base + v6ClzOff + 52 from by bv_addr] at S3e
  rw [clz_addr_v6_4] at S3e
  seqFrame IefS0eS1eS2e S3e
  let v3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then v2 else v2 <<< (4 : BitVec 6).toNat
  let c3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then c2 else c2 + signExtend12 (4 : BitVec 12)
  have S4 := divK_clz_stage_combined_within 62 2 2 v3 c3 (v2 >>> (60 : BitVec 6).toNat)
    ((base + v6ClzOff) + BitVec.ofNat 64 (4 * 17))
  dsimp only [] at S4
  have S4e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_modCodeV6 62 2 2 17
    (by decide) (by decide) (by decide)) S4
  rw [show (base + v6ClzOff : Word) + BitVec.ofNat 64 (4 * 17) = base + v6ClzOff + 68 from by bv_addr] at S4e
  rw [clz_addr_v6_5] at S4e
  seqFrame IefS0eS1eS2eS3e S4e
  let v4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then v3 else v3 <<< (2 : BitVec 6).toNat
  let c4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then c3 else c3 + signExtend12 (2 : BitVec 12)
  have S5 := divK_clz_last_combined_within v4 c4 (v3 >>> (62 : BitVec 6).toNat)
    ((base + v6ClzOff) + BitVec.ofNat 64 (4 * 21))
  dsimp only [] at S5
  have S5e := cpsTripleWithin_extend_code (hmono := clz_last_sub_modCodeV6 21
    (by decide) (by decide) (by decide)) S5
  rw [show (base + v6ClzOff : Word) + BitVec.ofNat 64 (4 * 21) = base + v6ClzOff + 84 from by bv_addr] at S5e
  rw [clz_addr_v6_6] at S5e
  seqFrame IefS0eS1eS2eS3eS4e S5e
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    IefS0eS1eS2eS3eS4eS5e

-- ============================================================================
-- fastSetup over `modCodeV6` (block index 2).  Mirror of FastSetupV6.lean
-- `divK_fastSetup_{body,shiftNz,shift0}_spec_within_v6`.
-- ============================================================================

private theorem divK_fastSetup_code_sub_modCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + v6SetupOff) (divK_fastSetup 88)) a = some i →
      (modCodeV6 base) a = some i := by
  unfold modCodeV6; simp only [CodeReq.unionAll_cons]
  skipBlockV6Mod; skipBlockV6Mod
  exact CodeReq.union_mono_left

theorem divK_fastSetup_body_spec_within_v6_mod (sp v5 s b0 v2Old m3992 m3984 : Word)
    (base : Word) :
    let antiShift := (0 : Word) - s
    let b0Prime := b0 <<< (s.toNat % 64)
    cpsTripleWithin 6 (base + v6SetupOff) (base + v6SetupOff + 24) (modCodeV6 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ s) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x2 ↦ᵣ v2Old) **
       ((sp + signExtend12 32) ↦ₘ b0) **
       ((sp + signExtend12 3992) ↦ₘ m3992) **
       ((sp + signExtend12 3984) ↦ₘ m3984))
      (divKFastSetupPost sp s b0 antiShift b0Prime) := by
  intro antiShift b0Prime
  have h := divK_fastSetup_body_spec_within sp v5 s b0 v2Old m3992 m3984 (base + v6SetupOff)
  exact cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_fastSetup_code_sub_modCodeV6 a i
      (CodeReq.ofProg_mono_sub (base + v6SetupOff) (base + v6SetupOff) (divK_fastSetup 88)
        divK_fastSetup_body_prog 0
        (by bv_addr) divK_fastSetup_body_slice (by decide) (by decide) a i h)) h

theorem divK_fastSetup_shiftNz_spec_within_v6_mod (sp v5 s b0 v2Old m3992 m3984 : Word)
    (base : Word) (hs_ne_0 : s ≠ (0 : Word)) :
    let antiShift := (0 : Word) - s
    let b0Prime := b0 <<< (s.toNat % 64)
    cpsTripleWithin 7 (base + v6SetupOff) (base + v6NormAOff) (modCodeV6 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ s) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x2 ↦ᵣ v2Old) **
       ((sp + signExtend12 32) ↦ₘ b0) **
       ((sp + signExtend12 3992) ↦ₘ m3992) **
       ((sp + signExtend12 3984) ↦ₘ m3984))
      (divKFastSetupPost sp s b0 antiShift b0Prime) := by
  intro antiShift b0Prime
  have hbody := divK_fastSetup_body_spec_within_v6_mod sp v5 s b0 v2Old m3992 m3984 base
  have hbody_u : cpsTripleWithin 6 (base + v6SetupOff) (base + v6SetupOff + 24) (modCodeV6 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ s) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x2 ↦ᵣ v2Old) **
       ((sp + signExtend12 32) ↦ₘ b0) **
       ((sp + signExtend12 3992) ↦ₘ m3992) **
       ((sp + signExtend12 3984) ↦ₘ m3984))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0Prime) ** (.x6 ↦ᵣ s) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x2 ↦ᵣ antiShift) **
       ((sp + signExtend12 32) ↦ₘ b0) **
       ((sp + signExtend12 3992) ↦ₘ s) **
       ((sp + signExtend12 3984) ↦ₘ b0Prime)) :=
    divKFastSetupPost_unfold ▸ hbody
  have hbeq := beq_spec_gen_within .x6 .x0 88 s (0 : Word) (base + v6SetupOff + 24)
  rw [divK_fastSetup_beq_taken_addr, divK_fastSetup_beq_ntaken_addr] at hbeq
  have hbeq_ntaken := cpsBranchWithin_ntakenStripPure2 hbeq
    (fun hp hQt => by
      obtain ⟨w1, w2, _, _, _, _, hw_rest⟩ := hQt
      obtain ⟨h3, _, _, _, hpure⟩ := hw_rest
      exact absurd hpure.2 hs_ne_0)
  have hbeq_e := cpsTripleWithin_extend_code (hmono := by
    intro a i h
    exact divK_fastSetup_code_sub_modCodeV6 a i
      (CodeReq.singleton_mono (by
        have hlookup := CodeReq.ofProg_lookup (base + v6SetupOff) (divK_fastSetup 88) 6
          (by decide) (by decide)
        rw [show (base + v6SetupOff : Word) + BitVec.ofNat 64 (4 * 6) =
          base + v6SetupOff + 24 from by bv_addr] at hlookup
        exact hlookup) a i h)) hbeq_ntaken
  have hbeq_f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0Prime) ** (.x2 ↦ᵣ antiShift) **
     ((sp + signExtend12 32) ↦ₘ b0) **
     ((sp + signExtend12 3992) ↦ₘ s) **
     ((sp + signExtend12 3984) ↦ₘ b0Prime))
    (by pcFree) hbeq_e
  have h := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody_u hbeq_f
  rw [divKFastSetupPost_unfold]
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h

theorem divK_fastSetup_shift0_spec_within_v6_mod (sp v5 s b0 v2Old m3992 m3984 : Word)
    (base : Word) (hs_eq_0 : s = (0 : Word)) :
    let antiShift := (0 : Word) - s
    let b0Prime := b0 <<< (s.toNat % 64)
    cpsTripleWithin 7 (base + v6SetupOff) (base + v6CopyAUOff) (modCodeV6 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ s) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x2 ↦ᵣ v2Old) **
       ((sp + signExtend12 32) ↦ₘ b0) **
       ((sp + signExtend12 3992) ↦ₘ m3992) **
       ((sp + signExtend12 3984) ↦ₘ m3984))
      (divKFastSetupPost sp s b0 antiShift b0Prime) := by
  intro antiShift b0Prime
  have hbody := divK_fastSetup_body_spec_within_v6_mod sp v5 s b0 v2Old m3992 m3984 base
  have hbody_u : cpsTripleWithin 6 (base + v6SetupOff) (base + v6SetupOff + 24) (modCodeV6 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ s) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x2 ↦ᵣ v2Old) **
       ((sp + signExtend12 32) ↦ₘ b0) **
       ((sp + signExtend12 3992) ↦ₘ m3992) **
       ((sp + signExtend12 3984) ↦ₘ m3984))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0Prime) ** (.x6 ↦ᵣ s) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x2 ↦ᵣ antiShift) **
       ((sp + signExtend12 32) ↦ₘ b0) **
       ((sp + signExtend12 3992) ↦ₘ s) **
       ((sp + signExtend12 3984) ↦ₘ b0Prime)) :=
    divKFastSetupPost_unfold ▸ hbody
  have hbeq := beq_spec_gen_within .x6 .x0 88 s (0 : Word) (base + v6SetupOff + 24)
  rw [divK_fastSetup_beq_taken_addr, divK_fastSetup_beq_ntaken_addr] at hbeq
  have hbeq_taken := cpsBranchWithin_takenStripPure2 hbeq
    (fun hp hQf => by
      obtain ⟨w1, w2, _, _, _, _, hw_rest⟩ := hQf
      obtain ⟨h3, _, _, _, hpure⟩ := hw_rest
      exact absurd hs_eq_0 hpure.2)
  have hbeq_e := cpsTripleWithin_extend_code (hmono := by
    intro a i h
    exact divK_fastSetup_code_sub_modCodeV6 a i
      (CodeReq.singleton_mono (by
        have hlookup := CodeReq.ofProg_lookup (base + v6SetupOff) (divK_fastSetup 88) 6
          (by decide) (by decide)
        rw [show (base + v6SetupOff : Word) + BitVec.ofNat 64 (4 * 6) =
          base + v6SetupOff + 24 from by bv_addr] at hlookup
        exact hlookup) a i h)) hbeq_taken
  have hbeq_f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0Prime) ** (.x2 ↦ᵣ antiShift) **
     ((sp + signExtend12 32) ↦ₘ b0) **
     ((sp + signExtend12 3992) ↦ₘ s) **
     ((sp + signExtend12 3984) ↦ₘ b0Prime))
    (by pcFree) hbeq_e
  have h := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody_u hbeq_f
  rw [divKFastSetupPost_unfold]
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h

-- ============================================================================
-- normA / copyAU over `modCodeV6` (block indices 3, 4).  Mirror of
-- NormAV6.lean `divK_normA_full_spec_within_v6` / `divK_copyAU_full_spec_within_v6`.
-- ============================================================================

private theorem divK_normA_code_sub_modCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + v6NormAOff) (divK_normA 40)) a = some i →
      (modCodeV6 base) a = some i := by
  unfold modCodeV6; simp only [CodeReq.unionAll_cons]
  skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod
  exact CodeReq.union_mono_left

private theorem divK_copyAU_code_sub_modCodeV6 {base : Word} :
    ∀ a i, (divK_copyAU_code (base + v6CopyAUOff)) a = some i →
      (modCodeV6 base) a = some i := by
  unfold modCodeV6 divK_copyAU_code; simp only [CodeReq.unionAll_cons]
  skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod
  exact CodeReq.union_mono_left

theorem divK_normA_full_spec_within_v6_mod (sp a0 a1 a2 a3 v5 v7 v10 shift antiShift : Word)
    (u0Old u1Old u2Old u3Old u4Old : Word) (base : Word) :
    cpsTripleWithin 21 (base + v6NormAOff) (base + v6Digit3Off) (modCodeV6 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4056) ↦ₘ u0Old))
      (normAFullPost sp a0 a1 a2 a3 shift antiShift) := by
  rw [normAFullPost_unfold]
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  have htop := divK_normA_top_spec_within 24 4024 sp a3 v5 v7 antiShift u4Old (base + v6NormAOff)
  simp only [se12_24] at htop
  have htope := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_modCodeV6 a i
      (CodeReq.ofProg_mono_sub (base + v6NormAOff) (base + v6NormAOff) (divK_normA 40)
        (divK_normA_top_prog 24 4024) 0
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) htop
  have htopef := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ v10) ** (.x6 ↦ᵣ shift) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) **
     ((sp + signExtend12 4032) ↦ₘ u3Old) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4056) ↦ₘ u0Old))
    (by pcFree) htope
  have hma1 := divK_normA_mergeA_spec_within 16 4032 sp a3 a2 u4 v10 shift antiShift u3Old (base + v6NormAOff + 12)
  simp only [se12_16] at hma1
  rw [show (base + v6NormAOff + 12 : Word) + 20 = base + v6NormAOff + 32 from by bv_addr] at hma1
  have hma1e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_modCodeV6 a i
      (CodeReq.ofProg_mono_sub (base + v6NormAOff) (base + v6NormAOff + 12) (divK_normA 40)
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
    shift antiShift u2Old (base + v6NormAOff + 32)
  simp only [se12_8] at hmb
  rw [show (base + v6NormAOff + 32 : Word) + 20 = base + v6NormAOff + 52 from by bv_addr] at hmb
  have hmbe := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_modCodeV6 a i
      (CodeReq.ofProg_mono_sub (base + v6NormAOff) (base + v6NormAOff + 32) (divK_normA 40)
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
    shift antiShift u1Old (base + v6NormAOff + 52)
  simp only [se12_0] at hma2
  rw [show (base + v6NormAOff + 52 : Word) + 20 = base + v6NormAOff + 72 from by bv_addr] at hma2
  have hma2e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_modCodeV6 a i
      (CodeReq.ofProg_mono_sub (base + v6NormAOff) (base + v6NormAOff + 52) (divK_normA 40)
        (divK_normA_mergeA_prog 0 4048) 13
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hma2
  have hma2ef := cpsTripleWithin_frameR
    (((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4056) ↦ₘ u0Old))
    (by pcFree) hma2e
  have h1234 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123 hma2ef
  have hlast := divK_normA_last_spec_within 4056 sp a0 shift u0Old (base + v6NormAOff + 72)
  rw [show (base + v6NormAOff + 72 : Word) + 8 = base + v6NormAOff + 80 from by bv_addr] at hlast
  have hlaste := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_modCodeV6 a i
      (CodeReq.ofProg_mono_sub (base + v6NormAOff) (base + v6NormAOff + 72) (divK_normA 40)
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
  have hjal := jal_x0_spec_gen_within 40 (base + v6NormAOff + 80)
  rw [show (base + v6NormAOff + 80 : Word) + signExtend21 40 = base + v6Digit3Off from by rv64_addr] at hjal
  have hjale := cpsTripleWithin_extend_code (hmono := by
    intro a i h
    exact divK_normA_code_sub_modCodeV6 a i
      (CodeReq.singleton_mono (by
        have hlookup := CodeReq.ofProg_lookup (base + v6NormAOff) (divK_normA 40) 20
          (by decide) (by decide)
        rw [show (base + v6NormAOff : Word) + BitVec.ofNat 64 (4 * 20) = base + v6NormAOff + 80 from by bv_addr]
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
  have hjal_clean : cpsTripleWithin 1 (base + v6NormAOff + 80) (base + v6Digit3Off) (modCodeV6 base) postAll postAll :=
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

theorem divK_copyAU_full_spec_within_v6_mod (sp : Word)
    (a0 a1 a2 a3 : Word) (u0 u1 u2 u3 u4 v5 : Word) (base : Word) :
    cpsTripleWithin 9 (base + v6CopyAUOff) (base + v6Digit3Off) (modCodeV6 base)
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
  have hcopy := divK_copyAU_spec_within sp (base + v6CopyAUOff) a0 a1 a2 a3 u0 u1 u2 u3 u4 v5
  rw [show (base + v6CopyAUOff : Word) + 36 = base + v6Digit3Off from by bv_addr] at hcopy
  exact cpsTripleWithin_extend_code divK_copyAU_code_sub_modCodeV6 hcopy

end EvmAsm.Evm64
