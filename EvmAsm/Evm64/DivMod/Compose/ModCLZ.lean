/-
  EvmAsm.Evm64.DivMod.Compose.ModCLZ

  MOD mirror of CLZ (Count Leading Zeros) composition.
  Proof structure mirrors CLZ.lean with modCode instead of divCode.
  Block 2 (CLZ at base+116) is identical between divCode and modCode.
-/

import EvmAsm.Evm64.DivMod.Compose.CLZ

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- MOD CodeReq subsumption lemmas for block 2 (CLZ)
-- ============================================================================

/-- CLZ code (block 2) is subsumed by modCode. -/
private theorem divK_clz_code_sub_modCode {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + clzOff) divK_clz) a = some i →
      (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock
  exact CodeReq.union_mono_left

/-- Helper: CLZ stage at instruction index k is subsumed by modCode. -/
private theorem clz_stage_sub_mod {base : Word}
    (K M_s : BitVec 6) (M_a : BitVec 12) (k : Nat)
    (hk : k + (divK_clz_stage_prog K M_s M_a).length ≤ divK_clz.length)
    (hslice : (divK_clz.drop k).take (divK_clz_stage_prog K M_s M_a).length =
      divK_clz_stage_prog K M_s M_a)
    (hbound : 4 * divK_clz.length < 2 ^ 64) :
    ∀ a i, (divK_clz_stage_code K M_s M_a ((base + clzOff) + BitVec.ofNat 64 (4 * k))) a = some i →
      (modCode base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_modCode a i
    (CodeReq.ofProg_mono_sub (base + clzOff) _ divK_clz _ k
      rfl hslice hk hbound a i h)

/-- Helper: CLZ last stage at instruction index k is subsumed by modCode. -/
private theorem clz_last_sub_mod {base : Word} (k : Nat)
    (hk : k + divK_clz_last_prog.length ≤ divK_clz.length)
    (hslice : (divK_clz.drop k).take divK_clz_last_prog.length = divK_clz_last_prog)
    (hbound : 4 * divK_clz.length < 2 ^ 64) :
    ∀ a i, (divK_clz_last_code ((base + clzOff) + BitVec.ofNat 64 (4 * k))) a = some i →
      (modCode base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_modCode a i
    (CodeReq.ofProg_mono_sub (base + clzOff) _ divK_clz _ k
      rfl hslice hk hbound a i h)

/-- Helper: CLZ init singleton (ADDI x6 x0 0 at base+116) is subsumed by modCode. -/
private theorem clz_init_sub_mod {base : Word} :
    ∀ a i, (CodeReq.singleton (base + clzOff) (.ADDI .x6 .x0 0)) a = some i →
      (modCode base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_modCode a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup (base + clzOff) divK_clz 0
      (by decide) (by decide)) a i (by rwa [show (base + clzOff : Word) =
        base + clzOff + BitVec.ofNat 64 (4 * 0) from by bv_addr] at h))

-- Address lemmas for CLZ stages (reused from CLZ.lean, but those are private so we redefine)
private theorem mod_clz_addr1 {base : Word} : (base + clzOff + 4 : Word) + 16 = base + clzOff + 20 := by bv_addr
private theorem mod_clz_addr2 {base : Word} : (base + clzOff + 20 : Word) + 16 = base + clzOff + 36 := by bv_addr
private theorem mod_clz_addr3 {base : Word} : (base + clzOff + 36 : Word) + 16 = base + clzOff + 52 := by bv_addr
private theorem mod_clz_addr4 {base : Word} : (base + clzOff + 52 : Word) + 16 = base + clzOff + 68 := by bv_addr
private theorem mod_clz_addr5 {base : Word} : (base + clzOff + 68 : Word) + 16 = base + clzOff + 84 := by bv_addr
private theorem mod_clz_addr6 {base : Word} : (base + clzOff + 84 : Word) + 12 = base + phaseC2Off := by bv_addr

/-- Combined CLZ stage: handles both taken and ntaken with conditional postcondition.
    (Reused from CLZ.lean — the stage specs are code-generic, only subsumption differs.) -/
private theorem mod_clz_stage_combined
    (K M_s : BitVec 6) (M_a : BitVec 12) (val count v7 : Word) (base : Word) :
    let cr := divK_clz_stage_code K M_s M_a base
    let val' := if val >>> K.toNat ≠ 0 then val else val <<< M_s.toNat
    let count' := if val >>> K.toNat ≠ 0 then count else count + signExtend12 M_a
    cpsTripleWithin 4 base (base + 16) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val') ** (.x6 ↦ᵣ count') **
       (.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro cr; dsimp only []
  by_cases h : val >>> K.toNat ≠ 0
  · simp only [if_pos h]
    exact cpsTripleWithin_mono_nSteps (by decide)
      (divK_clz_stage_taken_spec_within K M_s M_a val count v7 base h)
  · push Not at h
    simp only [if_neg (show ¬(val >>> K.toNat ≠ 0) from not_not.mpr h)]
    have hs := divK_clz_stage_ntaken_spec_within K M_s M_a val count v7 base h
    exact cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by rw [show (val >>> K.toNat : Word) = 0 from h]; exact hp) hs

/-- Combined CLZ last stage: handles both taken and ntaken. -/
private theorem mod_clz_last_combined (val count v7 : Word) (base : Word) :
    let cr := divK_clz_last_code base
    let count' := if val >>> (63 : Nat) ≠ 0 then count else count + signExtend12 (1 : BitVec 12)
    cpsTripleWithin 3 base (base + 12) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count') **
       (.x7 ↦ᵣ (val >>> (63 : Nat))) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro cr; dsimp only []
  by_cases h : val >>> (63 : Nat) ≠ 0
  · simp only [if_pos h]
    exact cpsTripleWithin_mono_nSteps (by decide)
      (divK_clz_last_taken_spec_within val count v7 base h)
  · push Not at h
    simp only [if_neg (show ¬(val >>> (63 : Nat) ≠ 0) from not_not.mpr h)]
    have hs := divK_clz_last_ntaken_spec_within val count v7 base h
    exact cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by rw [show (val >>> (63 : Nat) : Word) = 0 from h]; exact hp) hs

/-- Full CLZ composition for modCode: 24 instructions at base+116 -> base+212.
    Mirror of divK_clz_spec_within with modCode instead of divCode. -/
theorem mod_clz_spec_within (val v6Old v7Old : Word) (base : Word) :
    cpsTripleWithin 24 (base + clzOff) (base + phaseC2Off) (modCode base)
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ v6Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (clzResult val).2) ** (.x6 ↦ᵣ (clzResult val).1) **
       (.x7 ↦ᵣ (clzResult val).2 >>> (63 : Nat)) ** (.x0 ↦ᵣ (0 : Word))) := by
  unfold clzResult
  -- 0. Init: ADDI x6 x0 0 (base+116 -> base+clzOff+4)
  have I := divK_clz_init_spec_within v6Old (base + clzOff)
  have Ie := cpsTripleWithin_extend_code (hmono := clz_init_sub_mod) I
  -- Frame init with x5, x7
  have Ief := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ val) ** (.x7 ↦ᵣ v7Old)) (by pcFree) Ie
  -- Stage 0: K=32, M_s=32, M_a=32 (base+120 -> base+136)
  have S0 := mod_clz_stage_combined 32 32 32 val (signExtend12 0) v7Old
    ((base + clzOff) + BitVec.ofNat 64 (4 * 1))
  dsimp only [] at S0
  have S0e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_mod 32 32 32 1
    (by decide) (by decide) (by decide)) S0
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 1) = base + clzOff + 4 from by bv_addr] at S0e
  rw [mod_clz_addr1] at S0e
  seqFrame Ief S0e
  -- Abbreviations for stage 0 results
  let v0 := if val >>> (32 : BitVec 6).toNat ≠ 0 then val else val <<< (32 : BitVec 6).toNat
  let c0 := if val >>> (32 : BitVec 6).toNat ≠ 0 then signExtend12 (0 : BitVec 12)
    else signExtend12 (0 : BitVec 12) + signExtend12 (32 : BitVec 12)
  -- Stage 1: K=48, M_s=16, M_a=16 (base+136 -> base+152)
  have S1 := mod_clz_stage_combined 48 16 16 v0 c0 (val >>> (32 : BitVec 6).toNat)
    ((base + clzOff) + BitVec.ofNat 64 (4 * 5))
  dsimp only [] at S1
  have S1e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_mod 48 16 16 5
    (by decide) (by decide) (by decide)) S1
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 5) = base + clzOff + 20 from by bv_addr] at S1e
  rw [mod_clz_addr2] at S1e
  seqFrame IefS0e S1e
  -- Stage 2: K=56, M_s=8, M_a=8 (base+152 -> base+168)
  let v1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then v0 else v0 <<< (16 : BitVec 6).toNat
  let c1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then c0 else c0 + signExtend12 (16 : BitVec 12)
  have S2 := mod_clz_stage_combined 56 8 8 v1 c1 (v0 >>> (48 : BitVec 6).toNat)
    ((base + clzOff) + BitVec.ofNat 64 (4 * 9))
  dsimp only [] at S2
  have S2e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_mod 56 8 8 9
    (by decide) (by decide) (by decide)) S2
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 9) = base + clzOff + 36 from by bv_addr] at S2e
  rw [mod_clz_addr3] at S2e
  seqFrame IefS0eS1e S2e
  -- Stage 3: K=60, M_s=4, M_a=4 (base+168 -> base+184)
  let v2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then v1 else v1 <<< (8 : BitVec 6).toNat
  let c2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then c1 else c1 + signExtend12 (8 : BitVec 12)
  have S3 := mod_clz_stage_combined 60 4 4 v2 c2 (v1 >>> (56 : BitVec 6).toNat)
    ((base + clzOff) + BitVec.ofNat 64 (4 * 13))
  dsimp only [] at S3
  have S3e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_mod 60 4 4 13
    (by decide) (by decide) (by decide)) S3
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 13) = base + clzOff + 52 from by bv_addr] at S3e
  rw [mod_clz_addr4] at S3e
  seqFrame IefS0eS1eS2e S3e
  -- Stage 4: K=62, M_s=2, M_a=2 (base+184 -> base+200)
  let v3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then v2 else v2 <<< (4 : BitVec 6).toNat
  let c3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then c2 else c2 + signExtend12 (4 : BitVec 12)
  have S4 := mod_clz_stage_combined 62 2 2 v3 c3 (v2 >>> (60 : BitVec 6).toNat)
    ((base + clzOff) + BitVec.ofNat 64 (4 * 17))
  dsimp only [] at S4
  have S4e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_mod 62 2 2 17
    (by decide) (by decide) (by decide)) S4
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 17) = base + clzOff + 68 from by bv_addr] at S4e
  rw [mod_clz_addr5] at S4e
  seqFrame IefS0eS1eS2eS3e S4e
  -- Stage 5 (last): K=63 (base+200 -> base+212)
  let v4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then v3 else v3 <<< (2 : BitVec 6).toNat
  let c4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then c3 else c3 + signExtend12 (2 : BitVec 12)
  have S5 := mod_clz_last_combined v4 c4 (v3 >>> (62 : BitVec 6).toNat)
    ((base + clzOff) + BitVec.ofNat 64 (4 * 21))
  dsimp only [] at S5
  have S5e := cpsTripleWithin_extend_code (hmono := clz_last_sub_mod 21
    (by decide) (by decide) (by decide)) S5
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 21) = base + clzOff + 84 from by bv_addr] at S5e
  rw [mod_clz_addr6] at S5e
  seqFrame IefS0eS1eS2eS3eS4e S5e
  -- Final permutation
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    IefS0eS1eS2eS3eS4eS5e

