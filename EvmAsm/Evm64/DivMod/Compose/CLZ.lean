/-
  CLZ (Count Leading Zeros) composition for DivMod.

  24 instructions at base+116, 6-stage binary search.
  Computes leading zero count in x6, shifts x5 left by that count.
-/

import EvmAsm.Evm64.DivMod.Compose.Base

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Section 9: CLZ (Count Leading Zeros) composition
-- 24 instructions at base+116, 6-stage binary search.
-- Computes leading zero count in x6, shifts x5 left by that count.
-- ============================================================================

/-- CLZ code (block 2) is subsumed by divCode. -/
private theorem divK_clz_code_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 116) divK_clz) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- Helper: CLZ stage at instruction index k is subsumed by divCode.
    The stage has 4 instructions starting at index k of divK_clz. -/
private theorem clz_stage_sub (base : Word)
    (K M_s : BitVec 6) (M_a : BitVec 12) (k : Nat)
    (hk : k + (divK_clz_stage_prog K M_s M_a).length ≤ divK_clz.length)
    (hslice : (divK_clz.drop k).take (divK_clz_stage_prog K M_s M_a).length =
      divK_clz_stage_prog K M_s M_a)
    (hbound : 4 * divK_clz.length < 2 ^ 64) :
    ∀ a i, (divK_clz_stage_code K M_s M_a ((base + 116) + BitVec.ofNat 64 (4 * k))) a = some i →
      (divCode base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_divCode base a i
    (CodeReq.ofProg_mono_sub (base + 116) _ divK_clz _ k
      rfl hslice hk hbound a i h)

/-- Helper: CLZ last stage at instruction index k is subsumed by divCode.
    The last stage has 3 instructions. -/
private theorem clz_last_sub (base : Word) (k : Nat)
    (hk : k + divK_clz_last_prog.length ≤ divK_clz.length)
    (hslice : (divK_clz.drop k).take divK_clz_last_prog.length = divK_clz_last_prog)
    (hbound : 4 * divK_clz.length < 2 ^ 64) :
    ∀ a i, (divK_clz_last_code ((base + 116) + BitVec.ofNat 64 (4 * k))) a = some i →
      (divCode base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_divCode base a i
    (CodeReq.ofProg_mono_sub (base + 116) _ divK_clz _ k
      rfl hslice hk hbound a i h)

/-- Helper: CLZ init singleton (ADDI x6 x0 0 at base+116) is subsumed by divCode. -/
private theorem clz_init_sub (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 116) (.ADDI .x6 .x0 0)) a = some i →
      (divCode base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_divCode base a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup (base + 116) divK_clz 0
      (by native_decide) (by native_decide)) a i (by rwa [show (base + 116 : Word) =
        base + 116 + BitVec.ofNat 64 (4 * 0) from by bv_addr] at h))

-- CLZ stage parameters: (SRLI_K, SLLI_M_s, ADDI_M_a, instruction_index)
-- Stage 0: K=32, M_s=32, M_a=32, index 1 (after init at index 0)
-- Stage 1: K=48, M_s=16, M_a=16, index 5
-- Stage 2: K=56, M_s=8,  M_a=8,  index 9
-- Stage 3: K=60, M_s=4,  M_a=4,  index 13
-- Stage 4: K=62, M_s=2,  M_a=2,  index 17
-- Stage 5 (last): K=63, M_a=1,   index 21

/-- CLZ result function: compute (count, shifted_val) from a 6-stage binary search. -/
noncomputable def clzResult (val : Word) : Word × Word :=
  -- Stage 0: check top 32 bits
  let v0 := if val >>> (32 : BitVec 6).toNat ≠ 0 then val else val <<< (32 : BitVec 6).toNat
  let c0 := if val >>> (32 : BitVec 6).toNat ≠ 0 then signExtend12 (0 : BitVec 12)
    else signExtend12 (0 : BitVec 12) + signExtend12 (32 : BitVec 12)
  -- Stage 1: check bits 48..63 of current value
  let v1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then v0 else v0 <<< (16 : BitVec 6).toNat
  let c1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then c0 else c0 + signExtend12 (16 : BitVec 12)
  -- Stage 2: check bits 56..63
  let v2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then v1 else v1 <<< (8 : BitVec 6).toNat
  let c2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then c1 else c1 + signExtend12 (8 : BitVec 12)
  -- Stage 3: check bits 60..63
  let v3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then v2 else v2 <<< (4 : BitVec 6).toNat
  let c3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then c2 else c2 + signExtend12 (4 : BitVec 12)
  -- Stage 4: check bits 62..63
  let v4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then v3 else v3 <<< (2 : BitVec 6).toNat
  let c4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then c3 else c3 + signExtend12 (2 : BitVec 12)
  -- Stage 5 (last): check bit 63
  let c5 := if v4 >>> (63 : Nat) ≠ 0 then c4 else c4 + signExtend12 (1 : BitVec 12)
  (c5, v4)

-- Address lemmas for CLZ stages
private theorem clz_addr0 (base : Word) : (base + 116 : Word) + 4 = base + 120 := by bv_addr
private theorem clz_addr1 (base : Word) : (base + 120 : Word) + 16 = base + 136 := by bv_addr
private theorem clz_addr2 (base : Word) : (base + 136 : Word) + 16 = base + 152 := by bv_addr
private theorem clz_addr3 (base : Word) : (base + 152 : Word) + 16 = base + 168 := by bv_addr
private theorem clz_addr4 (base : Word) : (base + 168 : Word) + 16 = base + 184 := by bv_addr
private theorem clz_addr5 (base : Word) : (base + 184 : Word) + 16 = base + 200 := by bv_addr
private theorem clz_addr6 (base : Word) : (base + 200 : Word) + 12 = base + 212 := by bv_addr

/-- Combined CLZ stage: handles both taken and ntaken with conditional postcondition.
    After stage: val' = if (val>>>K≠0) then val else val<<<M_s,
    count' = if (val>>>K≠0) then count else count+M_a. -/
private theorem divK_clz_stage_combined
    (K M_s : BitVec 6) (M_a : BitVec 12) (val count v7 : Word) (base : Word) :
    let cr := divK_clz_stage_code K M_s M_a base
    let val' := if val >>> K.toNat ≠ 0 then val else val <<< M_s.toNat
    let count' := if val >>> K.toNat ≠ 0 then count else count + signExtend12 M_a
    cpsTriple base (base + 16) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val') ** (.x6 ↦ᵣ count') **
       (.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro cr; dsimp only []
  by_cases h : val >>> K.toNat ≠ 0
  · simp only [if_pos h]
    exact divK_clz_stage_taken_spec K M_s M_a val count v7 base h
  · push_neg at h
    simp only [if_neg (show ¬(val >>> K.toNat ≠ 0) from not_not.mpr h)]
    have hs := divK_clz_stage_ntaken_spec K M_s M_a val count v7 base h
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun _ hp => by rw [show (val >>> K.toNat : Word) = 0 from h]; exact hp) hs

/-- Combined CLZ last stage: handles both taken and ntaken. -/
private theorem divK_clz_last_combined (val count v7 : Word) (base : Word) :
    let cr := divK_clz_last_code base
    let count' := if val >>> (63 : Nat) ≠ 0 then count else count + signExtend12 (1 : BitVec 12)
    cpsTriple base (base + 12) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count') **
       (.x7 ↦ᵣ (val >>> (63 : Nat))) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro cr; dsimp only []
  by_cases h : val >>> (63 : Nat) ≠ 0
  · simp only [if_pos h]
    exact divK_clz_last_taken_spec val count v7 base h
  · push_neg at h
    simp only [if_neg (show ¬(val >>> (63 : Nat) ≠ 0) from not_not.mpr h)]
    have hs := divK_clz_last_ntaken_spec val count v7 base h
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun _ hp => by rw [show (val >>> (63 : Nat) : Word) = 0 from h]; exact hp) hs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Full CLZ composition: 24 instructions at base+116→base+212.
    Computes count of leading zeros in x6, shifts x5 left by that count.
    Entry: base+116 with x5=val, x6=v6_old, x7=v7_old, x0=0.
    Exit: base+212 with x5=(clzResult val).2, x6=(clzResult val).1, x0=0. -/
theorem divK_clz_spec (val v6_old v7_old : Word) (base : Word) :
    cpsTriple (base + 116) (base + 212) (divCode base)
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ v6_old) ** (.x7 ↦ᵣ v7_old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (clzResult val).2) ** (.x6 ↦ᵣ (clzResult val).1) **
       (.x7 ↦ᵣ (clzResult val).2 >>> (63 : Nat)) ** (.x0 ↦ᵣ (0 : Word))) := by
  unfold clzResult
  -- 0. Init: ADDI x6 x0 0 (base+116 → base+120)
  have I := divK_clz_init_spec v6_old (base + 116)
  have Ie := cpsTriple_extend_code (hmono := clz_init_sub base) I
  rw [clz_addr0] at Ie
  -- Frame init with x5, x7
  have Ief := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ val) ** (.x7 ↦ᵣ v7_old)) (by pcFree) Ie
  -- Stage 0: K=32, M_s=32, M_a=32 (base+120 → base+136)
  have S0 := divK_clz_stage_combined 32 32 32 val (signExtend12 0) v7_old
    ((base + 116) + BitVec.ofNat 64 (4 * 1))
  dsimp only [] at S0
  have S0e := cpsTriple_extend_code (hmono := clz_stage_sub base 32 32 32 1
    (by native_decide) (by native_decide) (by native_decide)) S0
  rw [show (base + 116 : Word) + BitVec.ofNat 64 (4 * 1) = base + 120 from by bv_addr] at S0e
  rw [clz_addr1] at S0e
  seqFrame Ief S0e
  -- Abbreviations for stage 0 results
  let v0 := if val >>> (32 : BitVec 6).toNat ≠ 0 then val else val <<< (32 : BitVec 6).toNat
  let c0 := if val >>> (32 : BitVec 6).toNat ≠ 0 then signExtend12 (0 : BitVec 12)
    else signExtend12 (0 : BitVec 12) + signExtend12 (32 : BitVec 12)
  -- Stage 1: K=48, M_s=16, M_a=16 (base+136 → base+152)
  have S1 := divK_clz_stage_combined 48 16 16 v0 c0 (val >>> (32 : BitVec 6).toNat)
    ((base + 116) + BitVec.ofNat 64 (4 * 5))
  dsimp only [] at S1
  have S1e := cpsTriple_extend_code (hmono := clz_stage_sub base 48 16 16 5
    (by native_decide) (by native_decide) (by native_decide)) S1
  rw [show (base + 116 : Word) + BitVec.ofNat 64 (4 * 5) = base + 136 from by bv_addr] at S1e
  rw [clz_addr2] at S1e
  seqFrame IefS0e S1e
  -- Stage 2: K=56, M_s=8, M_a=8 (base+152 → base+168)
  let v1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then v0 else v0 <<< (16 : BitVec 6).toNat
  let c1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then c0 else c0 + signExtend12 (16 : BitVec 12)
  have S2 := divK_clz_stage_combined 56 8 8 v1 c1 (v0 >>> (48 : BitVec 6).toNat)
    ((base + 116) + BitVec.ofNat 64 (4 * 9))
  dsimp only [] at S2
  have S2e := cpsTriple_extend_code (hmono := clz_stage_sub base 56 8 8 9
    (by native_decide) (by native_decide) (by native_decide)) S2
  rw [show (base + 116 : Word) + BitVec.ofNat 64 (4 * 9) = base + 152 from by bv_addr] at S2e
  rw [clz_addr3] at S2e
  seqFrame IefS0eS1e S2e
  -- Stage 3: K=60, M_s=4, M_a=4 (base+168 → base+184)
  let v2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then v1 else v1 <<< (8 : BitVec 6).toNat
  let c2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then c1 else c1 + signExtend12 (8 : BitVec 12)
  have S3 := divK_clz_stage_combined 60 4 4 v2 c2 (v1 >>> (56 : BitVec 6).toNat)
    ((base + 116) + BitVec.ofNat 64 (4 * 13))
  dsimp only [] at S3
  have S3e := cpsTriple_extend_code (hmono := clz_stage_sub base 60 4 4 13
    (by native_decide) (by native_decide) (by native_decide)) S3
  rw [show (base + 116 : Word) + BitVec.ofNat 64 (4 * 13) = base + 168 from by bv_addr] at S3e
  rw [clz_addr4] at S3e
  seqFrame IefS0eS1eS2e S3e
  -- Stage 4: K=62, M_s=2, M_a=2 (base+184 → base+200)
  let v3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then v2 else v2 <<< (4 : BitVec 6).toNat
  let c3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then c2 else c2 + signExtend12 (4 : BitVec 12)
  have S4 := divK_clz_stage_combined 62 2 2 v3 c3 (v2 >>> (60 : BitVec 6).toNat)
    ((base + 116) + BitVec.ofNat 64 (4 * 17))
  dsimp only [] at S4
  have S4e := cpsTriple_extend_code (hmono := clz_stage_sub base 62 2 2 17
    (by native_decide) (by native_decide) (by native_decide)) S4
  rw [show (base + 116 : Word) + BitVec.ofNat 64 (4 * 17) = base + 184 from by bv_addr] at S4e
  rw [clz_addr5] at S4e
  seqFrame IefS0eS1eS2eS3e S4e
  -- Stage 5 (last): K=63 (base+200 → base+212)
  let v4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then v3 else v3 <<< (2 : BitVec 6).toNat
  let c4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then c3 else c3 + signExtend12 (2 : BitVec 12)
  have S5 := divK_clz_last_combined v4 c4 (v3 >>> (62 : BitVec 6).toNat)
    ((base + 116) + BitVec.ofNat 64 (4 * 21))
  dsimp only [] at S5
  have S5e := cpsTriple_extend_code (hmono := clz_last_sub base 21
    (by native_decide) (by native_decide) (by native_decide)) S5
  rw [show (base + 116 : Word) + BitVec.ofNat 64 (4 * 21) = base + 200 from by bv_addr] at S5e
  rw [clz_addr6] at S5e
  seqFrame IefS0eS1eS2eS3eS4e S5e
  -- Final permutation
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    IefS0eS1eS2eS3eS4eS5e

end EvmAsm.Rv64
