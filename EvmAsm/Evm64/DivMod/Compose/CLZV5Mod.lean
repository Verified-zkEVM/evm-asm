/-
  EvmAsm.Evm64.DivMod.Compose.CLZV5Mod

  v5 count-leading-zeros brick (24 steps, clzOff → phaseC2Off) over
  `modCode_noNop_v5`.  Mirror of `divK_clz_spec_within_v4_noNop` (CLZ.lean): the
  clz binary-search stages don't touch div128, so the same version-agnostic stage
  bodies extend to the v5 code via the v5 block subsumption `sharedNoNop_v5_b2_mod`.
  Fifth brick of the v5 n=1 preloop.  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.CLZ
public import EvmAsm.Evm64.DivMod.Compose.V5NoNop

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CLZ block instructions are subsumed by `modCode_noNop_v5`. -/
private theorem divK_clz_code_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + clzOff) divK_clz) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact sharedNoNop_v5_b2_mod a i h

private theorem clz_stage_sub_noNop_v5 {base : Word}
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

private theorem clz_last_sub_noNop_v5 {base : Word} (k : Nat)
    (hk : k + divK_clz_last_prog.length ≤ divK_clz.length)
    (hslice : (divK_clz.drop k).take divK_clz_last_prog.length = divK_clz_last_prog)
    (hbound : 4 * divK_clz.length < 2 ^ 64) :
    ∀ a i, (divK_clz_last_code ((base + clzOff) + BitVec.ofNat 64 (4 * k))) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_modCode_noNop_v5 a i
    (CodeReq.ofProg_mono_sub (base + clzOff) _ divK_clz _ k
      rfl hslice hk hbound a i h)

private theorem clz_init_sub_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + clzOff) (.ADDI .x6 .x0 0)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_modCode_noNop_v5 a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup (base + clzOff) divK_clz 0
      (by decide) (by decide)) a i (by rwa [show (base + clzOff : Word) =
        base + clzOff + BitVec.ofNat 64 (4 * 0) from by bv_addr] at h))

/-- v5 count-leading-zeros full brick, over `modCode_noNop_v5`.  Mirror of the v4
    analog. -/
theorem divK_clz_spec_within_v5_noNop_mod (val v6Old v7Old : Word) (base : Word) :
    cpsTripleWithin 24 (base + clzOff) (base + phaseC2Off) (modCode_noNop_v5 base)
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ v6Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (clzResult val).2) ** (.x6 ↦ᵣ (clzResult val).1) **
       (.x7 ↦ᵣ (clzResult val).2 >>> (63 : Nat)) ** (.x0 ↦ᵣ (0 : Word))) := by
  unfold clzResult
  have I := divK_clz_init_spec_within v6Old (base + clzOff)
  have Ie := cpsTripleWithin_extend_code (hmono := clz_init_sub_noNop_v5) I
  have Ief := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ val) ** (.x7 ↦ᵣ v7Old)) (by pcFree) Ie
  have S0 := divK_clz_stage_combined_within 32 32 32 val (signExtend12 0) v7Old
    ((base + clzOff) + BitVec.ofNat 64 (4 * 1))
  dsimp only [] at S0
  have S0e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_noNop_v5 32 32 32 1
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
  have S1e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_noNop_v5 48 16 16 5
    (by decide) (by decide) (by decide)) S1
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 5) = base + clzOff + 20 from by bv_addr] at S1e
  rw [clz_addr2] at S1e
  seqFrame IefS0e S1e
  let v1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then v0 else v0 <<< (16 : BitVec 6).toNat
  let c1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then c0 else c0 + signExtend12 (16 : BitVec 12)
  have S2 := divK_clz_stage_combined_within 56 8 8 v1 c1 (v0 >>> (48 : BitVec 6).toNat)
    ((base + clzOff) + BitVec.ofNat 64 (4 * 9))
  dsimp only [] at S2
  have S2e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_noNop_v5 56 8 8 9
    (by decide) (by decide) (by decide)) S2
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 9) = base + clzOff + 36 from by bv_addr] at S2e
  rw [clz_addr3] at S2e
  seqFrame IefS0eS1e S2e
  let v2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then v1 else v1 <<< (8 : BitVec 6).toNat
  let c2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then c1 else c1 + signExtend12 (8 : BitVec 12)
  have S3 := divK_clz_stage_combined_within 60 4 4 v2 c2 (v1 >>> (56 : BitVec 6).toNat)
    ((base + clzOff) + BitVec.ofNat 64 (4 * 13))
  dsimp only [] at S3
  have S3e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_noNop_v5 60 4 4 13
    (by decide) (by decide) (by decide)) S3
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 13) = base + clzOff + 52 from by bv_addr] at S3e
  rw [clz_addr4] at S3e
  seqFrame IefS0eS1eS2e S3e
  let v3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then v2 else v2 <<< (4 : BitVec 6).toNat
  let c3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then c2 else c2 + signExtend12 (4 : BitVec 12)
  have S4 := divK_clz_stage_combined_within 62 2 2 v3 c3 (v2 >>> (60 : BitVec 6).toNat)
    ((base + clzOff) + BitVec.ofNat 64 (4 * 17))
  dsimp only [] at S4
  have S4e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_noNop_v5 62 2 2 17
    (by decide) (by decide) (by decide)) S4
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 17) = base + clzOff + 68 from by bv_addr] at S4e
  rw [clz_addr5] at S4e
  seqFrame IefS0eS1eS2eS3e S4e
  let v4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then v3 else v3 <<< (2 : BitVec 6).toNat
  let c4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then c3 else c3 + signExtend12 (2 : BitVec 12)
  have S5 := divK_clz_last_combined_within v4 c4 (v3 >>> (62 : BitVec 6).toNat)
    ((base + clzOff) + BitVec.ofNat 64 (4 * 21))
  dsimp only [] at S5
  have S5e := cpsTripleWithin_extend_code (hmono := clz_last_sub_noNop_v5 21
    (by decide) (by decide) (by decide)) S5
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 21) = base + clzOff + 84 from by bv_addr] at S5e
  rw [clz_addr6] at S5e
  seqFrame IefS0eS1eS2eS3eS4e S5e
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    IefS0eS1eS2eS3eS4eS5e

end EvmAsm.Evm64
