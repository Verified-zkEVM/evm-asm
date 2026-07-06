/-
  EvmAsm.Evm64.DivMod.Compose.CLZV6

  v6 count-leading-zeros brick (24 steps, v6ClzOff → v6SetupOff) over
  `divCodeV6`. Mirror of CLZV5.lean: the clz binary-search stages are
  version-agnostic, so the same stage bodies (Compose.CLZ) extend to the v6
  code bundle via block subsumption into `divCodeV6`.

  This also installs the canonical `skipBlockV6` tactic (mirroring Base.lean's
  `skipBlock` for the v1 layout), reusable by all later v6 body sub-files.
  First brick of the v6 n=1 fast-path body. Bead `evm-asm-7wbf8.1`.
-/

import EvmAsm.Evm64.DivMod.Compose.CLZ
import EvmAsm.Evm64.DivMod.Compose.OffsetsV6

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- V6-aware skipBlock: simplifies v6 block lengths and offsets, then bv_omega
-- discharges the range disjointness. Canonical for all v6 body sub-files
-- (mirrors Base.lean's `skipBlock` for the v1 layout).
-- ============================================================================

/-- Length of the offset-parameterized v6 epilogue (independent of the JAL
    immediate). General analog of Base.lean's `divK_divEpilogue_len` (which is
    pinned to offset 24). -/
theorem divK_div_epilogue_len' (off : BitVec 21) :
    (divK_div_epilogue off).length = 10 := by
  unfold divK_div_epilogue; rfl

macro "skipBlockV6" : tactic =>
  `(tactic| apply CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
        simp only [divK_dispatchN1_length, divK_clz_len, divK_fastSetup_length,
          divK_normA_len, divK_copyAU_len, divK_fastDigit_length,
          divK_div_epilogue_len', divK_div128_v5_len,
          dispatchN1Off, v6ClzOff, v6SetupOff, v6NormAOff, v6CopyAUOff,
          v6Digit3Off, v6Digit2Off, v6Digit1Off, v6Digit0Off, v6EpilogueOff,
          v6Div128Off] at hk1 hk2
        bv_omega)))

-- ============================================================================
-- CLZ (block index 1 of divCodeV6) subsumption by divCodeV6
-- ============================================================================

/-- CLZ block instructions are subsumed by `divCodeV6` (1 skipBlock: only
    `divK_dispatchN1` precedes `divK_clz` in the v6 layout). -/
private theorem divK_clz_code_sub_divCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + v6ClzOff) divK_clz) a = some i →
      (divCodeV6 base) a = some i := by
  unfold divCodeV6; simp only [CodeReq.unionAll_cons]
  skipBlockV6
  exact CodeReq.union_mono_left

private theorem clz_stage_sub_divCodeV6 {base : Word}
    (K M_s : BitVec 6) (M_a : BitVec 12) (k : Nat)
    (hk : k + (divK_clz_stage_prog K M_s M_a).length ≤ divK_clz.length)
    (hslice : (divK_clz.drop k).take (divK_clz_stage_prog K M_s M_a).length =
      divK_clz_stage_prog K M_s M_a)
    (hbound : 4 * divK_clz.length < 2 ^ 64) :
    ∀ a i, (divK_clz_stage_code K M_s M_a ((base + v6ClzOff) + BitVec.ofNat 64 (4 * k))) a = some i →
      (divCodeV6 base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_divCodeV6 a i
    (CodeReq.ofProg_mono_sub (base + v6ClzOff) _ divK_clz _ k
      rfl hslice hk hbound a i h)

private theorem clz_last_sub_divCodeV6 {base : Word} (k : Nat)
    (hk : k + divK_clz_last_prog.length ≤ divK_clz.length)
    (hslice : (divK_clz.drop k).take divK_clz_last_prog.length = divK_clz_last_prog)
    (hbound : 4 * divK_clz.length < 2 ^ 64) :
    ∀ a i, (divK_clz_last_code ((base + v6ClzOff) + BitVec.ofNat 64 (4 * k))) a = some i →
      (divCodeV6 base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_divCodeV6 a i
    (CodeReq.ofProg_mono_sub (base + v6ClzOff) _ divK_clz _ k
      rfl hslice hk hbound a i h)

private theorem clz_init_sub_divCodeV6 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + v6ClzOff) (.ADDI .x6 .x0 0)) a = some i →
      (divCodeV6 base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_divCodeV6 a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup (base + v6ClzOff) divK_clz 0
      (by decide) (by decide)) a i (by rwa [show (base + v6ClzOff : Word) =
        base + v6ClzOff + BitVec.ofNat 64 (4 * 0) from by bv_addr] at h))

-- ============================================================================
-- Address lemmas (relative to v6ClzOff; clz exits at v6SetupOff)
-- ============================================================================

theorem clz_addr_v6_1 {base : Word} : (base + v6ClzOff + 4 : Word) + 16 = base + v6ClzOff + 20 := by bv_addr
theorem clz_addr_v6_2 {base : Word} : (base + v6ClzOff + 20 : Word) + 16 = base + v6ClzOff + 36 := by bv_addr
theorem clz_addr_v6_3 {base : Word} : (base + v6ClzOff + 36 : Word) + 16 = base + v6ClzOff + 52 := by bv_addr
theorem clz_addr_v6_4 {base : Word} : (base + v6ClzOff + 52 : Word) + 16 = base + v6ClzOff + 68 := by bv_addr
theorem clz_addr_v6_5 {base : Word} : (base + v6ClzOff + 68 : Word) + 16 = base + v6ClzOff + 84 := by bv_addr
theorem clz_addr_v6_6 {base : Word} : (base + v6ClzOff + 84 : Word) + 12 = base + v6SetupOff := by bv_addr

-- ============================================================================
-- v6 count-leading-zeros full brick, over `divCodeV6`. Mirror of
-- `divK_clz_spec_within_v5_noNop` (CLZV5.lean).
-- ============================================================================

theorem divK_clz_spec_within_v6 (val v6Old v7Old : Word) (base : Word) :
    cpsTripleWithin 24 (base + v6ClzOff) (base + v6SetupOff) (divCodeV6 base)
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ v6Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (clzResult val).2) ** (.x6 ↦ᵣ (clzResult val).1) **
       (.x7 ↦ᵣ (clzResult val).2 >>> (63 : Nat)) ** (.x0 ↦ᵣ (0 : Word))) := by
  unfold clzResult
  have I := divK_clz_init_spec_within v6Old (base + v6ClzOff)
  have Ie := cpsTripleWithin_extend_code (hmono := clz_init_sub_divCodeV6) I
  have Ief := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ val) ** (.x7 ↦ᵣ v7Old)) (by pcFree) Ie
  have S0 := divK_clz_stage_combined_within 32 32 32 val (signExtend12 0) v7Old
    ((base + v6ClzOff) + BitVec.ofNat 64 (4 * 1))
  dsimp only [] at S0
  have S0e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_divCodeV6 32 32 32 1
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
  have S1e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_divCodeV6 48 16 16 5
    (by decide) (by decide) (by decide)) S1
  rw [show (base + v6ClzOff : Word) + BitVec.ofNat 64 (4 * 5) = base + v6ClzOff + 20 from by bv_addr] at S1e
  rw [clz_addr_v6_2] at S1e
  seqFrame IefS0e S1e
  let v1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then v0 else v0 <<< (16 : BitVec 6).toNat
  let c1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then c0 else c0 + signExtend12 (16 : BitVec 12)
  have S2 := divK_clz_stage_combined_within 56 8 8 v1 c1 (v0 >>> (48 : BitVec 6).toNat)
    ((base + v6ClzOff) + BitVec.ofNat 64 (4 * 9))
  dsimp only [] at S2
  have S2e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_divCodeV6 56 8 8 9
    (by decide) (by decide) (by decide)) S2
  rw [show (base + v6ClzOff : Word) + BitVec.ofNat 64 (4 * 9) = base + v6ClzOff + 36 from by bv_addr] at S2e
  rw [clz_addr_v6_3] at S2e
  seqFrame IefS0eS1e S2e
  let v2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then v1 else v1 <<< (8 : BitVec 6).toNat
  let c2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then c1 else c1 + signExtend12 (8 : BitVec 12)
  have S3 := divK_clz_stage_combined_within 60 4 4 v2 c2 (v1 >>> (56 : BitVec 6).toNat)
    ((base + v6ClzOff) + BitVec.ofNat 64 (4 * 13))
  dsimp only [] at S3
  have S3e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_divCodeV6 60 4 4 13
    (by decide) (by decide) (by decide)) S3
  rw [show (base + v6ClzOff : Word) + BitVec.ofNat 64 (4 * 13) = base + v6ClzOff + 52 from by bv_addr] at S3e
  rw [clz_addr_v6_4] at S3e
  seqFrame IefS0eS1eS2e S3e
  let v3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then v2 else v2 <<< (4 : BitVec 6).toNat
  let c3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then c2 else c2 + signExtend12 (4 : BitVec 12)
  have S4 := divK_clz_stage_combined_within 62 2 2 v3 c3 (v2 >>> (60 : BitVec 6).toNat)
    ((base + v6ClzOff) + BitVec.ofNat 64 (4 * 17))
  dsimp only [] at S4
  have S4e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_divCodeV6 62 2 2 17
    (by decide) (by decide) (by decide)) S4
  rw [show (base + v6ClzOff : Word) + BitVec.ofNat 64 (4 * 17) = base + v6ClzOff + 68 from by bv_addr] at S4e
  rw [clz_addr_v6_5] at S4e
  seqFrame IefS0eS1eS2eS3e S4e
  let v4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then v3 else v3 <<< (2 : BitVec 6).toNat
  let c4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then c3 else c3 + signExtend12 (2 : BitVec 12)
  have S5 := divK_clz_last_combined_within v4 c4 (v3 >>> (62 : BitVec 6).toNat)
    ((base + v6ClzOff) + BitVec.ofNat 64 (4 * 21))
  dsimp only [] at S5
  have S5e := cpsTripleWithin_extend_code (hmono := clz_last_sub_divCodeV6 21
    (by decide) (by decide) (by decide)) S5
  rw [show (base + v6ClzOff : Word) + BitVec.ofNat 64 (4 * 21) = base + v6ClzOff + 84 from by bv_addr] at S5e
  rw [clz_addr_v6_6] at S5e
  seqFrame IefS0eS1eS2eS3eS4e S5e
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    IefS0eS1eS2eS3eS4eS5e

end EvmAsm.Evm64
