/-
  EvmAsm.Evm64.DivMod.Compose.NormAV6

  v6 normalize-phase bricks over `divCodeV6`: the full NormA block (21 instrs,
  s>0) and the full CopyAU block (9 instrs, s=0). Both converge at
  `base + v6Digit3Off` (NormA via its trailing `JAL x0 40` that skips CopyAU;
  CopyAU by fall-through). Mirror of `Compose/NormA.lean` over the v1 layout:
  the programs (`divK_normA 40`, `divK_copyAU`) are identical, so only the code
  bundle, base offsets, and JAL target differ. `normAFullPost` (Compose/Base) is
  reused verbatim since it is state-only.

  Second brick of the v6 n=1 fast-path body. Bead `evm-asm-7wbf8.2`.
-/

import EvmAsm.Evm64.DivMod.Compose.NormA
import EvmAsm.Evm64.DivMod.Compose.CLZV6

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- signExtend12 rewrites pulled from the divmod_addr global set (AddrNorm.lean).
open EvmAsm.Evm64.DivMod.AddrNorm (se12_0 se12_8 se12_16 se12_24)
-- signExtend13/21 rewrites pulled from the rv64_addr global set (Rv64/AddrNorm.lean).
open EvmAsm.Rv64.AddrNorm (bv64_4mul_3)

-- ============================================================================
-- Code subsumption into divCodeV6
-- ============================================================================

/-- NormA code (block index 3 of divCodeV6) is subsumed by divCodeV6. -/
private theorem divK_normA_code_sub_divCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + v6NormAOff) (divK_normA 40)) a = some i →
      (divCodeV6 base) a = some i := by
  unfold divCodeV6; simp only [CodeReq.unionAll_cons]
  skipBlockV6; skipBlockV6; skipBlockV6
  exact CodeReq.union_mono_left

/-- CopyAU code (block index 4 of divCodeV6) is subsumed by divCodeV6. -/
private theorem divK_copyAU_code_sub_divCodeV6 {base : Word} :
    ∀ a i, (divK_copyAU_code (base + v6CopyAUOff)) a = some i →
      (divCodeV6 base) a = some i := by
  unfold divCodeV6 divK_copyAU_code; simp only [CodeReq.unionAll_cons]
  skipBlockV6; skipBlockV6; skipBlockV6; skipBlockV6
  exact CodeReq.union_mono_left

-- ============================================================================
-- Full NormA: normalize dividend a[0..3] → u[0..4] and jump over CopyAU.
-- base+v6NormAOff → base+v6Digit3Off (21 instructions including JAL).
-- ============================================================================

theorem divK_normA_full_spec_within_v6 (sp a0 a1 a2 a3 v5 v7 v10 shift antiShift : Word)
    (u0Old u1Old u2Old u3Old u4Old : Word) (base : Word) :
    cpsTripleWithin 21 (base + v6NormAOff) (base + v6Digit3Off) (divCodeV6 base)
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
  -- Top: LD a[3], SRL→u[4], SD u[4]
  have htop := divK_normA_top_spec_within 24 4024 sp a3 v5 v7 antiShift u4Old (base + v6NormAOff)
  simp only [se12_24] at htop
  have htope := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_divCodeV6 a i
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
  -- MergeA 1: u[3] = (a[3]<<<shift) | (a[2]>>>anti)
  have hma1 := divK_normA_mergeA_spec_within 16 4032 sp a3 a2 u4 v10 shift antiShift u3Old (base + v6NormAOff + 12)
  simp only [se12_16] at hma1
  rw [show (base + v6NormAOff + 12 : Word) + 20 = base + v6NormAOff + 32 from by bv_addr] at hma1
  have hma1e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_divCodeV6 a i
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
  -- MergeB: u[2] = (a[2]<<<shift) | (a[1]>>>anti)
  have hmb := divK_normA_mergeB_spec_within 8 4040 sp a2 a1 u3 (a2 >>> (antiShift.toNat % 64))
    shift antiShift u2Old (base + v6NormAOff + 32)
  simp only [se12_8] at hmb
  rw [show (base + v6NormAOff + 32 : Word) + 20 = base + v6NormAOff + 52 from by bv_addr] at hmb
  have hmbe := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_divCodeV6 a i
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
  -- MergeA 2: u[1] = (a[1]<<<shift) | (a[0]>>>anti)
  have hma2 := divK_normA_mergeA_spec_within 0 4048 sp a1 a0 u2 (a1 >>> (antiShift.toNat % 64))
    shift antiShift u1Old (base + v6NormAOff + 52)
  simp only [se12_0] at hma2
  rw [show (base + v6NormAOff + 52 : Word) + 20 = base + v6NormAOff + 72 from by bv_addr] at hma2
  have hma2e := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_divCodeV6 a i
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
  -- Last: u[0] = a[0]<<<shift
  have hlast := divK_normA_last_spec_within 4056 sp a0 shift u0Old (base + v6NormAOff + 72)
  rw [show (base + v6NormAOff + 72 : Word) + 8 = base + v6NormAOff + 80 from by bv_addr] at hlast
  have hlaste := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_divCodeV6 a i
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
  -- JAL x0 40 at base+v6NormAOff+80 → base+v6Digit3Off (skips CopyAU)
  have hjal := jal_x0_spec_gen_within 40 (base + v6NormAOff + 80)
  rw [show (base + v6NormAOff + 80 : Word) + signExtend21 40 = base + v6Digit3Off from by rv64_addr] at hjal
  have hjale := cpsTripleWithin_extend_code (hmono := by
    intro a i h
    exact divK_normA_code_sub_divCodeV6 a i
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
  have hjal_clean : cpsTripleWithin 1 (base + v6NormAOff + 80) (base + v6Digit3Off) (divCodeV6 base) postAll postAll :=
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
-- Full CopyAU: copy a[0..3] to u[0..3], set u[4]=0 (s=0 path).
-- base+v6CopyAUOff → base+v6Digit3Off (9 instructions, fall-through).
-- ============================================================================

theorem divK_copyAU_full_spec_within_v6 (sp : Word)
    (a0 a1 a2 a3 : Word) (u0 u1 u2 u3 u4 v5 : Word) (base : Word) :
    cpsTripleWithin 9 (base + v6CopyAUOff) (base + v6Digit3Off) (divCodeV6 base)
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
  exact cpsTripleWithin_extend_code divK_copyAU_code_sub_divCodeV6 hcopy

end EvmAsm.Evm64
