/-
  EvmAsm.Evm64.DivMod.Compose.NormAV5

  v5 normalize-A brick (21 steps, normAOff → loopSetupOff) over `divCode_noNop_v5`.
  Mirror of `divK_normA_full_spec_within_v4_noNop` (NormA.lean): the normA
  instructions don't touch div128, so the same version-agnostic instruction bodies
  are extended to the v5 code via the v5 block subsumption `sharedNoNop_v5_b5_div`.
  Second brick of the v5 n=1 preloop.  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.NormA
public import EvmAsm.Evm64.DivMod.Compose.V5NoNop

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (se12_0 se12_8 se12_16 se12_24)

/-- The normA block instructions are subsumed by `divCode_noNop_v5`. -/
private theorem divK_normA_code_sub_divCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + normAOff) (divK_normA 40)) a = some i →
      (divCode_noNop_v5 base) a = some i := by
  intro a i h
  exact sharedNoNop_v5_b5_div a i h

/-- v5 normalize-A full brick, over `divCode_noNop_v5`.  Mirror of the v4 analog. -/
theorem divK_normA_full_spec_within_v5_noNop (sp a0 a1 a2 a3 v5 v7 v10 shift antiShift : Word)
    (u0Old u1Old u2Old u3Old u4Old : Word) (base : Word) :
    cpsTripleWithin 21 (base + normAOff) (base + loopSetupOff) (divCode_noNop_v5 base)
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
    divK_normA_code_sub_divCode_noNop_v5 a i
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
    divK_normA_code_sub_divCode_noNop_v5 a i
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
    divK_normA_code_sub_divCode_noNop_v5 a i
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
    divK_normA_code_sub_divCode_noNop_v5 a i
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
    divK_normA_code_sub_divCode_noNop_v5 a i
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
    exact divK_normA_code_sub_divCode_noNop_v5 a i
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
  have hjal_clean : cpsTripleWithin 1 (base + normAOff + 80) (base + loopSetupOff) (divCode_noNop_v5 base) postAll postAll :=
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

end EvmAsm.Evm64
