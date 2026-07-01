/-
  EvmAsm.Evm64.DivMod.Compose.FastDenormEpilogueV6Mod

  MOD v6 fast-path tail: `divK_fastDenorm` ;; `divK_mod_epilogue` over `modCodeV6`,
  `base+modV6DenormOff → base+modV6ExitOff` (17 instructions).  This is the piece
  where the MOD fast path diverges from DIV: instead of DIV's single
  `divK_div_epilogue` (which stores the quotient), MOD first denormalizes the
  single-limb remainder (`divK_fastDenorm`: `u0 >>> s`, zero the high limbs) and
  then the MOD epilogue (`divK_mod_epilogue`) stores that remainder to the output
  cells `sp+32..56` and `JAL x0 1412` to the embedded v5 NOP exit.

  Brick 3 of the MOD v6 fast arm.  Mirror of `Compose/EpilogueV6.lean`
  (DIV epilogue over `divCodeV6`), specialized to the mod block offsets
  (`modV6DenormOff`/`modV6EpilogueOff`/`modV6ExitOff`), the fastDenorm block, and
  the remainder scratch cells `4056/4048/4040/4032`.
-/

import EvmAsm.Evm64.DivMod.Compose.FastDigitV6Mod
import EvmAsm.Evm64.DivMod.Compose.EpilogueV6

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Code subsumption: fastDenorm (block index 9) and mod_epilogue (block index 10)
-- into modCodeV6.
-- ============================================================================

private theorem divK_fastDenorm_code_sub_modCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + modV6DenormOff) divK_fastDenorm) a = some i →
      (modCodeV6 base) a = some i := by
  unfold modCodeV6; simp only [CodeReq.unionAll_cons]
  skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod
  skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod
  exact CodeReq.union_mono_left

private theorem divK_mod_epilogue_code_sub_modCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + modV6EpilogueOff) (divK_mod_epilogue 1412)) a = some i →
      (modCodeV6 base) a = some i := by
  unfold modCodeV6; simp only [CodeReq.unionAll_cons]
  skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod
  skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod
  exact CodeReq.union_mono_left

-- ============================================================================
-- fastDenorm over modCodeV6: base+modV6DenormOff → base+modV6EpilogueOff (7 instr).
-- ============================================================================

theorem divK_fastDenorm_spec_within_v6_mod (sp base : Word)
    (s u0 u1m u2m u3m v5 v6 : Word) :
    cpsTripleWithin 7 (base + modV6DenormOff) (base + modV6EpilogueOff) (modCodeV6 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ s) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1m) **
       ((sp + signExtend12 4040) ↦ₘ u2m) ** ((sp + signExtend12 4032) ↦ₘ u3m))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (u0 >>> (s.toNat % 64))) ** (.x6 ↦ᵣ s) **
       (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ s) **
       ((sp + signExtend12 4056) ↦ₘ (u0 >>> (s.toNat % 64))) **
       ((sp + signExtend12 4048) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4040) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4032) ↦ₘ (0 : Word))) := by
  have hden := divK_fastDenorm_spec_within sp (base + modV6DenormOff) s u0 u1m u2m u3m v5 v6
  rw [show (base + modV6DenormOff : Word) + 28 = base + modV6EpilogueOff from by bv_addr] at hden
  exact cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_fastDenorm_code_sub_modCodeV6 a i h) hden

-- ============================================================================
-- MOD epilogue over modCodeV6: base+modV6EpilogueOff → base+modV6ExitOff (10 instr).
-- Loads u[0..3] from 4056/4048/4040/4032, bumps sp, stores to sp+32..56, JAL 1412.
-- ============================================================================

theorem divK_mod_epilogue_spec_within_v6 (sp base : Word)
    (u0 u1 u2 u3 v5 v6 v7 v10 m0 m8 m16 m24 : Word) :
    cpsTripleWithin 10 (base + modV6EpilogueOff) (base + modV6ExitOff) (modCodeV6 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ u0) ** (.x6 ↦ᵣ u1) ** (.x7 ↦ᵣ u2) ** (.x10 ↦ᵣ u3) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ u0) ** ((sp + 40) ↦ₘ u1) **
       ((sp + 48) ↦ₘ u2) ** ((sp + 56) ↦ₘ u3)) := by
  have hload := divK_epilogue_load_spec_within 4056 4048 4040 4032 sp u0 u1 u2 u3 v5 v6 v7 v10
    (base + modV6EpilogueOff)
  have hloade := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_mod_epilogue_code_sub_modCodeV6 a i
      (CodeReq.ofProg_mono_sub (base + modV6EpilogueOff) (base + modV6EpilogueOff) (divK_mod_epilogue 1412)
        (divK_epilogue_load_prog 4056 4048 4040 4032) 0
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hload
  have hstore := divK_epilogue_store_spec_within sp (base + modV6EpilogueOff + 16) u0 u1 u2 u3 m0 m8 m16 m24 1412
  rw [show (base + modV6EpilogueOff + 16 : Word) + 20 + signExtend21 1412 = base + modV6ExitOff from by rv64_addr]
    at hstore
  have hstoree := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_mod_epilogue_code_sub_modCodeV6 a i
      (CodeReq.ofProg_mono_sub (base + modV6EpilogueOff) (base + modV6EpilogueOff + 16) (divK_mod_epilogue 1412)
        (divK_epilogue_store_prog 1412) 4
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hstore
  have hloadef := cpsTripleWithin_frameR
    (((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) ** ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hloade
  have hstoref := cpsTripleWithin_frameR
    (((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) hstoree
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hloadef hstoref
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12

-- ============================================================================
-- Composed MOD fast tail: fastDenorm ;; mod_epilogue.
-- base+modV6DenormOff → base+modV6ExitOff (17 instructions).
-- ============================================================================

/-- **MOD v6 fast tail.** Denormalize the single-limb remainder (`u0 >>> s`, the
    high limbs zeroed) and store it to the output cells `sp+32..56`.  Since the
    fast path only fires for single-limb divisors, the denormalized remainder is
    the single limb `u0 >>> s`. -/
theorem modK_fastDenormEpilogue_spec_within_v6 (sp base : Word)
    (s u0 u1m u2m u3m v5 v6 v7 v10 m0 m8 m16 m24 : Word) :
    cpsTripleWithin (7 + 10) (base + modV6DenormOff) (base + modV6ExitOff) (modCodeV6 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ s) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1m) **
       ((sp + signExtend12 4040) ↦ₘ u2m) ** ((sp + signExtend12 4032) ↦ₘ u3m) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ (u0 >>> (s.toNat % 64))) ** (.x6 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ s) **
       ((sp + signExtend12 4056) ↦ₘ (u0 >>> (s.toNat % 64))) **
       ((sp + signExtend12 4048) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4040) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4032) ↦ₘ (0 : Word)) **
       ((sp + 32) ↦ₘ (u0 >>> (s.toNat % 64))) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  have hden := divK_fastDenorm_spec_within_v6_mod sp base s u0 u1m u2m u3m v5 v6
  have hdenf := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
     ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
     ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hden
  have hep := divK_mod_epilogue_spec_within_v6 sp base
    (u0 >>> (s.toNat % 64)) (0 : Word) (0 : Word) (0 : Word)
    (u0 >>> (s.toNat % 64)) s v7 v10 m0 m8 m16 m24
  have hepf := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ s))
    (by pcFree) hep
  have hchain := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hdenf hepf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hchain

end EvmAsm.Evm64
