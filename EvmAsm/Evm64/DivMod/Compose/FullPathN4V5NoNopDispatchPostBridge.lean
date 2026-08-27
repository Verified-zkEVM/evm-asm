/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopDispatchPostBridge

  The n=4 v5 lane post-bridge (generic, structural): from the n=4 full-path
  denorm output (a `denormDivPost` with a single-limb quotient `qVal` + the n=4
  residual scratch frame) to `divStackDispatchPost sp a b ** memOwn (sp+3936)`,
  GIVEN the quotient-correctness facts `(a / b).getLimbN k = qVal/0`.  Since the
  n=4 divisor is full (b3 ≠ 0 ⟹ b ≥ 2^192) and a < 2^256, the quotient a/b < 2^64
  is single-limb, so `q1 = q2 = q3 = 0`.  The actual derivation of the `hdiv`
  facts (Knuth-D quotient correctness via the U4=0 semantic) is supplied by the
  lane; this bridge is the structural plumbing, a generic mirror of
  `n1_denormPost_to_divStackDispatchPost_v5` (FullPathN1V5Full).  Both n=4 call
  branches (skip/addback) instantiate it with their `qVal`/remainder/scratch.
  Bead `evm-asm-wbc4i.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Full

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- Generic structural post-bridge for the n=4 v5 call paths: the denorm output
    (single-limb quotient `qVal`) plus the residual scratch frame implies
    `divStackDispatchPost sp a b ** memOwn (sp+3936)`, given that the stored
    quotient matches `EvmWord.div a b`. -/
theorem n4_denormDivPost_frame_to_divStackDispatchPost_v5
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 : Word)
    (shift qVal rem0 rem1 rem2 rem3 u4f x9Val dMemV dloMemV scratchUn0V scratchOutV : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 = qVal)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 = 0)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = 0)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = 0) :
    ∀ h,
      (denormDivPost sp shift rem0 rem1 rem2 rem3 qVal 0 0 0 **
       ((sp + signExtend12 3992) ↦ₘ shift) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ u4f) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
       (.x9 ↦ᵣ x9Val) ** (.x11 ↦ᵣ qVal) **
       (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
       (sp + signExtend12 3960 ↦ₘ dMemV) **
       (sp + signExtend12 3952 ↦ₘ dloMemV) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0V) **
       (sp + signExtend12 3936 ↦ₘ scratchOutV) ** regOwn .x1) h →
      (divStackDispatchPost sp a b ** memOwn (sp + signExtend12 3936)) h := by
  intro h hp
  delta denormDivPost at hp
  rw [word_add_zero] at hp
  apply sepConj_mono_right (P := divStackDispatchPost sp a b) memIs_implies_memOwn h
  apply sepConj_mono_left (divStackDispatchPost_weaken sp a b) h
  rw [evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _ hdiv0 hdiv1 hdiv2 hdiv3,
      divScratchValuesCall_unfold, divScratchValues_unfold]
  xperm_hyp hp

end EvmAsm.Evm64
