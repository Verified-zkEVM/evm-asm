/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5Shift0PostBridge

  The n=4 v5 shift=0 lane post-bridge (generic, structural): from the n=4 shift=0
  full-path output (the shift=0 DIV epilogue post — a single-limb quotient `qVal`
  copied into the `sp+32..56` output slots, plus the loop registers and the
  residual scratch frame) to `divStackDispatchPost sp a b ** memOwn (sp+3936)`,
  GIVEN the quotient-correctness facts `(a/b).getLimbN k = qVal/0`.  Since the n=4
  divisor is full and `a < 2^256`, the quotient `a/b < 2^64` is single-limb, so
  `q1 = q2 = q3 = 0`.  Generic mirror of `n4_denormDivPost_frame_to_divStackDispatchPost_v5`
  (#7601) for the shift=0 epilogue post (where the quotient already sits in the
  output slots, no denormalization).  Both shift=0 call branches (skip/addback)
  instantiate it with their `qVal`/scratch.  Bead `evm-asm-wbc4i.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.Dispatcher

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- Generic structural post-bridge for the n=4 v5 shift=0 call paths: the shift=0
    epilogue output (single-limb quotient `qVal` in the `sp+32..56` output slots)
    plus the residual scratch frame implies `divStackDispatchPost sp a b **
    memOwn (sp+3936)`, given that the stored quotient matches `EvmWord.div a b`. -/
theorem n4_shift0_post_to_divStackDispatchPost_v5
    (sp : Word) (a b : EvmWord)
    (a0 a1 a2 a3 : Word)
    (qVal un3OutV v9Val un0V un1V un2V u4V shiftV : Word)
    (retMemV dMemV dloMemV scratchUn0V scratchOutV : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 = qVal)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 = 0)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = 0)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = 0) :
    ∀ h,
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ qVal) ** (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
       (.x2 ↦ᵣ un3OutV) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shiftV) **
       ((sp + signExtend12 4088) ↦ₘ qVal) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + 32) ↦ₘ qVal) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
       (.x9 ↦ᵣ v9Val) ** (.x11 ↦ᵣ qVal) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ un0V) ** ((sp + signExtend12 4048) ↦ₘ un1V) **
       ((sp + signExtend12 4040) ↦ₘ un2V) ** ((sp + signExtend12 4032) ↦ₘ un3OutV) **
       ((sp + signExtend12 4024) ↦ₘ u4V) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ (4 : Word)) ** ((sp + signExtend12 3976) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3968) ↦ₘ retMemV) ** ((sp + signExtend12 3960) ↦ₘ dMemV) **
       ((sp + signExtend12 3952) ↦ₘ dloMemV) ** ((sp + signExtend12 3944) ↦ₘ scratchUn0V) **
       ((sp + signExtend12 3936) ↦ₘ scratchOutV) ** regOwn .x1) h →
      (divStackDispatchPost sp a b ** memOwn (sp + signExtend12 3936)) h := by
  intro h hp
  rw [word_add_zero] at hp
  apply sepConj_mono_right (P := divStackDispatchPost sp a b) memIs_implies_memOwn h
  apply sepConj_mono_left (divStackDispatchPost_weaken sp a b) h
  rw [evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _ hdiv0 hdiv1 hdiv2 hdiv3,
      divScratchValuesCall_unfold, divScratchValues_unfold]
  xperm_hyp hp

end EvmAsm.Evm64
