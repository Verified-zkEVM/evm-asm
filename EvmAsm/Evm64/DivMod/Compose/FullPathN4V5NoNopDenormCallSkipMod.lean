/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopDenormCallSkipMod

  n=4 v5 MOD call+skip denorm/epilogue: denormOff → nopOff over `modCode_noNop_v5`.
  MOD mirror of `evm_div_n4_call_skip_denorm_epilogue_spec_v5_noNop`
  (FullPathN4V5NoNopDenormCallSkip): same shared pre `preloopCallSkipPostN4V5`
  (op-agnostic loop-exit state), but the MOD denorm epilogue
  (`evm_mod_preamble_denorm_epilogue_spec_v5_noNop`, post `denormModPost`) reads out
  the un-normalized REMAINDER (the mulsub result `ms`) where DIV reads the quotient.
  The quotient output cells (sp+4088/4080/4072/4064), unread by MOD, are framed
  through.  Step of the n=4 MOD lane.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopPreloopCallSkipMod
import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5Mod

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Final post for the n=4 v5 MOD call+skip full path: the denormalized MOD
    remainder (`denormModPost` of the mulsub result `ms`) plus the residual scratch
    cells (incl. the framed, unread quotient cells).  MOD mirror of
    `fullDivN4CallSkipPostV5`. -/
def fullModN4CallSkipPostV5 (sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem : Word) : Assertion :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  let qHat := divKTrialCallV5QHat u4 u3 b3'
  let dLo := divKTrialCallV5DLo b3'
  let div_un0 := divKTrialCallV5Un0 u3
  let scratchOut := divKTrialCallV5ScratchOut u4 u3 b3' scratchMem
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  denormModPost sp shift ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + signExtend12 4088) ↦ₘ qHat) **
  ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ u4 - ms.2.2.2.2) **
  (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x9 ↦ᵣ (0 : Word) + signExtend12 4095) ** (.x11 ↦ᵣ qHat) **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ b3') **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1

/-- n=4 v5 MOD call+skip denorm/epilogue: denormOff → nopOff over `modCode_noNop_v5`. -/
theorem evm_mod_n4_call_skip_denorm_epilogue_spec_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 scratchMem : Word)
    (hshift_nz : (clzResult b3).1 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff) (modCode_noNop_v5 base)
      (preloopCallSkipPostN4V5 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)
      (fullModN4CallSkipPostV5 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) := by
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  let qHat := divKTrialCallV5QHat u4 u3 b3'
  let dLo := divKTrialCallV5DLo b3'
  let div_un0 := divKTrialCallV5Un0 u3
  let scratchOut := divKTrialCallV5ScratchOut u4 u3 b3' scratchMem
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  have hB := evm_mod_preamble_denorm_epilogue_spec_v5_noNop sp base
    ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 shift
    ms.2.2.2.1 ((0 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088) ms.2.2.2.2
    b0' b1' b2' b3'
    hshift_nz
  have hBF := cpsTripleWithin_frameR
    (((sp + signExtend12 4088) ↦ₘ qHat) **
     ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4 - ms.2.2.2.2) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x9 ↦ᵣ (0 : Word) + signExtend12 4095) ** (.x11 ↦ᵣ qHat) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ b3') **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0) **
     (sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) hB
  exact cpsTripleWithin_weaken
    (fun h hp => by
      simp only [preloopCallSkipPostN4V5, loopBodyN4CallSkipJ0PostV5,
        loopBodyN4SkipPost, loopBodySkipPost, loopExitPost,
        se12_32, se12_40, se12_48, se12_56,
        u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
        u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at hp
      xperm_hyp hp)
    (fun h hq => by
      delta fullModN4CallSkipPostV5
      simp only [denormModPost_unfold] at hq ⊢
      xperm_chunked hq)
    hBF

end EvmAsm.Evm64
