/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopDenormCallAddback

  n=4 v5 call+addback-beq denorm/epilogue: denormOff → nopOff over
  `divCode_noNop_v5`.  Mirror of the v4
  `evm_div_n4_call_addback_beq_denorm_epilogue_spec_noNop` (FullPathN4Beq) and of
  the v5 call-skip denorm (FullPathN4V5NoNopDenormCallSkip), taking the addback
  loop-exit state (`preloopCallAddbackPostN4V5`, the #7594 post) to the final
  denormalized DIV output via the shared v5 denorm/epilogue.  The addback path
  feeds the corrected quotient `q_out` and the addback remainder `un*Out`.
  Bead `evm-asm-wbc4i.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopPreloopCallAddback
public import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Final post for the n=4 v5 call+addback-beq full path: the denormalized DIV
    output (with the corrected quotient `q_out`) plus the residual scratch cells. -/
def fullDivN4CallAddbackBeqPostV5 (sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem : Word) : Assertion :=
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
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
               else qHat + signExtend12 4095
  let un0Out := if carry = 0 then ab'.1 else ab.1
  let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
  let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
  let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
  let u4_out  := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
  denormDivPost sp shift un0Out un1Out un2Out un3Out q_out 0 0 0 **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ u4_out) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x9 ↦ᵣ (0 : Word) + signExtend12 4095) ** (.x11 ↦ᵣ q_out) **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ b3') **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1

/-- n=4 v5 call+addback-beq denorm/epilogue: denormOff → nopOff over `divCode_noNop_v5`. -/
theorem evm_div_n4_call_addback_beq_denorm_epilogue_spec_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 scratchMem : Word)
    (hshift_nz : (clzResult b3).1 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff) (divCode_noNop_v5 base)
      (preloopCallAddbackPostN4V5 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)
      (fullDivN4CallAddbackBeqPostV5 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) := by
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
  let c3 := ms.2.2.2.2
  let u4_new := u4 - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
               else qHat + signExtend12 4095
  let un0Out := if carry = 0 then ab'.1 else ab.1
  let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
  let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
  let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
  let u4_out  := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
  have hB := evm_div_preamble_denorm_epilogue_spec_v5_noNop sp base
    un0Out un1Out un2Out un3Out shift
    un3Out ((0 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088) c3
    q_out 0 0 0
    b0' b1' b2' b3'
    hshift_nz
  have hBF := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4_out) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x9 ↦ᵣ (0 : Word) + signExtend12 4095) ** (.x11 ↦ᵣ q_out) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ b3') **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0) **
     (sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) hB
  exact cpsTripleWithin_weaken
    (fun h hp => by
      simp only [preloopCallAddbackPostN4V5, loopBodyN4CallAddbackBeqJ0PostV5,
        loopBodyAddbackBeqPost, loopExitPost,
        se12_32, se12_40, se12_48, se12_56,
        u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
        u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at hp
      xperm_hyp hp)
    (fun h hq => by
      delta fullDivN4CallAddbackBeqPostV5
      rw [sepConj_assoc'] at hq
      xperm_hyp hq)
    hBF

end EvmAsm.Evm64
