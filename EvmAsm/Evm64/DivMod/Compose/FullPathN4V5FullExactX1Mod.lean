/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5FullExactX1Mod

  MOD mirror of `FullPathN4V5FullExactX1` (call-skip, shift≠0 branch): the x1-preserving
  n=4 v5 MOD denorm/epilogue + full-path composition (`base → nopOff` over
  `modCode_noNop_v5`), with the concrete caller `x1` (= `raVal`) framed through
  instead of `regOwn .x1`.  The output post lands `denormModPost` (remainder limbs)
  instead of `denormDivPost`.  Toward `evm_mod_callable_v5` / SMOD `.proven`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5PreloopExactX1Mod
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopDenormCallSkipMod
import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5Mod

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- `fullModN4CallSkipPostV5` minus the `regOwn .x1` atom. -/
def fullModN4CallSkipPostV5NoX1 (sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem : Word) : Assertion :=
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
  (sp + signExtend12 3936 ↦ₘ scratchOut)

/-- Exact-x1 twin of `evm_mod_n4_call_skip_denorm_epilogue_spec_v5_noNop`. -/
theorem evm_mod_n4_call_skip_denorm_epilogue_spec_v5_noNop_exact_x1 (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 scratchMem raVal : Word)
    (hshift_nz : (clzResult b3).1 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff) (modCode_noNop_v5 base)
      (preloopCallSkipPostN4V5NoX1 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem **
       (.x1 ↦ᵣ raVal))
      (fullModN4CallSkipPostV5NoX1 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
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
     (sp + signExtend12 3936 ↦ₘ scratchOut) ** (.x1 ↦ᵣ raVal))
    (by pcFree) hB
  exact cpsTripleWithin_weaken
    (fun h hp => by
      simp only [preloopCallSkipPostN4V5NoX1, loopBodyN4CallSkipJ0PostV5NoX1,
        loopBodyN4SkipPost, loopBodySkipPost, loopExitPost,
        se12_32, se12_40, se12_48, se12_56,
        u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
        u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at hp
      xperm_hyp hp)
    (fun h hq => by
      delta fullModN4CallSkipPostV5NoX1
      simp only [denormModPost_unfold] at hq ⊢
      xperm_chunked hq)
    hBF

/-- Exact-x1 twin of `evm_mod_n4_full_call_skip_spec_v5_noNop` (shift ≠ 0). -/
theorem evm_mod_n4_full_call_skip_spec_v5_noNop_exact_x1 (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old raVal x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4 a3 b2 b3)
    (hborrow : isSkipBorrowN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 158 + (2 + 23 + 10))
      base (base + nopOff) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ x2In) **
       (.x9 ↦ᵣ x9In) **
       (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) ** (.x1 ↦ᵣ raVal))
      (fullModN4CallSkipPostV5NoX1 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  have hA := evm_mod_n4_preloop_call_skip_spec_v5_noNop_exact_x1 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old raVal x9In x2In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow
  have hB := evm_mod_n4_call_skip_denorm_epilogue_spec_v5_noNop_exact_x1 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 scratchMem raVal hshift_nz
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hA hB
  exact cpsTripleWithin_mono_nSteps (by decide) hFull

/-- `fullModN4CallAddbackPostV5` minus the `regOwn .x1` atom. -/
def fullModN4CallAddbackPostV5NoX1 (sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem : Word) : Assertion :=
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
  denormModPost sp shift un0Out un1Out un2Out un3Out **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + signExtend12 4088) ↦ₘ q_out) **
  ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
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
  (sp + signExtend12 3936 ↦ₘ scratchOut)

/-- Exact-x1 twin of `evm_mod_n4_call_addback_denorm_epilogue_spec_v5_noNop`. -/
theorem evm_mod_n4_call_addback_denorm_epilogue_spec_v5_noNop_exact_x1 (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 scratchMem raVal : Word)
    (hshift_nz : (clzResult b3).1 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff) (modCode_noNop_v5 base)
      (preloopCallAddbackPostN4V5NoX1 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem **
       (.x1 ↦ᵣ raVal))
      (fullModN4CallAddbackPostV5NoX1 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
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
  have hB := evm_mod_preamble_denorm_epilogue_spec_v5_noNop sp base
    un0Out un1Out un2Out un3Out shift
    un3Out ((0 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088) c3
    b0' b1' b2' b3'
    hshift_nz
  have hBF := cpsTripleWithin_frameR
    (((sp + signExtend12 4088) ↦ₘ q_out) **
     ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
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
     (sp + signExtend12 3936 ↦ₘ scratchOut) ** (.x1 ↦ᵣ raVal))
    (by pcFree) hB
  exact cpsTripleWithin_weaken
    (fun h hp => by
      simp only [preloopCallAddbackPostN4V5NoX1, loopBodyN4CallAddbackBeqJ0PostV5NoX1,
        loopBodyAddbackBeqPost, loopExitPost,
        se12_32, se12_40, se12_48, se12_56,
        u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
        u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at hp
      xperm_hyp hp)
    (fun h hq => by
      delta fullModN4CallAddbackPostV5NoX1
      simp only [denormModPost_unfold] at hq ⊢
      xperm_chunked hq)
    hBF

/-- Exact-x1 twin of `evm_mod_n4_full_call_addback_spec_v5_noNop` (shift ≠ 0). -/
theorem evm_mod_n4_full_call_addback_spec_v5_noNop_exact_x1 (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old raVal x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4 a3 b2 b3)
    (hborrow : isAddbackBorrowN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2_nz : isAddbackCarry2NzN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 234 + (2 + 23 + 10))
      base (base + nopOff) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ x2In) **
       (.x9 ↦ᵣ x9In) **
       (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) ** (.x1 ↦ᵣ raVal))
      (fullModN4CallAddbackPostV5NoX1 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  have hA := evm_mod_n4_preloop_call_addback_spec_v5_noNop_exact_x1 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old raVal x9In x2In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow hcarry2_nz
  have hB := evm_mod_n4_call_addback_denorm_epilogue_spec_v5_noNop_exact_x1 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 scratchMem raVal hshift_nz
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hA hB
  exact cpsTripleWithin_mono_nSteps (by decide) hFull

/-- `fullModN4CallSkipShift0PostV5` minus the `regOwn .x1` atom. -/
def fullModN4CallSkipShift0PostV5NoX1 (sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem : Word) : Assertion :=
  let qHat := divKTrialCallV5QHat (0 : Word) a3 b3
  let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
  let dLo := divKTrialCallV5DLo b3
  let divUn0 := divKTrialCallV5Un0 a3
  let scratchOut := divKTrialCallV5ScratchOut (0 : Word) a3 b3 scratchMem
  (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ ms.1) ** (.x6 ↦ᵣ ms.2.1) ** (.x7 ↦ᵣ ms.2.2.1) **
  (.x2 ↦ᵣ ms.2.2.2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ms.2.2.2.1) **
  ((sp + signExtend12 3992) ↦ₘ (clzResult b3).1) **
  ((sp + signExtend12 4056) ↦ₘ ms.1) ** ((sp + signExtend12 4048) ↦ₘ ms.2.1) **
  ((sp + signExtend12 4040) ↦ₘ ms.2.2.1) ** ((sp + signExtend12 4032) ↦ₘ ms.2.2.2.1) **
  ((sp + 32) ↦ₘ ms.1) ** ((sp + 40) ↦ₘ ms.2.1) **
  ((sp + 48) ↦ₘ ms.2.2.1) ** ((sp + 56) ↦ₘ ms.2.2.2.1) **
  (.x9 ↦ᵣ (0 : Word) + signExtend12 4095) ** (.x11 ↦ᵣ qHat) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4088) ↦ₘ qHat) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4024) ↦ₘ ((0 : Word) - ms.2.2.2.2)) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 3984) ↦ₘ (4 : Word)) ** ((sp + signExtend12 3976) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 3968) ↦ₘ (base + div128CallRetOff)) ** ((sp + signExtend12 3960) ↦ₘ b3) **
  ((sp + signExtend12 3952) ↦ₘ dLo) ** ((sp + signExtend12 3944) ↦ₘ divUn0) **
  ((sp + signExtend12 3936) ↦ₘ scratchOut)

/-- Exact-x1 twin of `evm_mod_n4_full_call_skip_shift0_spec_v5_noNop`. -/
theorem evm_mod_n4_full_call_skip_shift0_spec_v5_noNop_exact_x1 (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v2 v5 v6 v7 v10 v11Old raVal x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_z : (clzResult b3).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3 (0 : Word)) :
    cpsTripleWithin ((((8 + 21 + 24 + 4) + 13) + 158) + 12) base (base + nopOff) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) **
       (.x9 ↦ᵣ x9In) **
       (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) ** (.x1 ↦ᵣ raVal))
      (fullModN4CallSkipShift0PostV5NoX1 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  have hA := evm_mod_n4_preloop_call_skip_shift0_spec_v5_noNop_exact_x1 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v2 v5 v6 v7 v10 v11Old raVal x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem hbnz hb3nz hshift_z halign hborrow
  have hB := evm_mod_shift0_epilogue_spec_v5_noNop sp base
    (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).1
    (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.1
    (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
    (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1
    (clzResult b3).1
    (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1
    ((0 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088)
    (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2
    b0 b1 b2 b3 hshift_z
  have hBf := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ (0 : Word) + signExtend12 4095) ** (.x11 ↦ᵣ divKTrialCallV5QHat (0 : Word) a3 b3) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4088) ↦ₘ divKTrialCallV5QHat (0 : Word) a3 b3) **
     ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4024) ↦ₘ ((0 : Word) - (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ (4 : Word)) ** ((sp + signExtend12 3976) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3968) ↦ₘ (base + div128CallRetOff)) ** ((sp + signExtend12 3960) ↦ₘ b3) **
     ((sp + signExtend12 3952) ↦ₘ divKTrialCallV5DLo b3) **
     ((sp + signExtend12 3944) ↦ₘ divKTrialCallV5Un0 a3) **
     ((sp + signExtend12 3936) ↦ₘ divKTrialCallV5ScratchOut (0 : Word) a3 b3 scratchMem) ** (.x1 ↦ᵣ raVal))
    (by pcFree) hB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      simp only [preloopCallSkipShift0PostN4V5NoX1, loopBodyN4CallSkipJ0PostV5NoX1,
        loopBodyN4SkipPost, loopBodySkipPost, loopExitPost,
        se12_32, se12_40, se12_48, se12_56,
        u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
        u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at hp
      xperm_hyp hp) hA hBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta fullModN4CallSkipShift0PostV5NoX1; xperm_hyp hq)
    hFull

end EvmAsm.Evm64
