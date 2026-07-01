/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5FullShift0CallAddbackMod

  Full n=4 v5 MOD code path, shift=0 call+addback-beq case (base → nopOff), over
  `modCode_noNop_v5`: the shift=0 preloop + call+addback loop body
  (`evm_mod_n4_preloop_call_addback_shift0_spec_v5_noNop`, base→denormOff) composed
  with the SHARED shift=0 MOD epilogue (`evm_mod_shift0_epilogue_spec_v5_noNop`,
  denormOff→nopOff).  MOD mirror of `evm_div_n4_full_call_addback_shift0_spec_v5_noNop`:
  where the DIV epilogue copies the single addback-corrected quotient digit `q_out`
  into the output slots, the MOD epilogue copies the addback-corrected REMAINDER
  u-cells (`un0Out..un3Out`) into `sp+32..56` (no denormalization since `shift = 0`).
  The quotient output cells, unread by MOD, are framed through.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5ToDenormShift0CallAddbackMod
import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5Mod

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Full n=4 v5 MOD shift=0 call+addback post (base → nopOff): the shift=0 MOD
    epilogue output (the addback-corrected remainder `un0Out..un3Out` copied into
    the `sp+32..56` output slots and the loop registers) plus the cells framed past
    the epilogue (incl. the framed, unread quotient cells). -/
def fullModN4CallAddbackShift0PostV5 (sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem : Word) : Assertion :=
  let qHat := divKTrialCallV5QHat (0 : Word) a3 b3
  let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0 b1 b2 b3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - c3) b0 b1 b2 b3
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0 b1 b2 b3
  let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095 else qHat + signExtend12 4095
  let un0Out := if carry = 0 then ab'.1 else ab.1
  let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
  let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
  let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
  let u4_out := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
  let dLo := divKTrialCallV5DLo b3
  let divUn0 := divKTrialCallV5Un0 a3
  let scratchOut := divKTrialCallV5ScratchOut (0 : Word) a3 b3 scratchMem
  (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ un0Out) ** (.x6 ↦ᵣ un1Out) ** (.x7 ↦ᵣ un2Out) **
  (.x2 ↦ᵣ un3Out) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ un3Out) **
  ((sp + signExtend12 3992) ↦ₘ (clzResult b3).1) **
  ((sp + signExtend12 4056) ↦ₘ un0Out) ** ((sp + signExtend12 4048) ↦ₘ un1Out) **
  ((sp + signExtend12 4040) ↦ₘ un2Out) ** ((sp + signExtend12 4032) ↦ₘ un3Out) **
  ((sp + 32) ↦ₘ un0Out) ** ((sp + 40) ↦ₘ un1Out) **
  ((sp + 48) ↦ₘ un2Out) ** ((sp + 56) ↦ₘ un3Out) **
  (.x9 ↦ᵣ (0 : Word) + signExtend12 4095) ** (.x11 ↦ᵣ q_out) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4088) ↦ₘ q_out) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4024) ↦ₘ u4_out) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 3984) ↦ₘ (4 : Word)) ** ((sp + signExtend12 3976) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 3968) ↦ₘ (base + div128CallRetOff)) ** ((sp + signExtend12 3960) ↦ₘ b3) **
  ((sp + signExtend12 3952) ↦ₘ dLo) ** ((sp + signExtend12 3944) ↦ₘ divUn0) **
  ((sp + signExtend12 3936) ↦ₘ scratchOut) ** regOwn .x1

/-- Full n=4 v5 MOD shift=0 call+addback path `base → nopOff` over `modCode_noNop_v5`. -/
theorem evm_mod_n4_full_call_addback_shift0_spec_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v2 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_z : (clzResult b3).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hborrow : (if BitVec.ult (0 : Word)
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV5QHat (0 : Word) a3 b3
      let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0 b1 b2 b3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - c3) b0 b1 b2 b3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 b0 b1 b2 b3 ≠ 0) :
    cpsTripleWithin ((((8 + 21 + 24 + 4) + 13) + 234) + 12) base (base + nopOff) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
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
       (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1)
      (fullModN4CallAddbackShift0PostV5 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) := by
  have hA := evm_mod_n4_preloop_call_addback_shift0_spec_v5_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v2 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem hbnz hb3nz hshift_z halign hborrow hcarry2_nz
  -- abbreviate the raw-window addback components (matching loopBodyAddbackBeqPost).
  let qHat := divKTrialCallV5QHat (0 : Word) a3 b3
  let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0 b1 b2 b3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - c3) b0 b1 b2 b3
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0 b1 b2 b3
  let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095 else qHat + signExtend12 4095
  let un0Out := if carry = 0 then ab'.1 else ab.1
  let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
  let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
  let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
  let u4_out := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
  have hB := evm_mod_shift0_epilogue_spec_v5_noNop sp base
    un0Out un1Out un2Out un3Out (clzResult b3).1
    un3Out ((0 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088)
    c3 b0 b1 b2 b3 hshift_z
  have hBf := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ (0 : Word) + signExtend12 4095) ** (.x11 ↦ᵣ q_out) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4088) ↦ₘ q_out) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4024) ↦ₘ u4_out) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ (4 : Word)) ** ((sp + signExtend12 3976) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3968) ↦ₘ (base + div128CallRetOff)) ** ((sp + signExtend12 3960) ↦ₘ b3) **
     ((sp + signExtend12 3952) ↦ₘ divKTrialCallV5DLo b3) **
     ((sp + signExtend12 3944) ↦ₘ divKTrialCallV5Un0 a3) **
     ((sp + signExtend12 3936) ↦ₘ divKTrialCallV5ScratchOut (0 : Word) a3 b3 scratchMem) ** regOwn .x1)
    (by pcFree) hB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      simp only [preloopCallAddbackShift0PostN4V5, loopBodyN4CallAddbackBeqJ0PostV5,
        loopBodyN4AddbackBeqPost, loopBodyAddbackBeqPost, loopExitPost,
        se12_32, se12_40, se12_48, se12_56,
        u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
        u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at hp
      xperm_hyp hp) hA hBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta fullModN4CallAddbackShift0PostV5; xperm_hyp hq)
    hFull

end EvmAsm.Evm64
