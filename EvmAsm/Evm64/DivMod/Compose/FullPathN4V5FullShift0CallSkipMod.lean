/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5FullShift0CallSkipMod

  Full n=4 v5 MOD code path, shift=0 call+skip case (base → nopOff), over
  `modCode_noNop_v5`: the shift=0 preloop + call+skip loop body
  (`evm_mod_n4_preloop_call_skip_shift0_spec_v5_noNop`, base→denormOff) composed
  with the SHARED shift=0 MOD epilogue (`evm_mod_shift0_epilogue_spec_v5_noNop`,
  denormOff→nopOff) via `cpsTripleWithin_seq_perm_same_cr`.  MOD mirror of
  `evm_div_n4_full_call_skip_shift0_spec_v5_noNop`: where the DIV epilogue copies
  the single quotient digit `qHat` into the output slots, the MOD epilogue copies
  the un-normalized REMAINDER u-cells (the mulsub result `ms`) into `sp+32..56`
  (no denormalization since `shift = 0`).  The quotient output cells
  (sp+4088/4080/4072/4064), unread by MOD, are framed through.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5ToDenormShift0CallSkipMod
import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5Mod

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Full n=4 v5 MOD shift=0 call+skip post (base → nopOff): the shift=0 MOD
    epilogue output (the mulsub remainder `ms` copied into the `sp+32..56` output
    slots and the loop registers) plus the cells framed past the epilogue
    (incl. the framed, unread quotient cells). -/
def fullModN4CallSkipShift0PostV5 (sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem : Word) : Assertion :=
  let qHat := divKTrialCallV5QHat (0 : Word) a3 b3
  let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
  let dLo := divKTrialCallV5DLo b3
  let divUn0 := divKTrialCallV5Un0 a3
  let scratchOut := divKTrialCallV5ScratchOut (0 : Word) a3 b3 scratchMem
  -- shift=0 MOD epilogue output
  (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ ms.1) ** (.x6 ↦ᵣ ms.2.1) ** (.x7 ↦ᵣ ms.2.2.1) **
  (.x2 ↦ᵣ ms.2.2.2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ms.2.2.2.1) **
  ((sp + signExtend12 3992) ↦ₘ (clzResult b3).1) **
  ((sp + signExtend12 4056) ↦ₘ ms.1) ** ((sp + signExtend12 4048) ↦ₘ ms.2.1) **
  ((sp + signExtend12 4040) ↦ₘ ms.2.2.1) ** ((sp + signExtend12 4032) ↦ₘ ms.2.2.2.1) **
  ((sp + 32) ↦ₘ ms.1) ** ((sp + 40) ↦ₘ ms.2.1) **
  ((sp + 48) ↦ₘ ms.2.2.1) ** ((sp + 56) ↦ₘ ms.2.2.2.1) **
  -- framed cells
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
  ((sp + signExtend12 3936) ↦ₘ scratchOut) ** regOwn .x1

/-- Full n=4 v5 MOD shift=0 call+skip path `base → nopOff` over `modCode_noNop_v5`. -/
theorem evm_mod_n4_full_call_skip_shift0_spec_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v2 v5 v6 v7 v10 v11Old : Word)
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
      (fullModN4CallSkipShift0PostV5 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) := by
  have hA := evm_mod_n4_preloop_call_skip_shift0_spec_v5_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v2 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem hbnz hb3nz hshift_z halign hborrow
  -- shift=0 MOD epilogue, instantiated with the raw-window mulsub remainder + loop-exit regs.
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
     ((sp + signExtend12 3936) ↦ₘ divKTrialCallV5ScratchOut (0 : Word) a3 b3 scratchMem) ** regOwn .x1)
    (by pcFree) hB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      simp only [preloopCallSkipShift0PostN4V5, loopBodyN4CallSkipJ0PostV5,
        loopBodyN4SkipPost, loopBodySkipPost, loopExitPost,
        se12_32, se12_40, se12_48, se12_56,
        u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
        u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at hp
      xperm_hyp hp) hA hBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta fullModN4CallSkipShift0PostV5; xperm_hyp hq)
    hFull

end EvmAsm.Evm64
