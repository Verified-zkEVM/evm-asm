/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5FullShift0CallSkip

  Full n=4 v5 DIV code path, shift=0 call+skip case (base → nopOff), over
  `divCode_noNop_v5`: the shift=0 preloop + call+skip loop body
  (`evm_div_n4_preloop_call_skip_shift0_spec_v5_noNop`, #7618, base→denormOff)
  composed with the SHARED shift=0 DIV epilogue
  (`evm_div_shift0_epilogue_spec_v5_noNop`, denormOff→nopOff) via
  `cpsTripleWithin_seq_perm_same_cr`.  Shift=0 analog of the call+skip full path
  `evm_div_n4_full_call_skip_spec_v5_noNop` (#7597); the epilogue is the n-agnostic
  shift=0 tail (which just copies the single quotient digit `qHat` into the output
  slots, since `shift = 0` means no remainder denormalization).  Bead
  `evm-asm-wbc4i.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5ToDenormShift0CallSkip
public import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5
public import EvmAsm.Evm64.DivMod.Compose.FullPathN4Loop

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Full n=4 v5 shift=0 call+skip post (base → nopOff): the shift=0 DIV epilogue
    output (quotient `qHat` copied into the `sp+32..56` output slots and the loop
    registers) plus the cells framed past the epilogue. -/
def fullDivN4CallSkipShift0PostV5 (sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem : Word) : Assertion :=
  let qHat := divKTrialCallV5QHat (0 : Word) a3 b3
  let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
  let dLo := divKTrialCallV5DLo b3
  let divUn0 := divKTrialCallV5Un0 a3
  let scratchOut := divKTrialCallV5ScratchOut (0 : Word) a3 b3 scratchMem
  -- shift=0 epilogue output
  (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ qHat) ** (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
  (.x2 ↦ᵣ ms.2.2.2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
  ((sp + signExtend12 3992) ↦ₘ (clzResult b3).1) **
  ((sp + signExtend12 4088) ↦ₘ qHat) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + 32) ↦ₘ qHat) ** ((sp + 40) ↦ₘ (0 : Word)) **
  ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
  -- framed cells
  (.x9 ↦ᵣ (0 : Word) + signExtend12 4095) ** (.x11 ↦ᵣ qHat) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4056) ↦ₘ ms.1) ** ((sp + signExtend12 4048) ↦ₘ ms.2.1) **
  ((sp + signExtend12 4040) ↦ₘ ms.2.2.1) ** ((sp + signExtend12 4032) ↦ₘ ms.2.2.2.1) **
  ((sp + signExtend12 4024) ↦ₘ ((0 : Word) - ms.2.2.2.2)) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 3984) ↦ₘ (4 : Word)) ** ((sp + signExtend12 3976) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 3968) ↦ₘ (base + div128CallRetOff)) ** ((sp + signExtend12 3960) ↦ₘ b3) **
  ((sp + signExtend12 3952) ↦ₘ dLo) ** ((sp + signExtend12 3944) ↦ₘ divUn0) **
  ((sp + signExtend12 3936) ↦ₘ scratchOut) ** regOwn .x1

/-- Full n=4 v5 shift=0 call+skip path `base → nopOff` over `divCode_noNop_v5`. -/
theorem evm_div_n4_full_call_skip_shift0_spec_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v2 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_z : (clzResult b3).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3 (0 : Word)) :
    cpsTripleWithin ((((8 + 21 + 24 + 4) + 13) + 158) + 12) base (base + nopOff) (divCode_noNop_v5 base)
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
      (fullDivN4CallSkipShift0PostV5 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) := by
  have hA := evm_div_n4_preloop_call_skip_shift0_spec_v5_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v2 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem hbnz hb3nz hshift_z halign hborrow
  -- shift=0 epilogue, instantiated with the raw-window quotient + loop-exit regs.
  have hB := evm_div_shift0_epilogue_spec_v5_noNop sp base
    (0 : Word) (0 : Word) (0 : Word) (0 : Word) (clzResult b3).1
    (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1
    ((0 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088)
    (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2
    (divKTrialCallV5QHat (0 : Word) a3 b3) (0 : Word) (0 : Word) (0 : Word)
    b0 b1 b2 b3 hshift_z
  have hBf := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ (0 : Word) + signExtend12 4095) ** (.x11 ↦ᵣ divKTrialCallV5QHat (0 : Word) a3 b3) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).1) **
     ((sp + signExtend12 4048) ↦ₘ (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.1) **
     ((sp + signExtend12 4040) ↦ₘ (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.1) **
     ((sp + signExtend12 4032) ↦ₘ (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1) **
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
    (fun h hq => by delta fullDivN4CallSkipShift0PostV5; xperm_hyp hq)
    hFull

end EvmAsm.Evm64
