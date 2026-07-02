/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5PathShift0

  Bridge from the n=3 v5 shift=0 preloop exit (at `loopBodyOff`, the layout
  produced by `evm_div_n3_to_loopSetup_shift0_spec_v5_noNop`, #7552) to the loop's
  entry bundle `loopN3PreWithScratchV4NoX1` over the RAW divisor `(b0, b1, b2, 0)`
  and shift=0 verbatim window — the shift=0 analog of
  `loopSetupPost_to_loopN3PreWithScratchV4NoX1_framed`.  Then the shift=0 path
  `base → denormOff`: preloop (#7552) ∘ bridge ∘ loop (#7554), carry from shape.
  n=3 analog of `FullPathN2V5PathShift0`.  Bead `evm-asm-wbc4i.9.3.3.8`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5PreloopShift0
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5LoopShift0
import EvmAsm.Evm64.DivMod.Compose.FullPathN3Loop

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Bridge: shift=0 preloop exit (`b3 = 0`) plus the framed scratch/return cells
    implies the loop entry bundle over the raw divisor + verbatim window. -/
theorem n3_shift0_loopExit_to_loopN3PreWithScratch (sp : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v11Old jMem retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hb3z : b3 = 0) :
    ∀ h,
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (3 : Word)) **
        (.x9 ↦ᵣ (signExtend12 (4 : BitVec 12) - (3 : Word))) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ (clzResult b2).1) **
        (.x7 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
        (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - (clzResult b2).1)) **
        ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
        ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
        ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4056) ↦ₘ a0) ** ((sp + signExtend12 4048) ↦ₘ a1) **
        ((sp + signExtend12 4040) ↦ₘ a2) ** ((sp + signExtend12 4032) ↦ₘ a3) **
        ((sp + signExtend12 4024) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (3 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1)) **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        ((sp + signExtend12 3968) ↦ₘ retMem) ** ((sp + signExtend12 3960) ↦ₘ dMem) **
        ((sp + signExtend12 3952) ↦ₘ dloMem) ** ((sp + signExtend12 3944) ↦ₘ scratchUn0) **
        ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ raVal))) h →
      ((loopN3PreWithScratchV4NoX1 sp jMem (3 : Word) (clzResult b2).1
        ((clzResult b2).2 >>> (63 : Nat)) (0 : Word) v11Old
        (signExtend12 (0 : BitVec 12) - (clzResult b2).1)
        b0 b1 b2 0 a1 a2 a3 0 0 a0 0 0
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))) h := by
  intro h hp
  subst hb3z
  rw [show signExtend12 (4 : BitVec 12) - (3 : Word) = (1 : Word) from by decide] at hp
  delta loopN3PreWithScratchV4NoX1 loopN3PreWithScratchNoX1 loopN3Pre
  simp only [n3_ub1_off0, n3_ub1_off4088, n3_ub1_off4080, n3_ub1_off4072, n3_ub1_off4064,
    n3_ub0_off0, n3_qa1, n3_qa0,
    se12_32, se12_40, se12_48, se12_56] at hp ⊢
  xperm_hyp hp

/-- Flag-parameterized n=3 v5 shift=0 path `base → denormOff`: preloop (#7552) ∘
    bridge ∘ loop (#7554), the carry discharged from shape. -/
theorem evm_div_n3_to_denorm_shift0_param_v5_noNop (bltu_1 bltu_0 : Bool)
    (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v2 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal x9In : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_z : (clzResult b2).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 = BitVec.ult (0 : Word) b2)
    (hbltu_0 : bltu_0 =
      BitVec.ult (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 b2) :
    cpsTripleWithin (((8 + 21 + 24 + 4) + 13) + 468) base (base + denormOff)
      (divCode_noNop_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) **
        (.x9 ↦ᵣ x9In) **
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
        ((sp + signExtend12 3992) ↦ₘ shiftMem)) **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        ((sp + signExtend12 3968) ↦ₘ retMem) ** ((sp + signExtend12 3960) ↦ₘ dMem) **
        ((sp + signExtend12 3952) ↦ₘ dloMem) ** ((sp + signExtend12 3944) ↦ₘ scratchUn0) **
        ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ raVal)))
      ((loopN3UnifiedPostV5NoX1 bltu_1 bltu_0 sp base
        b0 b1 b2 0 a1 a2 a3 0 0 a0
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))) := by
  have hb2ge : b2.toNat ≥ 2 ^ 63 := clz_zero_imp_msb hshift_z
  have hPre := evm_div_n3_to_loopSetup_shift0_spec_v5_noNop sp base a0 a1 a2 a3 b0 b1 b2 b3
    v2 v5 v6 v7 v10 q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem x9In
    hbnz hb3z hb2nz hshift_z
  have hPref := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
     ((sp + signExtend12 3968) ↦ₘ retMem) ** ((sp + signExtend12 3960) ↦ₘ dMem) **
     ((sp + signExtend12 3952) ↦ₘ dloMem) ** ((sp + signExtend12 3944) ↦ₘ scratchUn0) **
     ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ raVal))
    (by pcFree) hPre
  have hLoop := divK_loop_n3_shift0_param_v5_noNop bltu_1 bltu_0 sp base jMem (3 : Word)
    (clzResult b2).1 ((clzResult b2).2 >>> (63 : Nat)) (0 : Word) v11Old
    (signExtend12 (0 : BitVec 12) - (clzResult b2).1)
    a0 a1 a2 a3 b0 b1 b2 (0 : Word) (0 : Word) raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hb2ge hbltu_1 hbltu_0
  have hLoopf := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))
    (by pcFree) hLoop
  have hPre' := cpsTripleWithin_weaken (fun h hp => hp)
    (n3_shift0_loopExit_to_loopN3PreWithScratch sp a0 a1 a2 a3 b0 b1 b2 b3 v11Old
      jMem retMem dMem dloMem scratchUn0 scratchMem raVal hb3z)
    hPref
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hPre' hLoopf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => hp) (fun h hq => hq) hFull

end EvmAsm.Evm64
