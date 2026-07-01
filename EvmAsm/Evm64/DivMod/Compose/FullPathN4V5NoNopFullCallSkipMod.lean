/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopFullCallSkipMod

  Full n=4 v5 MOD call+skip path: base → nopOff over `modCode_noNop_v5`
  (shift ≠ 0, call+skip).  MOD mirror of `evm_div_n4_full_call_skip_spec_v5_noNop`:
  composes the preloop+body (`evm_mod_n4_preloop_call_skip_spec_v5_noNop`,
  base→denormOff) with the MOD denorm/epilogue
  (`evm_mod_n4_call_skip_denorm_epilogue_spec_v5_noNop`, denormOff→nopOff).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopDenormCallSkipMod

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Full n=4 v5 MOD call+skip path: base → nopOff (shift ≠ 0). -/
theorem evm_mod_n4_full_call_skip_spec_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
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
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
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
      (fullModN4CallSkipPostV5 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) := by
  have hA := evm_mod_n4_preloop_call_skip_spec_v5_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow
  have hB := evm_mod_n4_call_skip_denorm_epilogue_spec_v5_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 scratchMem hshift_nz
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hA hB
  exact cpsTripleWithin_mono_nSteps (by decide) hFull

end EvmAsm.Evm64
