/-
  EvmAsm.Evm64.DivMod.Compose.V6FastArmTriple

  The v6 DIV fast-arm triple (bead `evm-asm-35xs4`): a single
  `cpsTripleWithin` from the fast-path entry `v6ClzOff` to `v6ExitOff` over
  `divCodeV6`, whose postcondition is `divStackDispatchPostV5 sp a b` — the
  shape the reused v5 arm produces, so both arms converge under
  `cpsBranchWithin_merge_same_cr`.

  Built by a `by_cases` on the shift amount `(clzResult b0).1`:
    - `= 0`  → `divK_fastBody_shift0_spec_within_v6` (422 steps),
    - `≠ 0`  → `divK_fastBody_shiftNz_spec_within_v6` (434 steps),
  each framed with the four extra scratch cells (`sp+4016/4008/4000/3976`) and
  `x1` the body footprint omits, its post weakened to `divStackDispatchPostV5`
  via `fast_canonical_to_dispatchPostV5_{shiftNz,shift0}`, and lifted to the
  uniform 434-step bound with `cpsTripleWithin_mono_nSteps`.  The shared
  precondition `FASTPRE` (the shift≠0 body pre plus the extras) is permuted to
  each lane's body pre with `xperm`.
-/

import EvmAsm.Evm64.DivMod.Compose.BodyV6
import EvmAsm.Evm64.DivMod.Compose.V6FastArmConnect

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **v6 DIV fast-arm triple.** From `v6ClzOff` to `v6ExitOff` over `divCodeV6`,
    the n=1 fast path divides `a = ⟨a0,a1,a2,a3⟩` by `b = ⟨b0,0,0,0⟩` (b0 ≠ 0),
    landing `divStackDispatchPostV5 sp a b`. Covers both shift lanes. -/
theorem divK_fastBody_dispatchPostV5_within_v6
    (sp b0 a0 a1 a2 a3 v6Old v7Old v2Old v10 v9d v11d : Word)
    (qm3 qm2 qm1 qm0 m3992 m3984 retMem dMem dloMem un0Mem scratchMem m40 m48 m56 : Word)
    (u0Old u1Old u2Old u3Old u4Old : Word)
    (u5 u6 u7 jMem x1v b1 b2 b3 : Word) (base : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (halign3 : ((base + v6Digit3Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit3Off + 16)
    (halign2 : ((base + v6Digit2Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit2Off + 16)
    (halign1 : ((base + v6Digit1Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit1Off + 16)
    (halign0 : ((base + v6Digit0Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit0Off + 16) :
    cpsTripleWithin 434 (base + v6ClzOff) (base + v6ExitOff) (divCodeV6 base)
      ((((((.x5 ↦ᵣ b0) ** (.x6 ↦ᵣ v6Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word))) **
          ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2Old) ** ((sp + signExtend12 32) ↦ₘ b0) **
           ((sp + signExtend12 3992) ↦ₘ m3992) ** ((sp + signExtend12 3984) ↦ₘ m3984))) **
         ((.x10 ↦ᵣ v10) ** ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
          ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
          ((sp + signExtend12 4024) ↦ₘ u4Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
          ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
          ((sp + signExtend12 4056) ↦ₘ u0Old))) **
        ((.x9 ↦ᵣ v9d) ** (.x11 ↦ᵣ v11d) **
         (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
         (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ un0Mem) **
         (sp + signExtend12 3936 ↦ₘ scratchMem) **
         ((sp + signExtend12 4064) ↦ₘ qm3) ** ((sp + signExtend12 4072) ↦ₘ qm2) **
         ((sp + signExtend12 4080) ↦ₘ qm1) ** ((sp + signExtend12 4088) ↦ₘ qm0) **
         ((sp + 40) ↦ₘ m40) ** ((sp + 48) ↦ₘ m48) ** ((sp + 56) ↦ₘ m56))) **
       (((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
        ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        ((.x1 : Reg) ↦ᵣ x1v)))
      (divStackDispatchPostV5 sp
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)) := by
  by_cases hclz : (clzResult b0).1 = (0 : Word)
  · -- shift = 0 lane (422 steps)
    have hbody := divK_fastBody_shift0_spec_within_v6 sp b0 a0 a1 a2 a3 v6Old v7Old v2Old v10
      v9d v11d qm3 qm2 qm1 qm0 m3992 m3984 retMem dMem dloMem un0Mem scratchMem m40 m48 m56
      u0Old u1Old u2Old u3Old u4Old base hclz halign3 halign2 halign1 halign0
    have hbodyf := cpsTripleWithin_frameR
      (((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
       ((.x1 : Reg) ↦ᵣ x1v))
      (by pcFree) hbody
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => by simp only [AddrNorm.se12_0]; xperm_hyp hp)
        (fun h hq => ?_) hbodyf)
    simp only [AddrNorm.se12_0] at hq
    rw [show (sp + 0 : Word) = sp from by bv_omega] at hq
    exact fast_canonical_to_dispatchPostV5_shift0 sp a0 a1 a2 a3 b0 b1 b2 b3
      (base + v6Digit0Off + 16)
      (v6chainQ0 (0 : Word) a3 a2 a1 a0 (v6nD b0))
      (v6chainQ0 (0 : Word) a3 a2 a1 a0 (v6nD b0))
      (v6chainQ1 (0 : Word) a3 a2 a1 (v6nD b0))
      (v6chainQ2 (0 : Word) a3 a2 (v6nD b0))
      (v6chainQ3 (0 : Word) a3 (v6nD b0))
      (v6chainQ0 (0 : Word) a3 a2 a1 a0 (v6nD b0))
      (v6chainQ1 (0 : Word) a3 a2 a1 (v6nD b0))
      (v6chainQ2 (0 : Word) a3 a2 (v6nD b0))
      (v6chainQ3 (0 : Word) a3 (v6nD b0))
      (v6chainR0 (0 : Word) a3 a2 a1 a0 (v6nD b0))
      (v6chainR1 (0 : Word) a3 a2 a1 (v6nD b0))
      (v6chainR2 (0 : Word) a3 a2 (v6nD b0))
      (v6chainR3 (0 : Word) a3 (v6nD b0))
      (0 : Word) u5 u6 u7 ((clzResult b0).1) (v6nD b0) jMem x1v
      hbnz hb1z hb2z hb3z hclz h (by xperm_hyp hq)
  · -- shift ≠ 0 lane (434 steps)
    have hbody := divK_fastBody_shiftNz_spec_within_v6 sp b0 a0 a1 a2 a3 v6Old v7Old v2Old v10
      v9d v11d qm3 qm2 qm1 qm0 m3992 m3984 retMem dMem dloMem un0Mem scratchMem m40 m48 m56
      u0Old u1Old u2Old u3Old u4Old base hclz halign3 halign2 halign1 halign0
    have hbodyf := cpsTripleWithin_frameR
      (((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
       ((.x1 : Reg) ↦ᵣ x1v))
      (by pcFree) hbody
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hbodyf
    rw [show (sp + 0 : Word) = sp from by bv_omega] at hq
    exact fast_canonical_to_dispatchPostV5_shiftNz sp a0 a1 a2 a3 b0 b1 b2 b3
      (base + v6Digit0Off + 16)
      (v6chainQ0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0))
      (v6chainQ0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0))
      (v6chainQ1 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nD b0))
      (v6chainQ2 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nD b0))
      (v6chainQ3 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nD b0))
      (v6chainQ0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0))
      (v6chainQ1 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nD b0))
      (v6chainQ2 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nD b0))
      (v6chainQ3 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nD b0))
      (v6chainR0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0))
      (v6chainR1 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nD b0))
      (v6chainR2 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nD b0))
      (v6chainR3 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nD b0))
      (v6nU4 a3 b0) u5 u6 u7 ((clzResult b0).1) (v6nD b0) jMem x1v
      hbnz hb1z hb2z hb3z hclz h (by xperm_hyp hq)

end EvmAsm.Evm64
