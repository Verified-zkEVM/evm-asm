/-
  EvmAsm.Evm64.DivMod.Compose.V6DivStackSpec

  The v6 DIV top-level stack spec (`evm_div_v6_stack_spec`, bead `czmzp`):
  the full n=1 fast-path dispatch over `divCodeV6`, merging the BNE (n≥2) and
  BEQ (b0=0) dispatch branches with the reused v5 arm
  (`evm_div_v5_unconditional_over_divCodeV6`) and the fast-body arm
  (`divK_fastBody_dispatchPostV5_within_v6`) via `cpsBranchWithin_merge_same_cr`.

  Same pre/post as the v5 spec (`divModStackDispatchPreNoX1 … ** sp+3936 →
  divStackDispatchPostV5 sp a b`), only with entry at `base` over the full v6
  dispatch.
-/

import EvmAsm.Evm64.DivMod.Compose.V6FastArmTriple
import EvmAsm.Evm64.DivMod.Compose.V5ReuseV6
import EvmAsm.Evm64.DivMod.Compose.DispatchV6
import EvmAsm.Rv64.Tactics.ExtractPure

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- `fromLimbs` of the per-limb `getLimbN` match recovers the word. -/
private theorem fromLimbs_match_getLimbN (v : EvmWord) :
    (EvmWord.fromLimbs fun i : Fin 4 => match i with
      | 0 => v.getLimbN 0 | 1 => v.getLimbN 1 | 2 => v.getLimbN 2 | 3 => v.getLimbN 3) = v := by
  rw [show (fun i : Fin 4 => match i with
      | 0 => v.getLimbN 0 | 1 => v.getLimbN 1 | 2 => v.getLimbN 2 | 3 => v.getLimbN 3)
      = v.getLimb from by
    funext i; fin_cases i <;> rfl]
  exact EvmWord.fromLimbs_getLimb v

/-- Peel a pure `⌜fact⌝` from the right of the precondition into an ambient
    hypothesis. -/
private theorem cpsTripleWithin_of_pure_imp
    {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} {fact : Prop}
    (h : fact → cpsTripleWithin nSteps entry exit_ cr P Q) :
    cpsTripleWithin nSteps entry exit_ cr (P ** ⌜fact⌝) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, hpq⟩ := hPR
  obtain ⟨h1, h2, hd, hunion, hPF, hR_⟩ := hpq
  have hpf := (sepConj_pure_right h1).1 hPF
  exact h hpf.2 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hunion, hpf.1, hR_⟩ hpc

/-- **The v6 DIV stack spec.** Over `divCodeV6`, entry `base`, exit
    `base + v6ExitOff`: the full n=1 fast-path dispatch divides `a` by `b` for
    every 256-bit divisor, landing `divStackDispatchPostV5 sp a b`. -/
theorem evm_div_v6_stack_spec
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halignV5 : (((base + v6V5Off) + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      (base + v6V5Off) + div128CallRetOff)
    (halign3 : ((base + v6Digit3Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit3Off + 16)
    (halign2 : ((base + v6Digit2Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit2Off + 16)
    (halign1 : ((base + v6Digit1Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit1Off + 16)
    (halign0 : ((base + v6Digit0Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit0Off + 16) :
    cpsTripleWithin 954 base (base + v6ExitOff) (divCodeV6 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        (divDispatchShiftX2 b) v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  -- v5 arm, parametric in the (post-dispatch) values of x5 / x10.
  have hv5app : ∀ (x5v x10v : Word),
      cpsTripleWithin unifiedDivBound (base + v6V5Off) (base + v6ExitOff) (divCodeV6 base)
        (divModStackDispatchPreNoX1 sp a b
          (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
          (divDispatchShiftX2 b) x5v v6 v7 x10v v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostV5 sp a b) := fun x5v x10v =>
    evm_div_v5_unconditional_over_divCodeV6 sp base a b raVal x5v v6 v7 x10v v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem halignV5
  -- Fast arm, given the n=1 divisor facts (b0 ≠ 0, b1|b2|b3 = 0); its post is
  -- already `divStackDispatchPostV5 sp a b` after the `fromLimbs∘getLimbN` fold.
  have hfastapp :
      (b.getLimbN 0 ≠ (0 : Word)) →
      ((b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3) = (0 : Word)) →
      cpsTripleWithin 434 (base + v6ClzOff) (base + v6ExitOff) (divCodeV6 base)
        ((((((.x5 ↦ᵣ b.getLimbN 0) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word))) **
            ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ divDispatchShiftX2 b) ** ((sp + signExtend12 32) ↦ₘ b.getLimbN 0) **
             ((sp + signExtend12 3992) ↦ₘ shiftMem) ** ((sp + signExtend12 3984) ↦ₘ nMem))) **
           ((.x10 ↦ᵣ b.getLimbN 3) ** ((sp + 0) ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
            ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
            ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
            ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1) **
            ((sp + signExtend12 4056) ↦ₘ u0))) **
          ((.x9 ↦ᵣ (signExtend12 (4 : BitVec 12) - (4 : Word))) ** (.x11 ↦ᵣ v11) **
           (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
           (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0) **
           (sp + signExtend12 3936 ↦ₘ scratchMem) **
           ((sp + signExtend12 4064) ↦ₘ q3) ** ((sp + signExtend12 4072) ↦ₘ q2) **
           ((sp + signExtend12 4080) ↦ₘ q1) ** ((sp + signExtend12 4088) ↦ₘ q0) **
           ((sp + 40) ↦ₘ b.getLimbN 1) ** ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3))) **
         (((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
          ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
          ((.x1 : Reg) ↦ᵣ raVal)))
        (divStackDispatchPostV5 sp a b) := by
    intro hb0 hor
    have hb3z : b.getLimbN 3 = 0 := (BitVec.or_eq_zero_iff.mp hor).2
    have hb1z : b.getLimbN 1 = 0 := (BitVec.or_eq_zero_iff.mp (BitVec.or_eq_zero_iff.mp hor).1).1
    have hb2z : b.getLimbN 2 = 0 := (BitVec.or_eq_zero_iff.mp (BitVec.or_eq_zero_iff.mp hor).1).2
    have hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 := by
      rw [hb1z, hb2z, hb3z]; simpa using hb0
    refine cpsTripleWithin_weaken (fun h hp => hp) (fun h hq => ?_)
      (divK_fastBody_dispatchPostV5_within_v6 sp (b.getLimbN 0)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        v6 v7 (divDispatchShiftX2 b) (b.getLimbN 3) (signExtend12 (4 : BitVec 12) - (4 : Word)) v11
        q3 q2 q1 q0 shiftMem nMem retMem dMem dloMem scratch_un0 scratchMem
        (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) u0 u1 u2 u3 u4
        u5 u6 u7 jMem raVal (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) base
        hbnz hb1z hb2z hb3z halign3 halign2 halign1 halign0)
    convert hq using 3 <;> exact (fromLimbs_match_getLimbN _).symm
  -- Fast arm with the two divisor facts bundled into the precondition.
  have hfast_full := cpsTripleWithin_of_pure_imp (fun
      (hor : (b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3) = (0 : Word)) =>
    cpsTripleWithin_of_pure_imp (fun (hb0 : b.getLimbN 0 ≠ (0 : Word)) =>
      hfastapp hb0 hor))
  -- v5 arms with the dispatch pure facts bundled (so xperm matches them as atoms).
  have hv5_beqT := cpsTripleWithin_of_pure_imp (fun
      (_ : (b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3) = (0 : Word)) =>
    cpsTripleWithin_of_pure_imp (fun (_ : b.getLimbN 0 = (0 : Word)) =>
      hv5app (b.getLimbN 0) (b.getLimbN 3)))
  have hv5_bneT := cpsTripleWithin_of_pure_imp (fun
      (_ : (b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3) ≠ (0 : Word)) =>
    hv5app (b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3) (b.getLimbN 3))
  -- INNER merge: BEQ {v5 (b0=0) | fast (b0≠0)} at base+24, bound 948.
  have hbeq := divK_dispatchN1_beq_spec_within_v6 sp
    (b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3) (b.getLimbN 0) base
  have hbeqf := cpsBranchWithin_frameR
    ((.x9 ↦ᵣ (signExtend12 (4 : BitVec 12) - (4 : Word))) ** (.x1 ↦ᵣ raVal) ** (.x6 ↦ᵣ v6) **
     (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ b.getLimbN 3) ** (.x11 ↦ᵣ v11) **
     (.x2 ↦ᵣ divDispatchShiftX2 b) ** evmWordIs sp a **
     ((sp + 40) ↦ₘ b.getLimbN 1) ** ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3) **
     divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
     ((sp + signExtend12 3936) ↦ₘ scratchMem) **
     ⌜(b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3) = (0 : Word)⌝)
    (by pcFree) hbeq
  have hinner := cpsBranchWithin_merge_same_cr hbeqf
    (cpsTripleWithin_weaken (fun h hp => by
        rw [divModStackDispatchPreNoX1_unfold, evmWordIs_sp32_unfold]
        simp only [AddrNorm.se12_32] at hp
        xperm_hyp hp)
      (fun h hq => hq)
      hv5_beqT)
    (cpsTripleWithin_mono_nSteps (by decide)
      (cpsTripleWithin_weaken (fun h hp => by
          rw [show (sp + 0 : Word) = sp from by bv_omega]
          rw [evmWordIs_sp_unfold, divScratchValuesCallNoX1_unfold, divScratchValues_unfold] at hp
          xperm_hyp hp)
        (fun h hq => hq)
        hfast_full))
  -- OUTER merge: BNE {v5 (n≥2) | inner (base+24)} at base, bound 954.
  have hbne := divK_dispatchN1_bne_spec_within_v6 sp v5 v10
    (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) base
  have hbnef := cpsBranchWithin_frameR
    ((.x9 ↦ᵣ (signExtend12 (4 : BitVec 12) - (4 : Word))) ** (.x1 ↦ᵣ raVal) ** (.x6 ↦ᵣ v6) **
     (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x2 ↦ᵣ divDispatchShiftX2 b) ** evmWordIs sp a **
     ((sp + 32) ↦ₘ b.getLimbN 0) **
     divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
     ((sp + signExtend12 3936) ↦ₘ scratchMem))
    (by pcFree) hbne
  have houter := cpsBranchWithin_merge_same_cr hbnef
    (cpsTripleWithin_mono_nSteps (by decide)
      (cpsTripleWithin_weaken (fun h hp => by
          rw [divModStackDispatchPreNoX1_unfold, evmWordIs_sp32_unfold]
          simp only [AddrNorm.se12_40, AddrNorm.se12_48, AddrNorm.se12_56] at hp
          xperm_hyp hp)
        (fun h hq => hq)
        hv5_bneT))
    (cpsTripleWithin_weaken (fun h hp => by
        simp only [AddrNorm.se12_32, AddrNorm.se12_40, AddrNorm.se12_48, AddrNorm.se12_56] at hp ⊢
        xperm_hyp hp)
      (fun h hq => hq)
      hinner)
  -- Fold the entry precondition back to `divModStackDispatchPreNoX1 … ** sp+3936`.
  refine cpsTripleWithin_weaken (fun h hp => by
      rw [divModStackDispatchPreNoX1_unfold, evmWordIs_sp32_unfold] at hp
      simp only [AddrNorm.se12_40, AddrNorm.se12_48, AddrNorm.se12_56] at ⊢
      xperm_hyp hp)
    (fun h hq => hq) houter

end EvmAsm.Evm64
