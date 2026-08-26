/-
  EvmAsm.Evm64.DivMod.Spec.N3V4StackPre

  Legacy stack-level wrappers for n=3 DIV v4 preloop+loop paths with raw carry.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.Dispatcher
public import EvmAsm.Evm64.DivMod.Spec.CallablePost
public import EvmAsm.Evm64.DivMod.Spec.N3QuotientWord
public import EvmAsm.Evm64.DivMod.Spec.N3QuotientStackBridge
public import EvmAsm.Evm64.DivMod.Spec.UnifiedBzero
public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V4
public import EvmAsm.Evm64.DivMod.Compose.ModFullPathN3V4NoNopPreloop
public import EvmAsm.Evm64.DivMod.Spec.N3RemainderWordV4

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- Legacy EvmWord-level wrapper around the n=3 exact-x1/scratch v4
    preloop+loop path over the no-NOP v4 body. It still exposes raw
    `Carry2NzAll`; prefer selected-carry wrappers for new v4 work. -/
theorem evm_div_n3_preloop_loop_stack_pre_spec_v4_noNop (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hbltu_0 : bltu_0 =
      match bltu_1, hbltu_1 with
      | false, _ =>
        BitVec.ult
          (iterN3Max
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      | true, _ =>
        BitVec.ult
          (iterWithDoubleAddback
            (divKTrialCallV4QHat
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
              (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hcarry2 : Carry2NzAll
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 448)
      base (base + denormOff) (divCode_noNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      ((loopN3UnifiedPostV4NoX1 bltu_1 bltu_0 sp base
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).2.2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).2.2.2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).2.2.2.2
        (0 : Word)
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
        ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult (b.getLimbN 2)).1))) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hrawNoNop := fullDivN3_preloop_loop_unified_exact_x1_scratch_v4_noNop
    bltu_1 bltu_0 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz' hb3z hb2nz hshift_nz halign hbltu_1
    (by cases bltu_1 <;> simpa using hbltu_0) hcarry2
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [divModStackDispatchPreNoX1_unfold, divScratchValuesCallNoX1_unfold] at hp
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hrawNoNop

theorem evm_div_n3_preloop_loop_stack_pre_spec_v4_noNop_selectedCarry
    (sp base : Word) (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word) (hbnz : b ≠ 0) (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hbltu_0 : bltu_0 =
      match bltu_1, hbltu_1 with
      | false, _ =>
        BitVec.ult
          (iterN3Max
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      | true, _ =>
        BitVec.ult
          (iterWithDoubleAddback
            (divKTrialCallV4QHat
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
              (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hcarry2_j1 :
      if bltu_1 then
        loopBodyN3CallAddbackCarry2NzV4
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
          (0 : Word)
      else
        isAddbackCarry2NzN3Max
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
          (0 : Word))
    (hcarry2_j0 :
      match bltu_1 with
      | false =>
        let r1 := iterN3Max
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
          (0 : Word)
        if bltu_0 then
          loopBodyN3CallAddbackCarry2NzV4
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).1
            r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
        else
          isAddbackCarry2NzN3Max
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).1
            r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
      | true =>
        let r1 := iterWithDoubleAddback
          (divKTrialCallV4QHat
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
          (0 : Word)
        if bltu_0 then
          loopBodyN3CallAddbackCarry2NzV4
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).1
            r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
        else
          isAddbackCarry2NzN3Max
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).1
            r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 448)
      base (base + denormOff) (divCode_noNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      ((loopN3UnifiedPostV4NoX1 bltu_1 bltu_0 sp base
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).2.2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).2.2.2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).2.2.2.2
        (0 : Word)
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
        ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult (b.getLimbN 2)).1))) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hrawNoNop :
      cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 448)
        base (base + denormOff) (divCode_noNop_v4 base)
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult (b.getLimbN 2)).2 >>> (63 : Nat)) **
          (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
          ((sp + 0) ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
          ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
          ((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
          ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3) **
          ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
          ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
          ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
          ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
          ((sp + signExtend12 4024) ↦ₘ u4Old) **
          ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
          ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
          ((sp + signExtend12 3992) ↦ₘ shiftMem)) **
         ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
          (sp + signExtend12 3968 ↦ₘ retMem) **
          (sp + signExtend12 3960 ↦ₘ dMem) **
          (sp + signExtend12 3952 ↦ₘ dloMem) **
          (sp + signExtend12 3944 ↦ₘ scratchUn0) **
          (sp + signExtend12 3936 ↦ₘ scratchMem) **
          (.x1 ↦ᵣ raVal)))
        ((loopN3UnifiedPostV4NoX1 bltu_1 bltu_0 sp base
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 2)).2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 2)).2.2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 2)).2.2.2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 2)).2.2.2.2
          (0 : Word)
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 2)).1
          retMem dMem dloMem scratchUn0 scratchMem **
          (.x1 ↦ᵣ raVal)) **
         (((sp + 0) ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
          ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
          ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
          ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
          ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
          ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
          ((sp + signExtend12 3992) ↦ₘ (clzResult (b.getLimbN 2)).1))) := by
    cases bltu_1 <;> cases bltu_0
    · exact fullDivN3_preloop_loop_unified_exact_x1_scratch_v4_noNop_selectedCarry
        false false sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
        hbnz' hb3z hb2nz hshift_nz halign hbltu_1
        (by simpa using hbltu_0) hcarry2_j1 hcarry2_j0
    · exact fullDivN3_preloop_loop_unified_exact_x1_scratch_v4_noNop_selectedCarry
        false true sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
        hbnz' hb3z hb2nz hshift_nz halign hbltu_1
        (by simpa using hbltu_0) hcarry2_j1 hcarry2_j0
    · exact fullDivN3_preloop_loop_unified_exact_x1_scratch_v4_noNop_selectedCarry
        true false sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
        hbnz' hb3z hb2nz hshift_nz halign hbltu_1
        (by simpa using hbltu_0) hcarry2_j1 hcarry2_j0
    · exact fullDivN3_preloop_loop_unified_exact_x1_scratch_v4_noNop_selectedCarry
        true true sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
        hbnz' hb3z hb2nz hshift_nz halign hbltu_1
        (by simpa using hbltu_0) hcarry2_j1 hcarry2_j0
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [divModStackDispatchPreNoX1_unfold, divScratchValuesCallNoX1_unfold] at hp
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hrawNoNop

/-- EvmWord-level wrapper around the n=3 MOD v4/no-NOP path from dispatcher
    entry to loop setup, preserving the callable `x1` and v4 scratch frame. -/
theorem evm_mod_n3_to_loopSetup_stack_pre_spec_v4_noNop (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4)
      base (base + loopBodyOff) (modCode_noNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (loopSetupPost sp (3 : Word) (clzResult (b.getLimbN 2)).1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) **
       (.x11 ↦ᵣ v11Old) **
       ((sp + signExtend12 3976) ↦ₘ jMem) **
       ((sp + signExtend12 3968) ↦ₘ retMem) **
         ((sp + signExtend12 3960) ↦ₘ dMem) **
         ((sp + signExtend12 3952) ↦ₘ dloMem) **
         ((sp + signExtend12 3944) ↦ₘ scratchUn0) **
         ((sp + signExtend12 3936) ↦ₘ scratchMem) **
         (.x1 ↦ᵣ raVal)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_mod_n3_to_loopSetup_spec_within_v4_noNop sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    hbnz' hb3z hb2nz hshift_nz
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [divModStackDispatchPreNoX1_unfold, divScratchValuesCallNoX1_unfold] at hp
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_frameR
      ((.x11 ↦ᵣ v11Old) **
       ((sp + signExtend12 3976) ↦ₘ jMem) **
       ((sp + signExtend12 3968) ↦ₘ retMem) **
         ((sp + signExtend12 3960) ↦ₘ dMem) **
         ((sp + signExtend12 3952) ↦ₘ dloMem) **
         ((sp + signExtend12 3944) ↦ₘ scratchUn0) **
         ((sp + signExtend12 3936) ↦ₘ scratchMem) **
         (.x1 ↦ᵣ raVal))
      (by pcFree)
      hraw)

/-- EvmWord-level wrapper around the n=3 MOD v4/no-NOP path from dispatcher
    entry through the unified loop, preserving the callable `x1` and v4
    scratch frame. -/
theorem evm_mod_n3_preloop_loop_stack_pre_spec_v4_noNop (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hbltu_0 : bltu_0 =
      match bltu_1, hbltu_1 with
      | false, _ =>
        BitVec.ult
          (iterN3Max
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      | true, _ =>
        BitVec.ult
          (iterWithDoubleAddback
            (divKTrialCallV4QHat
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
              (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hcarry2 : Carry2NzAll
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 448)
      base (base + denormOff) (modCode_noNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      ((loopN3UnifiedPostV4NoX1 bltu_1 bltu_0 sp base
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).2.2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).2.2.2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).2.2.2.2
        (0 : Word)
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 2)).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
        ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult (b.getLimbN 2)).1))) := by
  have hSetup := evm_mod_n3_to_loopSetup_stack_pre_spec_v4_noNop
    sp base a b v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2nz hshift_nz
  have hLoop := evm_mod_n3_loop_unified_inst_noNop_exact_x1_v4
    bltu_1 bltu_0 sp base
    (fullDivN3Shift (b.getLimbN 2)) (fullDivN3AntiShift (b.getLimbN 2))
    (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
    (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
    (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
    (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
    (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 2)).1
    (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 2)).2.1
    (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 2)).2.2.1
    (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 2)).2.2.2.1
    (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 2)).2.2.2.2
    (a.getLimbN 0 >>> ((fullDivN3AntiShift (b.getLimbN 2)).toNat % 64))
    v11Old jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    halign hbltu_1 (by cases bltu_1 <;> simpa using hbltu_0) hcarry2
  have hLoopF := cpsTripleWithin_frameR
    ((((sp + 0) ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
      ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
      ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 3992) ↦ₘ (clzResult (b.getLimbN 2)).1)))
    (by pcFree) hLoop
  exact cpsTripleWithin_seq_perm_same_cr
    (loopSetupPost_to_loopN3PreWithScratchV4NoX1_framed sp
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      v11Old jMem retMem dMem dloMem scratchUn0 scratchMem raVal)
    hSetup hLoopF

/-- Compose the n=3 MOD v4 stack precondition through the v4 no-NOP path to the
    v4 final no-`x1` MOD post, preserving the exact caller `x1`. -/
theorem evm_mod_n3_stack_pre_to_unified_post_v4_noNop (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hbltu_0 : bltu_0 =
      match bltu_1, hbltu_1 with
      | false, _ =>
        BitVec.ult
          (iterN3Max
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      | true, _ =>
        BitVec.ult
          (iterWithDoubleAddback
            (divKTrialCallV4QHat
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
              (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hcarry2 : Carry2NzAll
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2) :
    cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 448) + (2 + 23 + 10))
      base (base + nopOff) (modCode_noNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (fullModN3UnifiedPostNoX1V4 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  have hA := evm_mod_n3_preloop_loop_stack_pre_spec_v4_noNop
    sp base a b v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2nz hshift_nz halign hbltu_1 hbltu_0 hcarry2
  have hshift_nz' : fullDivN3Shift (b.getLimbN 2) ≠ 0 := by
    rw [fullDivN3Shift_unfold]
    exact hshift_nz
  have hB := evm_mod_n3_denorm_epilogue_bundled_spec_v4_noNop_v4Final_exact_x1_scratch_frame
    bltu_1 bltu_0 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    retMem dMem dloMem scratchUn0 scratchMem raVal hshift_nz'
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      cases bltu_1 <;> cases bltu_0
      · exact loopN3UnifiedPostV4NoX1_to_fullDivN3DenormPreV4_frame_FF
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN3UnifiedPostV4NoX1_to_fullDivN3DenormPreV4_frame_FT
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN3UnifiedPostV4NoX1_to_fullDivN3DenormPreV4_frame_TF
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN3UnifiedPostV4NoX1_to_fullDivN3DenormPreV4_frame_TT
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp)
    hA hB
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hq => hq)
    hFull

/-- Legacy raw-carry path through denormalization to the v4 final no-`x1`
    post, preserving the exact caller `x1`. -/
theorem evm_div_n3_stack_pre_to_unified_post_v4_noNop (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hbltu_0 : bltu_0 =
      match bltu_1, hbltu_1 with
      | false, _ =>
        BitVec.ult
          (iterN3Max
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      | true, _ =>
        BitVec.ult
          (iterWithDoubleAddback
            (divKTrialCallV4QHat
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
              (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hcarry2 : Carry2NzAll
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2) :
    cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 448) + (2 + 23 + 10))
      base (base + nopOff) (divCode_noNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (fullDivN3UnifiedPostNoX1V4 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  have hA := evm_div_n3_preloop_loop_stack_pre_spec_v4_noNop
    sp base a b v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2nz hshift_nz halign hbltu_1 hbltu_0 hcarry2
  have hshift_nz' : fullDivN3Shift (b.getLimbN 2) ≠ 0 := by
    rw [fullDivN3Shift_unfold]
    exact hshift_nz
  have hBNoNop := evm_div_n3_denorm_epilogue_bundled_spec_v4_noNop_v4Final_exact_x1_scratch_frame
    bltu_1 bltu_0 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    retMem dMem dloMem scratchUn0 scratchMem raVal hshift_nz'
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      cases bltu_1 <;> cases bltu_0
      · exact loopN3UnifiedPostV4NoX1_to_fullDivN3DenormPreV4_frame_FF
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN3UnifiedPostV4NoX1_to_fullDivN3DenormPreV4_frame_FT
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN3UnifiedPostV4NoX1_to_fullDivN3DenormPreV4_frame_TF
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN3UnifiedPostV4NoX1_to_fullDivN3DenormPreV4_frame_TT
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp)
    hA hBNoNop
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hq => hq)
    hFull

/-- Legacy full-code form of `evm_div_n3_stack_pre_to_unified_post_v4_noNop`. -/
theorem evm_div_n3_stack_pre_to_unified_post_v4 (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hbltu_0 : bltu_0 =
      match bltu_1, hbltu_1 with
      | false, _ =>
        BitVec.ult
          (iterN3Max
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      | true, _ =>
        BitVec.ult
          (iterWithDoubleAddback
            (divKTrialCallV4QHat
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
              (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hcarry2 : Carry2NzAll
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2) :
    cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 448) + (2 + 23 + 10))
      base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (fullDivN3UnifiedPostNoX1V4 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (evm_div_n3_stack_pre_to_unified_post_v4_noNop
      sp base a b v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
      hbnz hb3z hb2nz hshift_nz halign hbltu_1 hbltu_0 hcarry2)

/-- Convert the n=3 v4 final post plus exact caller `x1` to the
    exact-register concrete DIV callable surface, preserving the v4 trial-call
    scratch cell that is not part of the public callable post. -/
theorem fullDivN3UnifiedPostNoX1V4_frame_to_divConcretePostNoX1ExactRegsFrame_scratch
    (bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = (0 : Word))
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word)) :
    ∀ h,
      (fullDivN3UnifiedPostNoX1V4 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      (divConcretePostNoX1ExactRegsFrame sp a b
        (signExtend12 4095) raVal
        (signExtend12 (0 : BitVec 12) - fullDivN3Shift b2)
        (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (0 : Word)
        (0 : Word)
        (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (0 : Word)
        (0 : Word)
        (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            (((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat) % 64)))
        (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            (((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat) % 64)))
        (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            (((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat) % 64)))
        ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64))
        (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2
        (fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2
        (0 : Word)
        (0 : Word)
        (fullDivN3Shift b2) (3 : Word) (0 : Word)
        (if bltu_0 then (base + div128CallRetOff)
          else if bltu_1 then (base + div128CallRetOff) else retMem)
        (if bltu_0 then (fullDivN3NormV b0 b1 b2 b3).2.2.1
          else if bltu_1 then (fullDivN3NormV b0 b1 b2 b3).2.2.1 else dMem)
        (if bltu_0 then divKTrialCallV4DLo (fullDivN3NormV b0 b1 b2 b3).2.2.1
          else if bltu_1 then divKTrialCallV4DLo
            (fullDivN3NormV b0 b1 b2 b3).2.2.1 else dloMem)
        (if bltu_0 then divKTrialCallV4Un0
            (fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
          else if bltu_1 then divKTrialCallV4Un0
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          else scratchUn0) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)) h := by
  intro h hq
  let shift := fullDivN3Shift b2
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let r1 := fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  let scratchRet := if bltu_0 then (base + div128CallRetOff)
    else if bltu_1 then (base + div128CallRetOff) else retMem
  let scratchD := if bltu_0 then v.2.2.1
    else if bltu_1 then v.2.2.1 else dMem
  let scratchDLo := if bltu_0 then divKTrialCallV4DLo v.2.2.1
    else if bltu_1 then divKTrialCallV4DLo v.2.2.1 else dloMem
  let scratchUn0' := if bltu_0 then divKTrialCallV4Un0 r1.2.2.1
    else if bltu_1 then divKTrialCallV4Un0 u.2.2.2.1 else scratchUn0
  let u0' := (r0.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.1 <<< (antiShift.toNat % 64))
  let u1' := (r0.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.1 <<< (antiShift.toNat % 64))
  let u2' := (r0.2.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.2.1 <<< (antiShift.toNat % 64))
  let u3' := r0.2.2.2.2.1 >>> (shift.toNat % 64)
  rw [divConcretePostNoX1ExactRegsFrame_unfold]
  change
    ((((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ r0.1) ** (.x10 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) **
     ((.x9 ↦ᵣ (signExtend12 4095 : Word)) ** (.x1 ↦ᵣ raVal) **
      (.x2 ↦ᵣ antiShift) ** (.x6 ↦ᵣ r1.1) ** (.x7 ↦ᵣ (0 : Word)) **
      (.x11 ↦ᵣ r0.1) ** evmWordIs sp a **
      divScratchValuesCallNoX1 sp r0.1 r1.1 (0 : Word) (0 : Word)
        u0' u1' u2' u3' r0.2.2.2.2.2 r1.2.2.2.2.2
        (0 : Word) (0 : Word) shift (3 : Word) (0 : Word)
        scratchRet scratchD scratchDLo scratchUn0')) **
     ((sp + signExtend12 3936) ↦ₘ
      fullDivN3ScratchMemV4 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)) h
  delta fullDivN3UnifiedPostNoX1V4 fullDivN3DenormPostV4 fullDivN3FrameNoX1V4
    fullDivN3ScratchNoX1V4 at hq
  simp only [denormDivPost_unfold] at hq
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3))
      from by rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3]]
  rw [show evmWordIs (sp + 32) (EvmWord.div a b) =
      (((sp + 32) ↦ₘ
          (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1) **
       ((sp + 40) ↦ₘ
          (fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1) **
       ((sp + 48) ↦ₘ (0 : Word)) **
       ((sp + 56) ↦ₘ (0 : Word)))
      from by
        rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
          hdiv0 hdiv1 hdiv2 hdiv3]]
  rw [divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

/-- Named callable-frame version of
    `fullDivN3UnifiedPostNoX1V4_frame_to_divConcretePostNoX1ExactRegsFrame_scratch`. -/
theorem fullDivN3UnifiedPostNoX1V4_frame_to_divStackDispatchPostCallableExactFrame_scratch
    (bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = (0 : Word))
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word)) :
    ∀ h,
      (fullDivN3UnifiedPostNoX1V4 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)) h := by
  intro h hp
  rw [divStackDispatchPostCallableExactFrame_unfold]
  have hExact :=
    fullDivN3UnifiedPostNoX1V4_frame_to_divConcretePostNoX1ExactRegsFrame_scratch
      bltu_1 bltu_0 sp base a b
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem
      raVal ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hp
  exact sepConj_mono_left
    (fun h hp => divConcretePostNoX1ExactRegs_weaken_callable_frame sp a b h hp)
    h hExact

/-- Word-quotient form of
    `fullDivN3UnifiedPostNoX1V4_frame_to_divStackDispatchPostCallableExactFrame_scratch`. -/
theorem fullDivN3UnifiedPostNoX1V4_frame_to_divStackDispatchPostCallableExactFrame_scratch_word
    (bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hdivWord : fullDivN3QuotientWordV4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b) :
    ∀ h,
      (fullDivN3UnifiedPostNoX1V4 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) h := by
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    fullDivN3V4_hdivs_of_word_eq bltu_1 bltu_0 a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hdivWord
  exact fullDivN3UnifiedPostNoX1V4_frame_to_divStackDispatchPostCallableExactFrame_scratch
    bltu_1 bltu_0 sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    retMem dMem dloMem scratchUn0 scratchMem raVal
    rfl rfl rfl rfl hdiv0 hdiv1 hdiv2 hdiv3

/-- Legacy raw-carry stack precondition through the v4 no-NOP path to the
    public callable DIV post, keeping the v4 trial-call scratch cell framed. -/
theorem evm_div_n3_stack_pre_to_callable_post_v4_scratch_noNop (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hbltu_0 : bltu_0 =
      match bltu_1, hbltu_1 with
      | false, _ =>
        BitVec.ult
          (iterN3Max
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      | true, _ =>
        BitVec.ult
          (iterWithDoubleAddback
            (divKTrialCallV4QHat
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
              (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hcarry2 : fullDivN3Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN3R0V4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN3R1V4 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = (0 : Word))
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word)) :
    cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 448) + (2 + 23 + 10))
      base (base + nopOff) (divCode_noNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun h hq =>
      fullDivN3UnifiedPostNoX1V4_frame_to_divStackDispatchPostCallableExactFrame_scratch
        bltu_1 bltu_0 sp base a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem raVal
        rfl rfl rfl rfl hdiv0 hdiv1 hdiv2 hdiv3 h hq)
    (evm_div_n3_stack_pre_to_unified_post_v4_noNop
      sp base a b v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
      hbnz hb3z hb2nz hshift_nz halign hbltu_1 hbltu_0 hcarry2)

/-- Legacy quotient-word version of
    `evm_div_n3_stack_pre_to_callable_post_v4_scratch_noNop`.
    It still consumes the legacy carry package; prefer selected wrappers. -/
theorem evm_div_n3_stack_pre_to_callable_post_v4_scratch_word (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hbltu_0 : bltu_0 =
      match bltu_1, hbltu_1 with
      | false, _ =>
        BitVec.ult
          (iterN3Max
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      | true, _ =>
        BitVec.ult
          (iterWithDoubleAddback
            (divKTrialCallV4QHat
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
              (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
              (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
    (hcarry2 : Carry2NzAll
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2)
    (hdivWord : fullDivN3QuotientWordV4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b) :
    cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 448) + (2 + 23 + 10))
      base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4 <|
    cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun h hq =>
        fullDivN3UnifiedPostNoX1V4_frame_to_divStackDispatchPostCallableExactFrame_scratch_word
          bltu_1 bltu_0 sp base a b
          retMem dMem dloMem scratchUn0 scratchMem raVal hdivWord h hq)
      (evm_div_n3_stack_pre_to_unified_post_v4_noNop
        sp base a b v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
        hbnz hb3z hb2nz hshift_nz halign hbltu_1 hbltu_0 hcarry2)

/-- Legacy arithmetic-assumption version of
    `evm_div_n3_stack_pre_to_callable_post_v4_scratch_word`. -/
theorem evm_div_n3_stack_pre_to_callable_post_v4_scratch_of_mulsub_overestimate
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hpath : fullDivN3PathConditionsWordV4 bltu_1 bltu_0 a b) :
    cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 448) + (2 + 23 + 10))
      base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) := by
  have hbltu_1 := fullDivN3PathConditionsWordV4_trial_j1
    bltu_1 bltu_0 a b hpath
  have hbltu_0 := fullDivN3PathConditionsWordV4_trial_j0
    bltu_1 bltu_0 a b hpath
  have hcarry2 := fullDivN3PathConditionsWordV4_carry2
    bltu_1 bltu_0 a b hpath
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hdivWord :=
    fullDivN3QuotientWordV4_eq_div_of_word_path_conditions
      bltu_1 bltu_0 a b hbnz' hpath
  exact evm_div_n3_stack_pre_to_callable_post_v4_scratch_word
    sp base a b v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2nz hshift_nz halign hbltu_1
    (by cases bltu_1 <;> simpa [isTrialN3V4_j0] using hbltu_0)
    hcarry2 hdivWord

/-- Lift the N3 v4 stack-pre/callable-post path to the shared
    `unifiedDivBound` used by dispatcher-facing stack specs, over the no-NOP
    v4 body expected by callable wrappers. -/
theorem evm_div_n3_stack_pre_to_callable_post_v4_scratch_noNop_bound_unified
    {P Q : Assertion} (base : Word)
    (h :
      cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 448) + (2 + 23 + 10))
        base (base + nopOff) (divCode_noNop_v4 base) P Q) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v4 base) P Q := by
  exact cpsTripleWithin_mono_nSteps (by unfold unifiedDivBound; decide) h

/-- Full-code form of
    `evm_div_n3_stack_pre_to_callable_post_v4_scratch_noNop_bound_unified`. -/
theorem evm_div_n3_stack_pre_to_callable_post_v4_scratch_bound_unified
    {P Q : Assertion} (base : Word)
    (h :
      cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 448) + (2 + 23 + 10))
        base (base + nopOff) (divCode_v4 base) P Q) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v4 base) P Q := by
  exact cpsTripleWithin_mono_nSteps (by unfold unifiedDivBound; decide) h

end EvmAsm.Evm64
