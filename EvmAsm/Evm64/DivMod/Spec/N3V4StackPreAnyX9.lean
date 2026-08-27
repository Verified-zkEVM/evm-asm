/-
  EvmAsm.Evm64.DivMod.Spec.N3V4StackPreAnyX9

  MOD n=3 anyX9 variants: the loop-setup instruction overwrites x9 ← 4-n
  before the loop body, so the initial x9 value is irrelevant.  This file
  contains generalisations of the stack-level n=3 MOD path theorems that
  accept an arbitrary initial x9 value in the precondition.

  Split out from N3V4StackPre.lean to stay within the 1500-line file-size cap.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N3V4StackPre

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- Generalization of `evm_mod_n3_to_loopSetup_stack_pre_spec_v4_noNop`
    allowing any initial `x9` value. -/
theorem evm_mod_n3_to_loopSetup_stack_pre_spec_v4_noNop_anyX9 (sp base : Word)
    (x9Init : Word)
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
        x9Init raVal
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
  have hraw := evm_mod_n3_to_loopSetup_spec_within_v4_noNop_anyX9 sp base x9Init
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

/-- Legacy raw-carry generalization of
    `evm_mod_n3_preloop_loop_stack_pre_spec_v4_noNop`, allowing any initial
    `x9` value. Prefer selected-carry wrappers for new v4 work. -/
theorem evm_mod_n3_preloop_loop_stack_pre_spec_v4_noNop_anyX9 (sp base : Word)
    (x9Init : Word)
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
        x9Init raVal
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
  have hSetup := evm_mod_n3_to_loopSetup_stack_pre_spec_v4_noNop_anyX9
    sp base x9Init a b v5 v6 v7 v10 v11Old
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

/-- Legacy raw-carry generalization of
    `evm_mod_n3_stack_pre_to_unified_post_v4_noNop`, allowing any initial
    `x9` value. Prefer selected-carry wrappers for new v4 work. -/
theorem evm_mod_n3_stack_pre_to_unified_post_v4_noNop_anyX9 (sp base : Word)
    (x9Init : Word)
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
        x9Init raVal
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
  have hA := evm_mod_n3_preloop_loop_stack_pre_spec_v4_noNop_anyX9
    sp base x9Init a b v5 v6 v7 v10 v11Old
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

end EvmAsm.Evm64
