/-
  EvmAsm.Evm64.DivMod.Spec.CallSkipExactX1

  `evm_div_n4_call_skip_stack_spec_exact_x1`: a variant of the standard
  call-skip n=4 DIV stack spec that preserves the concrete post-branch
  `x1` value rather than weakening it to `regOwn`.

  Split from `CallSkip.lean` per issue #1078 (file-size guardrail) to
  keep `CallSkip.lean` below the 1500-line cap.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.CallSkip

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64.Tactics

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)
open EvmWord (val256)

/-- Variant of `evm_div_n4_call_skip_stack_spec` that keeps the concrete
    post-branch `x1` value instead of weakening it to `regOwn`. -/
theorem evm_div_n4_call_skip_stack_spec_exact_x1 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallEvm a b)
    (hsem : n4CallSkipSemanticHolds a b) :
    cpsTripleWithin 264 base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divN4CallSkipStackPostNoX1 sp a b **
        (.x9 ↦ᵣ signExtend12 (4095 : BitVec 12))) := by
  have h_pre := evm_div_n4_full_call_skip_stack_pre_spec_bundled sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hborrow
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    n4_call_skip_div_mod_getLimbN a b hbnz hshift_nz hborrow hsem
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h_pre
  intro h hq
  simp only [fullDivN4CallSkipPost_unfold, denormDivPost_unfold] at hq
  apply div_n4_call_skip_stack_weaken_noX1 sp a b h
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold]
  rw [show evmWordIs (sp + 32) (EvmWord.div a b) =
      (((sp + 32) ↦ₘ (div128Quot ((a.getLimbN 3) >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 3)).1).toNat % 64))
          (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((a.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) -
              (clzResult (b.getLimbN 3)).1).toNat % 64)))
          (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((b.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) -
              (clzResult (b.getLimbN 3)).1).toNat % 64))))) **
       ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) **
       ((sp + 56) ↦ₘ (0 : Word)))
      from by rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
                  hdiv0 hdiv1 hdiv2 hdiv3]]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

end EvmAsm.Evm64
