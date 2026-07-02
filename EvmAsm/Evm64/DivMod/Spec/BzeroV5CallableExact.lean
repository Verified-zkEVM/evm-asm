/-
  EvmAsm.Evm64.DivMod.Spec.BzeroV5CallableExact

  Zero-divisor (b = 0) v5 DIV callable-ExactFrame lane — the `lane_bzero`
  hypothesis of the 5-lane callable scaffold
  `evm_div_stack_spec_unconditional_of_lanes_v5_div_callableExact`.

  Mirrors the proven v4 lane (`Spec/UnifiedBzero.lean` /
  `Spec/BzeroV4ExactFrame.lean`) over the v5 body
  `evm_div_bzero_stack_spec_within_noNop_v5` (`Compose/FullPathN1V5Bzero.lean`).

  The b = 0 path is short (8 + 5 steps) and never runs `divK_loopSetup`, so it
  never touches `.x9`: the incoming `x9In` is framed unread all the way through
  and appears UNCHANGED in the post (`x9Out = x9In`).  This DIFFERS from the
  nonzero lanes, whose `loopSetup` leaves `x9 = signExtend12 4095` — so the
  bzero lane's post-x9 is the free incoming value, not a fixed constant.  M2
  assembly must account for this (either the scaffold takes a per-lane x9Out, or
  the callable post sheds x9 to `regOwn`, which SDIV does anyway since its
  return post carries no x9).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Bzero
import EvmAsm.Evm64.DivMod.Spec.UnifiedBzero

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 zero-divisor DIV dispatcher in the concrete callable post shape (no-X1
    pre, `divConcretePostNoX1Frame` post), over `divCode_noNop_v5`.  Verbatim
    mirror of `evm_div_bzero_stack_spec_within_dispatch_noNop_v4_concrete_callable_uni`
    over the v5 body. -/
theorem evm_div_bzero_stack_spec_within_dispatch_noNop_v5_concrete_callable_uni
    (sp base : Word)
    (a b : EvmWord) (x9Val raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0) := by
  let frame : Assertion :=
    (.x9 ↦ᵣ x9Val) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
    (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
    evmWordIs sp a **
    divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0
  have hBzero :=
    evm_div_bzero_stack_spec_within_noNop_v5 sp base a b v5 v10 hbz
  have hFramed :
      cpsTripleWithin (8 + 5) base (base + nopOff) (divCode_noNop_v5 base)
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) b) ** frame)
        ((((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) ** frame)) :=
    cpsTripleWithin_frameR frame (by
      dsimp [frame]
      rw [divScratchValuesCallNoX1_unfold]
      pcFree) hBzero
  exact cpsTripleWithin_mono_nSteps (by decide) <|
    cpsTripleWithin_weaken
      (fun _ hp => by
        rw [divModStackDispatchPreNoX1_unfold] at hp
        dsimp [frame]
        simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
        exact hp)
      (fun h hq => by
        simpa [frame, divConcretePostNoX1Frame_unfold,
          sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq)
      hFramed

/-- The `lane_bzero` hypothesis of the 5-lane callable scaffold: zero-divisor v5
    DIV over `divCode_noNop_v5` landing `divStackDispatchPostCallableExactFrame`
    with the incoming `x9In` unchanged in the post, plus the framed div128
    scratch cell weakened to `memOwn`. -/
theorem evm_div_bzero_stack_spec_noNop_v5_preNoX1_callableExactFrame
    (sp base : Word) (a b : EvmWord)
    (x9In raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal x9In **
       memOwn (sp + signExtend12 3936)) := by
  have hcore :=
    evm_div_bzero_stack_spec_within_dispatch_noNop_v5_concrete_callable_uni
      sp base a b x9In raVal v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 hbz
  have hframed :=
    cpsTripleWithin_frameR ((sp + signExtend12 3936) ↦ₘ scratchMem)
      (by pcFree) hcore
  rw [divStackDispatchPostCallableExactFrame_unfold]
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun h hq =>
      sepConj_mono
        (divConcretePostNoX1_weaken_callable_frame sp a b)
        (fun _ hc => memIs_implies_memOwn _ hc)
        h hq)
    hframed

end EvmAsm.Evm64
