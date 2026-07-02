/-
  EvmAsm.Evm64.DivMod.Compose.DivCallableV5Assembly

  M2 infrastructure for `evm_div_callable_v5` full correctness: the x9-OWNED
  callable post (sheds the concrete `x9Out` to `regOwn .x9`, so the divisor-shape
  lanes — bzero leaves `x9 = x9In`, nonzero lanes leave `signExtend12 4095` — can be
  combined under a single uniform post), plus the x9-owned twins of the 5-lane
  scaffold and the layer-1 scratch return adapter.

  The final assembly (`refine`-ing the x9-owned scaffold with `v2 := divDispatchShiftX2 b`
  and discharging the 5 lanes, then applying the x9-owned adapter) lands the callable
  correctness spec over `evm_div_callable_code_v5`; it mirrors the dispatched
  `FullPathV5DivAssembly` (`evm_div_stack_spec_unconditional_v5_div_of_n4lane`).
-/

import EvmAsm.Evm64.DivMod.Compose.CallableV5DivScratchAdapter
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5DivCallable
import EvmAsm.Evm64.DivMod.Spec.DivDispatchShift
import EvmAsm.Evm64.DivMod.Spec.BzeroV5CallableExact
import EvmAsm.Evm64.DivMod.Spec.N2V5CallableExactOfShape
import EvmAsm.Evm64.DivMod.Spec.N3V5CallableExact
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5CallableExactShift0
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5CallableExact

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Public no-NOP DIV callable post with exact caller-framed `x1` but with `x9`
    merely OWNED (shed).  This is the uniform post the five divisor-shape lanes
    can all land after weakening their concrete `x9Out` — bzero's `x9 = x9In` and
    the nonzero lanes' `x9 = signExtend12 4095` both weaken to `regOwn .x9`. -/
@[irreducible]
def divStackDispatchPostCallableX9Owned
    (sp : Word) (a b : EvmWord) (raVal : Word) : Assertion :=
  (divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) ** regOwn .x9

theorem divStackDispatchPostCallableX9Owned_unfold
    {sp : Word} {a b : EvmWord} {raVal : Word} :
    divStackDispatchPostCallableX9Owned sp a b raVal =
      ((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) ** regOwn .x9) := by
  delta divStackDispatchPostCallableX9Owned
  rfl

theorem divStackDispatchPostCallableX9Owned_pcFree
    (sp : Word) (a b : EvmWord) (raVal : Word) :
    (divStackDispatchPostCallableX9Owned sp a b raVal).pcFree := by
  rw [divStackDispatchPostCallableX9Owned_unfold,
    divStackDispatchPostCallable_unfold, divScratchOwnCallNoX1_unfold]
  pcFree

/-- Shed the exact `x9Out` of the callable ExactFrame post to `regOwn .x9`,
    carrying the `sp+3936` scratch cell.  The bridge that lets any concrete-`x9`
    lane feed the x9-owned scaffold. -/
theorem divStackDispatchPostCallableExactFrame_scratch_to_X9Owned
    (sp : Word) (a b : EvmWord) (raVal x9Out : Word) :
    ∀ h : PartialState,
      (divStackDispatchPostCallableExactFrame sp a b raVal x9Out **
        memOwn (sp + signExtend12 3936)) h →
      (divStackDispatchPostCallableX9Owned sp a b raVal **
        memOwn (sp + signExtend12 3936)) h := by
  intro h hp
  rw [divStackDispatchPostCallableExactFrame_unfold] at hp
  rw [divStackDispatchPostCallableX9Owned_unfold]
  exact sepConj_mono
    (sepConj_mono (fun _ hc => hc) (regIs_implies_regOwn .x9))
    (fun _ hc => hc) h hp

/-- x9-owned twin of `evm_div_stack_spec_unconditional_of_lanes_v5_div_callableExact`:
    same `DivisorLimbCase.elim_named` dispatch, but every lane (and the result)
    lands the x9-owned callable post.  Combinator toward `evm_div_callable_v5`. -/
theorem evm_div_stack_spec_unconditional_of_lanes_v5_div_callableX9Owned
    (sp base : Word) (a b : EvmWord)
    (x9In raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (lane_bzero : b = 0 →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostCallableX9Owned sp a b raVal **
         memOwn (sp + signExtend12 3936)))
    (lane_n1 : N1ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostCallableX9Owned sp a b raVal **
         memOwn (sp + signExtend12 3936)))
    (lane_n2 : N2ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostCallableX9Owned sp a b raVal **
         memOwn (sp + signExtend12 3936)))
    (lane_n3 : N3ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostCallableX9Owned sp a b raVal **
         memOwn (sp + signExtend12 3936)))
    (lane_n4 : N4ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostCallableX9Owned sp a b raVal **
         memOwn (sp + signExtend12 3936))) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableX9Owned sp a b raVal **
       memOwn (sp + signExtend12 3936)) := by
  refine DivisorLimbCase.elim_named
    (P := fun b' => cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b' x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableX9Owned sp a b' raVal **
       memOwn (sp + signExtend12 3936)))
    b ?bzero ?n1 ?n2 ?n3 ?n4
  case bzero => exact lane_bzero
  case n1 => exact lane_n1
  case n2 => exact lane_n2
  case n3 => exact lane_n3
  case n4 => exact lane_n4

/-- x9-owned twin of `evm_div_callable_v5_spec_from_noNop_exact_frame_scratch`:
    extends the x9-owned div body triple onto `evm_div_callable_code_v5` and appends
    the `cc_ret` return, landing the x9-owned callable post. -/
theorem evm_div_callable_v5_spec_from_noNop_X9Owned_scratch
    (sp base x9In raVal : Word) (a b : EvmWord)
    (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b
          x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostCallableX9Owned sp a b raVal **
         memOwn (sp + signExtend12 3936))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableX9Owned sp a b raVal **
       memOwn (sp + signExtend12 3936)) := by
  rw [divStackDispatchPostCallableX9Owned_unfold] at hStack ⊢
  have hStackCall :=
    cpsTripleWithin_extend_code
      (hmono := divCode_noNop_v5_sub_div_callable_code_v5) hStack
  have hStackForRet :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (evm_div_callable_code_v5 base)
        (divModStackDispatchPreNoX1 sp a b
          x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (((divStackDispatchPostCallable sp a b ** regOwn .x9) **
            memOwn (sp + signExtend12 3936)) ** (.x1 ↦ᵣ raVal)) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by xperm_hyp hp) hStackCall
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_div_callable_code_v5_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL
      ((divStackDispatchPostCallable sp a b ** regOwn .x9) **
        memOwn (sp + signExtend12 3936))
      (by
        rw [divStackDispatchPostCallable_unfold, divScratchOwnCallNoX1_unfold,
          divScratchOwn_unfold]
        pcFree)
      hRet
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_same_cr hStackForRet hRetFramed)

/-- **`evm_div_callable_v5` full correctness** (x9-owned callable post): for every
    divisor shape, the callable code takes the callable dispatch pre with a FREE
    incoming `x9In` (and the uniform dispatch shift `divDispatchShiftX2 b` in `x2`)
    to the x9-owned callable return post.  Assembles the five `x9In`-generic
    divisor-shape lanes through the x9-owned scaffold and layer-1 adapter, mirroring
    the dispatched `evm_div_stack_spec_unconditional_v5_div_of_n4lane`. -/
theorem evm_div_callable_v5_stack_spec_within_x9owned
    (sp base : Word) (a b : EvmWord)
    (x9In raVal v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal (divDispatchShiftX2 b) v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableX9Owned sp a b raVal **
       memOwn (sp + signExtend12 3936)) := by
  have hStack :=
    evm_div_stack_spec_unconditional_of_lanes_v5_div_callableX9Owned sp base a b
      x9In raVal (divDispatchShiftX2 b) v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
      -- bzero: v2 is free in the bzero lane; its post keeps x9 = x9In, shed to owned
      (fun hbz =>
        cpsTripleWithin_weaken (fun _ hp => hp)
          (divStackDispatchPostCallableExactFrame_scratch_to_X9Owned sp a b raVal x9In)
          (evm_div_bzero_stack_spec_noNop_v5_preNoX1_callableExactFrame sp base a b
            x9In raVal (divDispatchShiftX2 b) v5 v6 v7 v10 v11
            q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
            nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem hbz))
      -- n1
      (fun hshape => by
        rw [divDispatchShiftX2_n1 hshape]
        exact cpsTripleWithin_weaken (fun _ hp => hp)
          (divStackDispatchPostCallableExactFrame_scratch_to_X9Owned sp a b raVal
            (signExtend12 4095 : Word))
          (evm_div_n1_stack_spec_noNop_v5_preNoX1_callableExactFrame_of_shape sp base a b
            v5 v6 v7 v10 v11 raVal x9In
            q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
            nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
            (by rw [hshape.2.1, hshape.2.2.1, hshape.2.2.2.1]; simpa using hshape.2.2.2.2)
            hshape.2.1 hshape.2.2.1 hshape.2.2.2.1 halign))
      -- n2
      (fun hshape => by
        rw [divDispatchShiftX2_n2 hshape]
        exact cpsTripleWithin_weaken (fun _ hp => hp)
          (divStackDispatchPostCallableExactFrame_scratch_to_X9Owned sp a b raVal
            (signExtend12 4095 : Word))
          (evm_div_n2_stack_spec_noNop_v5_preNoX1_callableExactFrame_of_shape sp base a b
            raVal v5 v6 v7 v10 v11 x9In
            q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
            nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
            hshape.1 hshape.2.1 hshape.2.2.1 hshape.2.2.2 halign))
      -- n3
      (fun hshape => by
        rw [divDispatchShiftX2_n3 hshape]
        exact cpsTripleWithin_weaken (fun _ hp => hp)
          (divStackDispatchPostCallableExactFrame_scratch_to_X9Owned sp a b raVal
            (signExtend12 4095 : Word))
          (evm_div_n3_stack_spec_noNop_v5_preNoX1_callableExactFrame_of_shape sp base a b
            raVal v5 v6 v7 v10 v11 x9In
            q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
            nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
            hshape.2.1 hshape.2.2 halign))
      -- n4
      (fun hshape => by
        rw [divDispatchShiftX2_n4 hshape]
        exact cpsTripleWithin_weaken (fun _ hp => hp)
          (divStackDispatchPostCallableExactFrame_scratch_to_X9Owned sp a b raVal
            (signExtend12 4095 : Word))
          (evm_div_n4_stack_spec_noNop_v5_preNoX1_callableExactFrame_of_shape sp base a b
            raVal v5 v6 v7 v10 v11 x9In
            q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
            nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
            hshape.2 halign))
  exact evm_div_callable_v5_spec_from_noNop_X9Owned_scratch sp base x9In raVal a b
    (divDispatchShiftX2 b) v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem hStack

/-- **Discharged body-layer x9-owned DIV result** (the `hStack` from
    `evm_div_callable_v5_stack_spec_within_x9owned`, extracted standalone).  Over
    `divCode_noNop_v5 base`, bound `unifiedDivBound`, the callable dispatch pre
    (free `x9In`, uniform shift `divDispatchShiftX2 b` in x2) reaches the x9-owned
    callable post — BEFORE the cc_ret / scratch adapter.  This is the body-layer
    feed for the SDIV `hStack` (M3): SDIV's divCall-return handoff composes the
    cc_ret itself, so it needs this body triple, not the full callable spec. -/
theorem evm_div_body_v5_div_callableX9Owned_of_shape
    (sp base : Word) (a b : EvmWord)
    (x9In raVal v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal (divDispatchShiftX2 b) v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableX9Owned sp a b raVal **
       memOwn (sp + signExtend12 3936)) := by
  exact evm_div_stack_spec_unconditional_of_lanes_v5_div_callableX9Owned sp base a b
    x9In raVal (divDispatchShiftX2 b) v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
    (fun hbz =>
      cpsTripleWithin_weaken (fun _ hp => hp)
        (divStackDispatchPostCallableExactFrame_scratch_to_X9Owned sp a b raVal x9In)
        (evm_div_bzero_stack_spec_noNop_v5_preNoX1_callableExactFrame sp base a b
          x9In raVal (divDispatchShiftX2 b) v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem hbz))
    (fun hshape => by
      rw [divDispatchShiftX2_n1 hshape]
      exact cpsTripleWithin_weaken (fun _ hp => hp)
        (divStackDispatchPostCallableExactFrame_scratch_to_X9Owned sp a b raVal
          (signExtend12 4095 : Word))
        (evm_div_n1_stack_spec_noNop_v5_preNoX1_callableExactFrame_of_shape sp base a b
          v5 v6 v7 v10 v11 raVal x9In
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
          (by rw [hshape.2.1, hshape.2.2.1, hshape.2.2.2.1]; simpa using hshape.2.2.2.2)
          hshape.2.1 hshape.2.2.1 hshape.2.2.2.1 halign))
    (fun hshape => by
      rw [divDispatchShiftX2_n2 hshape]
      exact cpsTripleWithin_weaken (fun _ hp => hp)
        (divStackDispatchPostCallableExactFrame_scratch_to_X9Owned sp a b raVal
          (signExtend12 4095 : Word))
        (evm_div_n2_stack_spec_noNop_v5_preNoX1_callableExactFrame_of_shape sp base a b
          raVal v5 v6 v7 v10 v11 x9In
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
          hshape.1 hshape.2.1 hshape.2.2.1 hshape.2.2.2 halign))
    (fun hshape => by
      rw [divDispatchShiftX2_n3 hshape]
      exact cpsTripleWithin_weaken (fun _ hp => hp)
        (divStackDispatchPostCallableExactFrame_scratch_to_X9Owned sp a b raVal
          (signExtend12 4095 : Word))
        (evm_div_n3_stack_spec_noNop_v5_preNoX1_callableExactFrame_of_shape sp base a b
          raVal v5 v6 v7 v10 v11 x9In
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
          hshape.2.1 hshape.2.2 halign))
    (fun hshape => by
      rw [divDispatchShiftX2_n4 hshape]
      exact cpsTripleWithin_weaken (fun _ hp => hp)
        (divStackDispatchPostCallableExactFrame_scratch_to_X9Owned sp a b raVal
          (signExtend12 4095 : Word))
        (evm_div_n4_stack_spec_noNop_v5_preNoX1_callableExactFrame_of_shape sp base a b
          raVal v5 v6 v7 v10 v11 x9In
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
          hshape.2 halign))

end EvmAsm.Evm64
