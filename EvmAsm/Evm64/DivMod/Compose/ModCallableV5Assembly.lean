/-
  EvmAsm.Evm64.DivMod.Compose.ModCallableV5Assembly

  M4 infrastructure for `evm_mod_callable_v5` full correctness: the x9-OWNED MOD
  callable post, the x9-owned twins of the 5-lane scaffold and the layer-1 scratch
  return adapter, and the final assembly.  Mechanical mirror of
  `DivCallableV5Assembly` (div→mod), landing the callable correctness spec over
  `evm_mod_callable_code_v5`.  Toward SMOD `.proven`.

  The one asymmetry vs the DIV assembly: the MOD bzero lane
  (`evm_mod_stack_spec_bzero_noNop_v5_preNoX1_callableExactFrame`) does not carry
  the `sp+3936` div128 scratch cell (the b=0 path never calls div128), so its
  scaffold hypothesis frames the cell on explicitly; the nonzero lanes carry it.
-/

import EvmAsm.Evm64.DivMod.CallableV5Mod
import EvmAsm.Evm64.DivMod.Spec.ModBzeroV5CallableExact
import EvmAsm.Evm64.DivMod.Spec.N2V5CallableExactOfShapeMod
import EvmAsm.Evm64.DivMod.Spec.N3V5CallableExactMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5CallableExactShift0Mod
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5CallableExactMod

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Public no-NOP MOD callable post with exact caller-framed `x1` but `x9` merely
    OWNED (shed) — the uniform post the five divisor-shape lanes land after
    weakening their concrete `x9Out`. -/
@[irreducible]
def modStackDispatchPostCallableX9Owned
    (sp : Word) (a b : EvmWord) (raVal : Word) : Assertion :=
  (modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) ** regOwn .x9

theorem modStackDispatchPostCallableX9Owned_unfold
    {sp : Word} {a b : EvmWord} {raVal : Word} :
    modStackDispatchPostCallableX9Owned sp a b raVal =
      ((modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) ** regOwn .x9) := by
  delta modStackDispatchPostCallableX9Owned
  rfl

theorem modStackDispatchPostCallableX9Owned_pcFree
    (sp : Word) (a b : EvmWord) (raVal : Word) :
    (modStackDispatchPostCallableX9Owned sp a b raVal).pcFree := by
  rw [modStackDispatchPostCallableX9Owned_unfold,
    modStackDispatchPostCallable_unfold, divScratchOwnCallNoX1_unfold,
    divScratchOwn_unfold]
  pcFree

/-- Shed the exact `x9Out` of the MOD callable ExactFrame post to `regOwn .x9`,
    carrying the `sp+3936` scratch cell. -/
theorem modStackDispatchPostCallableExactFrame_scratch_to_X9Owned
    (sp : Word) (a b : EvmWord) (raVal x9Out : Word) :
    ∀ h : PartialState,
      (modStackDispatchPostCallableExactFrame sp a b raVal x9Out **
        memOwn (sp + signExtend12 3936)) h →
      (modStackDispatchPostCallableX9Owned sp a b raVal **
        memOwn (sp + signExtend12 3936)) h := by
  intro h hp
  rw [modStackDispatchPostCallableExactFrame_unfold] at hp
  rw [modStackDispatchPostCallableX9Owned_unfold]
  exact sepConj_mono
    (sepConj_mono (fun _ hc => hc) (regIs_implies_regOwn .x9))
    (fun _ hc => hc) h hp

/-- x9-owned twin of the MOD 5-lane callable scaffold. -/
theorem evm_mod_stack_spec_unconditional_of_lanes_v5_mod_callableX9Owned
    (sp base : Word) (a b : EvmWord)
    (x9In raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (lane_bzero : b = 0 →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (modStackDispatchPostCallableX9Owned sp a b raVal **
         memOwn (sp + signExtend12 3936)))
    (lane_n1 : N1ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (modStackDispatchPostCallableX9Owned sp a b raVal **
         memOwn (sp + signExtend12 3936)))
    (lane_n2 : N2ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (modStackDispatchPostCallableX9Owned sp a b raVal **
         memOwn (sp + signExtend12 3936)))
    (lane_n3 : N3ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (modStackDispatchPostCallableX9Owned sp a b raVal **
         memOwn (sp + signExtend12 3936)))
    (lane_n4 : N4ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (modStackDispatchPostCallableX9Owned sp a b raVal **
         memOwn (sp + signExtend12 3936))) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableX9Owned sp a b raVal **
       memOwn (sp + signExtend12 3936)) := by
  refine DivisorLimbCase.elim_named
    (P := fun b' => cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b' x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableX9Owned sp a b' raVal **
       memOwn (sp + signExtend12 3936)))
    b ?bzero ?n1 ?n2 ?n3 ?n4
  case bzero => exact lane_bzero
  case n1 => exact lane_n1
  case n2 => exact lane_n2
  case n3 => exact lane_n3
  case n4 => exact lane_n4

/-- x9-owned layer-1 MOD scratch adapter: extends the x9-owned mod body triple
    onto `evm_mod_callable_code_v5` and appends `cc_ret`. -/
theorem evm_mod_callable_v5_spec_from_noNop_X9Owned_scratch
    (sp base x9In raVal : Word) (a b : EvmWord)
    (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b
          x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (modStackDispatchPostCallableX9Owned sp a b raVal **
         memOwn (sp + signExtend12 3936))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableX9Owned sp a b raVal **
       memOwn (sp + signExtend12 3936)) := by
  rw [modStackDispatchPostCallableX9Owned_unfold] at hStack ⊢
  have hStackCall :=
    cpsTripleWithin_extend_code
      (hmono := modCode_noNop_v5_sub_mod_callable_code_v5) hStack
  have hStackForRet :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (evm_mod_callable_code_v5 base)
        (divModStackDispatchPreNoX1 sp a b
          x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (((modStackDispatchPostCallable sp a b ** regOwn .x9) **
            memOwn (sp + signExtend12 3936)) ** (.x1 ↦ᵣ raVal)) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by xperm_hyp hp) hStackCall
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_mod_callable_code_v5_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL
      ((modStackDispatchPostCallable sp a b ** regOwn .x9) **
        memOwn (sp + signExtend12 3936))
      (by
        rw [modStackDispatchPostCallable_unfold, divScratchOwnCallNoX1_unfold,
          divScratchOwn_unfold]
        pcFree)
      hRet
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_same_cr hStackForRet hRetFramed)

/-- **Discharged body-layer x9-owned MOD result** — the `hStack` feed for the
    SMOD handoff (M4 flip). Over `modCode_noNop_v5`, bound `unifiedDivBound`, from
    the callable dispatch pre (free `x9In`, free incoming `x2`/`v2`) to the
    x9-owned callable post, BEFORE the cc_ret / scratch adapter. -/
theorem evm_mod_body_v5_mod_callableX9Owned_of_shape
    (sp base : Word) (a b : EvmWord)
    (x9In raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableX9Owned sp a b raVal **
       memOwn (sp + signExtend12 3936)) := by
  refine evm_mod_stack_spec_unconditional_of_lanes_v5_mod_callableX9Owned sp base a b
    x9In raVal v2 v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
    ?bzero ?n1 ?n2 ?n3 ?n4
  case bzero =>
    intro hbz
    have hb := cpsTripleWithin_frameR ((sp + signExtend12 3936) ↦ₘ scratchMem)
      (by pcFree)
      (evm_mod_stack_spec_bzero_noNop_v5_preNoX1_callableExactFrame sp base a b
        x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0 hbz)
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hp => modStackDispatchPostCallableExactFrame_scratch_to_X9Owned sp a b raVal x9In h
        (sepConj_mono (fun _ hc => hc) memIs_implies_memOwn h hp))
      hb
  case n1 =>
    intro hshape
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (modStackDispatchPostCallableExactFrame_scratch_to_X9Owned sp a b raVal
        (signExtend12 4095 : Word))
      (evm_mod_n1_stack_spec_noNop_v5_preNoX1_callableExactFrame_of_shape sp base a b
        v5 v6 v7 v10 v11 raVal x9In v2
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
        (by rw [hshape.2.1, hshape.2.2.1, hshape.2.2.2.1]; simpa using hshape.2.2.2.2)
        hshape.2.1 hshape.2.2.1 hshape.2.2.2.1 halign)
  case n2 =>
    intro hshape
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (modStackDispatchPostCallableExactFrame_scratch_to_X9Owned sp a b raVal
        (signExtend12 4095 : Word))
      (evm_mod_n2_stack_spec_noNop_v5_preNoX1_callableExactFrame_of_shape sp base a b
        raVal v5 v6 v7 v10 v11 x9In v2
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
        hshape.1 hshape.2.1 hshape.2.2.1 hshape.2.2.2 halign)
  case n3 =>
    intro hshape
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (modStackDispatchPostCallableExactFrame_scratch_to_X9Owned sp a b raVal
        (signExtend12 4095 : Word))
      (evm_mod_n3_stack_spec_noNop_v5_preNoX1_callableExactFrame_of_shape sp base a b
        raVal v5 v6 v7 v10 v11 x9In v2
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
        hshape.2.1 hshape.2.2 halign)
  case n4 =>
    intro hshape
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (modStackDispatchPostCallableExactFrame_scratch_to_X9Owned sp a b raVal
        (signExtend12 4095 : Word))
      (evm_mod_n4_stack_spec_noNop_v5_preNoX1_callableExactFrame_of_shape sp base a b
        raVal v5 v6 v7 v10 v11 x9In v2
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
        hshape.2 halign)

/-- **`evm_mod_callable_v5` full correctness** (x9-owned callable post): the mod
    callable code takes the callable dispatch pre (FREE `x9In`, FREE `x2`/`v2`) to
    the x9-owned callable return post, for every divisor shape. -/
theorem evm_mod_callable_v5_stack_spec_within_x9owned
    (sp base : Word) (a b : EvmWord)
    (x9In raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableX9Owned sp a b raVal **
       memOwn (sp + signExtend12 3936)) := by
  exact evm_mod_callable_v5_spec_from_noNop_X9Owned_scratch sp base x9In raVal a b
    v2 v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
    (evm_mod_body_v5_mod_callableX9Owned_of_shape sp base a b
      x9In raVal v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem halign)

end EvmAsm.Evm64
