/-
  Teer auth-loop exit → wouldbe → ret when rolled_back = 0.
  AfterAuthLoopLi (E+724) BEQ taken → AtLoopExit → ret (30 steps).
  Covers empty auth list (idx = count = 0) and loop-done (idx = count).

  Live s7/s8 are the loop idx/count (cur.s7/cur.s8); epi restores saved s7/s8.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerWouldbe
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopBeq
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopField0
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

local macro "pcf" : tactic => `(tactic|
  repeat first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_emp
    | exact pcFree_pure
    | exact pcFree_regsAt _ _
    | exact pcFree_frameSlotsSaved _ _ _
    | exact bytesRegion_pcFree _ _)

/-- Loop-exit BEQ taken + wouldbe(rolled=0) + epi → ret (1+29 = 30 steps).

    Preconditions on `cur`:
    * `cur.s10 = s10Val` (live refund accumulator)
    * `cur.s8 = idx`, `cur.s7 = countW` with `idx = countW` (BEQ taken)
    Epi restores *saved* s7/s8 from the frame (`s.s7`/`s.s8`). -/
theorem teerAuthLoopExitToRet_rolled0
    (sp0 spC : Word) (s cur : TeerSaved)
    (s10Val a0Old a1Old t0Old t1Old refund : Word)
    (hspC : spC = sp0 + signExtend12 (-160 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hcur10 : cur.s10 = s10Val)
    (heq : cur.s8 = cur.s7) :
    cpsTripleWithin 30 AfterAuthLoopLi s.ra teerLinkedField0
      ((.x2 ↦ᵣ spC) **
        regsAt teerEpiFrame (teerSavedVals cur) **
        frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (RegularRefundAddr ↦ₘ refund) **
        memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
        (RolledBackAddr ↦ₘ (0 : Word)))
      ((.x10 ↦ᵣ s10Val) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
        (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
        frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
        (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
        (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (RegularRefundAddr ↦ₘ refund) **
        memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
        (RolledBackAddr ↦ₘ (0 : Word))) := by
  -- BEQ uses live s8/s7 (= cur.s8/cur.s7); peel them out of regsAt.
  have hb0 := teerAuthLoopBeqTaken cur.s8 cur.s7 heq
  have hb := cpsTripleWithin_extend_code teerField0_mono_count hb0
  have hbF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x1 ↦ᵣ cur.ra) ** (.x8 ↦ᵣ cur.s0) ** (.x9 ↦ᵣ cur.s1) **
      (.x18 ↦ᵣ cur.s2) ** (.x19 ↦ᵣ cur.s3) ** (.x20 ↦ᵣ cur.s4) **
      (.x21 ↦ᵣ cur.s5) ** (.x22 ↦ᵣ cur.s6) **
      (.x25 ↦ᵣ cur.s9) ** (.x26 ↦ᵣ cur.s10) ** (.x27 ↦ᵣ cur.s11) **
      frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
      (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (RegularRefundAddr ↦ₘ refund) **
      memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
      (RolledBackAddr ↦ₘ (0 : Word)))
    (by pcf) hb
  have hret0 := teerWouldbeToRet_rolled0 sp0 spC s cur s10Val a0Old a1Old
    t0Old t1Old refund hspC hret hcur10
  -- After BEQ, live s7/s8 remain; wouldbe/epi do not need them as separate
  -- atoms beyond regsAt (epi restores saved s7/s8 from the frame).
  -- hperm: Q1 (hbF post) → Q2 (hret0 prest with regsAt)
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      rw [regsAt_teerEpiFrame]
      simp only [hcur10] at hp ⊢
      xperm_hyp hp) hbF hret0
  -- hpre: theorem prest (regsAt) → hall prest (expanded); expand hyp then xperm
  exact cpsTripleWithin_weaken (fun _ hp => by
      rw [regsAt_teerEpiFrame] at hp
      xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-- Empty auth list (live s8=s7=0) exit → ret when rolled=0. -/
theorem teerEmptyAuthToRet_rolled0
    (sp0 spC : Word) (s cur : TeerSaved)
    (s10Val a0Old a1Old t0Old t1Old refund : Word)
    (hspC : spC = sp0 + signExtend12 (-160 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hcur10 : cur.s10 = s10Val)
    (hcur78 : cur.s8 = (0 : Word) ∧ cur.s7 = (0 : Word)) :
    cpsTripleWithin 30 AfterAuthLoopLi s.ra teerLinkedField0
      ((.x2 ↦ᵣ spC) **
        regsAt teerEpiFrame (teerSavedVals cur) **
        frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (RegularRefundAddr ↦ₘ refund) **
        memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
        (RolledBackAddr ↦ₘ (0 : Word)))
      ((.x10 ↦ᵣ s10Val) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
        (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
        frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
        (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
        (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (RegularRefundAddr ↦ₘ refund) **
        memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
        (RolledBackAddr ↦ₘ (0 : Word))) := by
  have heq : cur.s8 = cur.s7 := by rw [hcur78.1, hcur78.2]
  exact teerAuthLoopExitToRet_rolled0 sp0 spC s cur s10Val a0Old a1Old
    t0Old t1Old refund hspC hret hcur10 heq

#print axioms teerAuthLoopExitToRet_rolled0
#print axioms teerEmptyAuthToRet_rolled0

end EvmAsm.Codegen.TxEip7702TeerSpec
