/-
  EvmAsm.Evm64.AddMod.Compose.CarryLb

  Phase-3 M3d for total ADDMOD (issue #9704): the second carry-branch sub-chain.

  Lb runs from La's post (byte 252) through the second MOD call:

    plus_one_args (252,24) ;;
    [adapter call2 : JAL@348 → evm_mod_callable_v5 → ret@352] ;;
    call_mod_restore (352,1)

  ending at byte 356 with `EvmWord.pow256ModN N` at F+32..56 — the `2^256 mod N`
  carry contribution — via the runtime identity `((2^256−1) mod N + 1) mod N`.

  Direct mirror of `CarryLa`, with two additions: a pure `+1` carry-chain
  bridge (`addOne_via_incr_chain`) identifying the `plus_one_args` output with
  `EvmWord.mod (-1) N + 1`, and the `pow256ModN_runtime_construction` rewrite of
  the second remainder to `EvmWord.pow256ModN N`.
-/

import EvmAsm.Evm64.AddMod.Compose.CarryLa

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64

/-- The `plus_one_args` block's four-limb increment carry-chain, applied to the
    limbs of an `EvmWord` `w`, reassembles to `w + 1`. Matches the block's
    `SLTIU`/`SLTU` idiom against the general `add_carry_chain_correct` at
    `b = 1` (whose higher limbs are 0, collapsing the combined carries). -/
theorem addOne_via_incr_chain (w : EvmWord) :
    let m0 := w.getLimbN 0
    let m1 := w.getLimbN 1
    let m2 := w.getLimbN 2
    let m3 := w.getLimbN 3
    let q0 := m0 + (1 : Word)
    let k0 := if BitVec.ult q0 (1 : Word) then (1 : Word) else 0
    let q1 := m1 + k0
    let k1 := if BitVec.ult q1 k0 then (1 : Word) else 0
    let q2 := m2 + k1
    let k2 := if BitVec.ult q2 k1 then (1 : Word) else 0
    let q3 := m3 + k2
    EvmWord.fromLimbs ![q0, q1, q2, q3] = w + 1 := by
  intro m0 m1 m2 m3 q0 k0 q1 k1 q2 k2 q3
  have h := EvmWord.add_carry_chain_correct w (1 : EvmWord)
  have e0 : (1 : EvmWord).getLimb 0 = (1 : Word) := by decide
  have e1 : (1 : EvmWord).getLimb 1 = (0 : Word) := by decide
  have e2 : (1 : EvmWord).getLimb 2 = (0 : Word) := by decide
  have e3 : (1 : EvmWord).getLimb 3 = (0 : Word) := by decide
  simp only [e0, e1, e2, e3,
    show ∀ x : Word, x + (0 : Word) = x from fun x => by simp,
    show ∀ x : Word, BitVec.ult x (0 : Word) = false from fun x => by simp [BitVec.ult]] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  have hfun : (![q0, q1, q2, q3] : Fin 4 → Word) = (w + 1).getLimb := by
    funext i
    fin_cases i
    · simpa [q0, m0, EvmWord.getLimb_eq_getLimbN] using h0.symm
    · simpa [q1, k0, q0, m0, m1, EvmWord.getLimb_eq_getLimbN] using h1.symm
    · simpa [q2, k1, q1, k0, q0, m0, m1, m2, EvmWord.getLimb_eq_getLimbN] using h2.symm
    · simpa [q3, k2, q2, k1, q1, k0, q0, m0, m1, m2, m3, EvmWord.getLimb_eq_getLimbN]
        using h3.symm
  calc EvmWord.fromLimbs ![q0, q1, q2, q3]
      = EvmWord.fromLimbs (w + 1).getLimb := by rw [hfun]
    _ = w + 1 := EvmWord.fromLimbs_getLimb (w + 1)

-- ============================================================================
-- Own → generic-valued conversion for memory cells (Lb needs this: between the
-- MOD calls the div-scratch band is only OWNED, but the next call's adapter
-- pre wants it VALUED; the adapter is generic in every scratch value, so we
-- ∃-eliminate the owned cells and instantiate). Mirror of
-- `cpsTripleWithin_pre_regOwn` / `_under` for `memOwn`.
-- ============================================================================

/-- Choose the concrete value of a leading `memOwn a` in a `cpsTripleWithin`
    precondition. -/
theorem cpsTripleWithin_pre_memOwn
    {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {a : Word} {B Q : Assertion}
    (h : ∀ v, cpsTripleWithin nSteps entry exit_ cr ((a ↦ₘ v) ** B) Q) :
    cpsTripleWithin nSteps entry exit_ cr (memOwn a ** B) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hst, hcompat, hP⟩ := hPR
  have hP' : (memOwn a ** (B ** R)) hst := (sepConj_assoc hst).mp hP
  obtain ⟨v, hv⟩ := sepConj_choose_memOwn hP'
  have hv' : (((a ↦ₘ v) ** B) ** R) hst := (sepConj_assoc hst).mpr hv
  exact h v R hR s hcr ⟨hst, hcompat, hv'⟩ hpc

/-- Choose the concrete value of a `memOwn a` sitting in the SECOND position of a
    precondition (behind a leading `A`). Peels several `memOwn`s out of a chain
    one at a time via `sepConj_left_comm'`. -/
theorem cpsTripleWithin_pre_memOwn_under
    {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {A : Assertion} {a : Word} {B Q : Assertion}
    (h : ∀ v, cpsTripleWithin nSteps entry exit_ cr (A ** ((a ↦ₘ v) ** B)) Q) :
    cpsTripleWithin nSteps entry exit_ cr (A ** (memOwn a ** B)) Q := by
  rw [sepConj_left_comm']
  refine cpsTripleWithin_pre_memOwn (fun v => ?_)
  rw [sepConj_left_comm']
  exact h v

/-- Convert an OWNED div-scratch call band in a `cpsTripleWithin` precondition
    into the generic-VALUED form the MOD-call adapter needs. The 19 scratch
    cells are ∃-eliminated (the adapter is universally generic in every scratch
    value). Peel pattern: `pre_memOwn` for the leading cell, then
    `rw [← sepConj_assoc']; pre_memOwn_under` for each of the remaining 18
    (folding the growing valued prefix into one left-nested block so the next
    owned cell sits in the second slot `_under` can reach). -/
theorem cpsTripleWithin_pre_divScratchValued
    {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq} {F : Word} {B Q : Assertion}
    (h : ∀ q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratch_un0,
      cpsTripleWithin nSteps entry exit_ cr
        (divScratchValuesCallNoX1 F q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 ** B) Q) :
    cpsTripleWithin nSteps entry exit_ cr (divScratchOwnCallNoX1 F ** B) Q := by
  rw [divScratchOwnCallNoX1_unfold, divScratchOwn_unfold]
  simp only [sepConj_assoc']
  refine cpsTripleWithin_pre_memOwn (fun q0 => ?_)
  refine cpsTripleWithin_pre_memOwn_under (fun q1 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun q2 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun q3 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun u0 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun u1 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun u2 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun u3 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun u4 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun u5 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun u6 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun u7 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun shiftMem => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun nMem => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun jMem => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun retMem => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun dMem => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun dloMem => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun scratch_un0 => ?_)
  have hh := h q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0
  rw [divScratchValuesCallNoX1_unfold, divScratchValues_unfold] at hh
  simp only [sepConj_assoc'] at hh ⊢
  exact hh

end EvmAsm.Evm64.AddMod.Compose
