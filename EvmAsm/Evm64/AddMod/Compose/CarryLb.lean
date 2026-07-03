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
import EvmAsm.Evm64.AddMod.Compose.CarryBranch

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

-- ============================================================================
-- Lb link 1: plus_one_args (byte 252 → 348)
-- ============================================================================

/-- Frame carried through `plus_one_args`: `x0`, the return address, the
    registers untouched by the block (`x2/x9/x10/x11`, still owned from the
    callable return), the S2 (=r) / S3 (=stale m) park cells, and the owned
    div-scratch band + its `F−160` cell. -/
def addmodLbPlusOneFrame (F raVal x2v x9v x10v x11v : Word)
    (r0 r1 r2 r3 sm0 sm1 sm2 sm3 : Word) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
  (.x2 ↦ᵣ x2v) ** (.x9 ↦ᵣ x9v) ** (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) **
  ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ r0) **
  ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ r1) **
  ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ r2) **
  ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ r3) **
  ((F + signExtend12 (3840 : BitVec 12)) ↦ₘ sm0) **
  ((F + signExtend12 (3848 : BitVec 12)) ↦ₘ sm1) **
  ((F + signExtend12 (3856 : BitVec 12)) ↦ₘ sm2) **
  ((F + signExtend12 (3864 : BitVec 12)) ↦ₘ sm3) **
  divScratchOwnCallNoX1 F ** memOwn (F + signExtend12 (3936 : BitVec 12))

theorem addmodLbPlusOneFrame_pcFree (F raVal x2v x9v x10v x11v
    r0 r1 r2 r3 sm0 sm1 sm2 sm3 : Word) :
    (addmodLbPlusOneFrame F raVal x2v x9v x10v x11v
      r0 r1 r2 r3 sm0 sm1 sm2 sm3).pcFree := by
  unfold addmodLbPlusOneFrame divScratchOwnCallNoX1 divScratchOwn
  pcFree

/-- Link 1 of Lb: `plus_one_args` framed, over `C`. Consumes the (owned from
    the callable return) `x5/x6/x7` at generic values, reads the call-1
    remainder limbs `m0..m3` at F+32..56 and the all-ones `w0..w3` at F+0..24,
    reloads `N` from S1, and writes the `+1` increment `q0..q3` into F+0..24. -/
theorem lb_plus_one_in_C
    (bt F raVal x2v x9v x10v x11v : Word)
    (m0 m1 m2 m3 w0 w1 w2 w3 n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3 : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word) :
    let q0 := m0 + signExtend12 (1 : BitVec 12)
    let k0 := if BitVec.ult q0 (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0
    let q1 := m1 + k0
    let k1 := if BitVec.ult q1 k0 then (1 : Word) else 0
    let q2 := m2 + k1
    let k2 := if BitVec.ult q2 k1 then (1 : Word) else 0
    let q3 := m3 + k2
    let k3 := if BitVec.ult q3 k2 then (1 : Word) else 0
    cpsTripleWithin 24 (bt + 252) ((bt + 252) + 96)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        ((F + signExtend12 (32 : BitVec 12)) ↦ₘ m0) **
        ((F + signExtend12 (40 : BitVec 12)) ↦ₘ m1) **
        ((F + signExtend12 (48 : BitVec 12)) ↦ₘ m2) **
        ((F + signExtend12 (56 : BitVec 12)) ↦ₘ m3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ w0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ w1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ w2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ w3) **
        ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ n3)) **
       addmodLbPlusOneFrame F raVal x2v x9v x10v x11v r0 r1 r2 r3 sm0 sm1 sm2 sm3)
      (((.x12 ↦ᵣ F) ** (.x5 ↦ᵣ n3) ** (.x6 ↦ᵣ q3) ** (.x7 ↦ᵣ k3) **
        ((F + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ q0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ q1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ q2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ q3) **
        ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ n3)) **
       addmodLbPlusOneFrame F raVal x2v x9v x10v x11v r0 r1 r2 r3 sm0 sm1 sm2 sm3) := by
  intro q0 k0 q1 k1 q2 k2 q3 k3
  simp only [sepConj_assoc']
  refine cpsTripleWithin_pre_regOwn_under (fun x5o => ?_)
  rw [← sepConj_assoc']
  refine cpsTripleWithin_pre_regOwn_under (fun x6o => ?_)
  rw [← sepConj_assoc']
  refine cpsTripleWithin_pre_regOwn_under (fun x7o => ?_)
  have hblk := carry_block_in_C
    (blockCode := evm_addmod_carry_plus_one_args_code (bt + 252))
    (totalCode := evm_addmod_total_program_code bt mo1 mo2 mo3 moNC)
    (calleeCode := evm_mod_callable_code_v5 calleeEntry)
    (fun a i h => evm_addmod_total_program_code_carry_plus_one_args_sub a i
      (by rw [← evm_addmod_carry_plus_one_args_code_eq_ofProg]; exact h))
    (cpsTripleWithin_frameR
      (addmodLbPlusOneFrame F raVal x2v x9v x10v x11v r0 r1 r2 r3 sm0 sm1 sm2 sm3)
      (addmodLbPlusOneFrame_pcFree F raVal x2v x9v x10v x11v r0 r1 r2 r3 sm0 sm1 sm2 sm3)
      (evm_addmod_carry_plus_one_args_spec_within F (bt + 252) x5o x6o x7o
        m0 m1 m2 m3 w0 w1 w2 w3 n0 n1 n2 n3))
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_) hblk
  · simp only [addmodLbPlusOneFrame, sepConj_assoc'] at hp ⊢; xperm_hyp hp
  · simp only [addmodLbPlusOneFrame, sepConj_assoc'] at hp ⊢; xperm_hyp hp

-- ============================================================================
-- Lb link 2: the second MOD near-call (byte 348 → 352)
-- ============================================================================

/-- Link 2 of Lb: the second MOD near-call (`JAL@348 → evm_mod_callable_v5 →
    ret@352`), discharged by the adapter. Dividend is the `+1` increment
    `fromLimbs ![q0,q1,q2,q3]`, divisor is the modulus `fromLimbs ![n0..n3]`.
    Between calls the div-scratch band arrives OWNED (from the callable return);
    it is `∃`-eliminated to the generic-valued form the adapter needs via
    `cpsTripleWithin_pre_divScratchValued`. The registers `x2/x9/x10/x11` are
    already carried as generic values (untouched by `plus_one_args`). -/
theorem lb_call2_in_C
    (bt F calleeEntry raVal x2v x9v x10v x11v : Word)
    (q0 q1 q2 q3 n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3 nn3 : Word)
    (mo1 mo2 mo3 moNC : BitVec 21)
    (hoffset : (bt + 348) + signExtend21 mo2 = calleeEntry)
    (callerAlign : ((bt + 348) + 4) &&& ~~~(1 : Word) = (bt + 348) + 4)
    (retAlign : ((calleeEntry + div128CallRetOff) + signExtend12 (0 : BitVec 12))
        &&& ~~~(1 : Word) = calleeEntry + div128CallRetOff)
    (hdisj : (CodeReq.singleton (bt + 348) (.JAL .x1 mo2)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjTC : (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC).Disjoint
      (evm_mod_callable_code_v5 calleeEntry)) :
    cpsTripleWithin (1 + (unifiedDivBound + 1)) (bt + 348) ((bt + 348) + 4)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      ((divScratchOwnCallNoX1 F **
        ((F + signExtend12 (3936 : BitVec 12)) ↦ₘ nn3) **
        (.x12 ↦ᵣ F) ** (.x9 ↦ᵣ x9v) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ x2v) **
        (.x5 ↦ᵣ n3) ** (.x6 ↦ᵣ q3) ** (.x7 ↦ᵣ nn3) **
        (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) ** (.x0 ↦ᵣ (0 : Word)) **
        evmWordIs F (EvmWord.fromLimbs ![q0, q1, q2, q3]) **
        evmWordIs (F + 32) (EvmWord.fromLimbs ![n0, n1, n2, n3])) **
       addmodCall1Frame F n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3)
      ((modStackDispatchPostCallableX9Owned F (EvmWord.fromLimbs ![q0, q1, q2, q3])
          (EvmWord.fromLimbs ![n0, n1, n2, n3]) ((bt + 348) + 4) **
        memOwn (F + signExtend12 (3936 : BitVec 12))) **
       addmodCall1Frame F n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3) := by
  refine cpsTripleWithin_frameR _
    (addmodCall1Frame_pcFree F n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3) ?_
  refine cpsTripleWithin_pre_divScratchValued (fun dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 => ?_)
  have hadapter := evm_addmod_v5_call_adapter_in_C (bt + 348) F calleeEntry mo2
    (EvmWord.fromLimbs ![q0, q1, q2, q3]) (EvmWord.fromLimbs ![n0, n1, n2, n3])
    x9v raVal x2v n3 q3 nn3 x10v x11v
    dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 nn3
    (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC)
    hoffset callerAlign retAlign hdisj
    (fun a i h => evm_addmod_total_program_code_carry_call2_sub a i h)
    hdisjTC
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => hp) hadapter
  rw [divModStackDispatchPreNoX1_unfold]
  simp only [sepConj_assoc'] at hp ⊢
  xperm_hyp hp

end EvmAsm.Evm64.AddMod.Compose
