/-
  EvmAsm.Evm64.AddMod.Compose.CarryCompose

  Phase-3 M3d for total ADDMOD (issue #9704): compose the carry sub-chains.

  `evm_addmod_carry_after_call2_spec_within` chains La (`la_spec_within`,
  byte 160 → 252) with Lb (`lb_spec_within`, 252 → 356) over the common region
  `C = addmodCarryCode …`, yielding a single triple from the carry-path entry
  through the second MOD call, with `EvmWord.pow256ModN N` (= `2^256 mod N`) in
  the work window at F+32..56.

  The reusable glue solved here (and mirrored by the later Lc/Ld composes): La's
  post sheds `x2/x9/x10/x11` to `regOwn`, but Lb's pre pins them at generic
  `regIs` values. A pure midpoint implication cannot turn `regOwn` into a fixed
  `regIs`, so Lb is first re-derived with those four registers OWNED in its pre
  (via the `cpsTripleWithin_pre_regOwn`/`_under` peel, mirroring
  `cpsTripleWithin_pre_divScratchValued`); then the La→Lb midpoint is a pure
  permutation (`xperm_hyp`), with the F+0..24 / F+32..56 work cells folded from
  `evmWordIs` and the second remainder rewritten to `pow256ModN N` via
  `addOne_via_incr_chain` + `pow256ModN_runtime_construction`.
-/

import EvmAsm.Evm64.AddMod.Compose.CarryLb

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64

/-- La;;Lb over `C`: carry entry (byte 160) through the second MOD call
    (byte 356). Post: `x12 = F`, `EvmWord.pow256ModN N` at F+32..56 (the
    `2^256 mod N` carry contribution), N parked at S1, r at S2. -/
theorem evm_addmod_carry_after_call2_spec_within
    (bt F x5Old n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 : Word)
    (x1v x2v x6v x7v x9v x10v x11v : Word)
    (sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7 : Word)
    (shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word)
    (hN : EvmWord.fromLimbs ![n0, n1, n2, n3] ≠ 0)
    (hoffset1 : (bt + 244) + signExtend21 mo1 = calleeEntry)
    (callerAlign1 : ((bt + 244) + 4) &&& ~~~(1 : Word) = (bt + 244) + 4)
    (hoffset2 : (bt + 348) + signExtend21 mo2 = calleeEntry)
    (callerAlign2 : ((bt + 348) + 4) &&& ~~~(1 : Word) = (bt + 348) + 4)
    (retAlign : ((calleeEntry + div128CallRetOff) + signExtend12 (0 : BitVec 12))
        &&& ~~~(1 : Word) = calleeEntry + div128CallRetOff)
    (hdisj1 : (CodeReq.singleton (bt + 244) (.JAL .x1 mo1)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisj2 : (CodeReq.singleton (bt + 348) (.JAL .x1 mo2)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjTC : (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC).Disjoint
      (evm_mod_callable_code_v5 calleeEntry)) :
    cpsTripleWithin
      (((21 + (1 + (unifiedDivBound + 1))) + 1) + (((24 + (1 + (unifiedDivBound + 1))) + 1)))
      (bt + 160) (((bt + 348) + 4) + 4)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** (.x5 ↦ᵣ x5Old) **
        ((F + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
        ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
        ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
        ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
        ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
        ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
        ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
        ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3)) **
       addmodLaTail F x1v x2v x6v x7v x9v x10v x11v
         sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem)
      (addmodCarryAfterCall2 F ((bt + 348) + 4)
        (EvmWord.mod (-1 : EvmWord) (EvmWord.fromLimbs ![n0, n1, n2, n3]) + 1)
        (EvmWord.pow256ModN (EvmWord.fromLimbs ![n0, n1, n2, n3]))
        n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3) := by
  -- La (160 → 248+4 = 252)
  have hla := la_spec_within bt F x5Old n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3
    x1v x2v x6v x7v x9v x10v x11v
    sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem
    mo1 mo2 mo3 moNC calleeEntry hoffset1 callerAlign1 retAlign hdisj1 hdisjTC
  rw [show (bt + 248) + 4 = bt + 252 from by bv_omega] at hla
  set N := EvmWord.fromLimbs ![n0, n1, n2, n3] with hNdef
  -- Lb, re-derived with x2/x9/x10/x11 OWNED in its pre, instantiated at the
  -- concrete work-cell limbs m_i = getLimbN (mod (-1) N) i, w_i = getLimbN (-1) i.
  have hlb_ready : cpsTripleWithin (((24 + (1 + (unifiedDivBound + 1))) + 1))
      (bt + 252) (((bt + 348) + 4) + 4)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (addmodCarryAfterCall1 F (bt + 248) n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3)
      (addmodCarryAfterCall2 F ((bt + 348) + 4)
        (EvmWord.mod (-1 : EvmWord) N + 1)
        (EvmWord.pow256ModN N) n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3) := by
    -- key: pre with the four sheddable regs OWNED, brought to the front.
    have key : cpsTripleWithin (((24 + (1 + (unifiedDivBound + 1))) + 1))
        (bt + 252) (((bt + 348) + 4) + 4)
        (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
        (regOwn .x2 ** regOwn .x9 ** regOwn .x10 ** regOwn .x11 **
          ((.x12 ↦ᵣ F) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
           (.x0 ↦ᵣ (0 : Word)) **
           evmWordIs F (-1 : EvmWord) **
           evmWordIs (F + 32) (EvmWord.mod (-1 : EvmWord) N) **
           divScratchOwnCallNoX1 F ** (.x1 ↦ᵣ (bt + 248)) **
           memOwn (F + signExtend12 (3936 : BitVec 12)) **
           addmodCall1Frame F n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3))
        (addmodCarryAfterCall2 F ((bt + 348) + 4)
          (EvmWord.mod (-1 : EvmWord) N + 1)
          (EvmWord.pow256ModN N) n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3) := by
      refine cpsTripleWithin_pre_regOwn (fun x2gv => ?_)
      refine cpsTripleWithin_pre_regOwn_under (fun x9gv => ?_)
      rw [← sepConj_assoc']; refine cpsTripleWithin_pre_regOwn_under (fun x10gv => ?_)
      rw [← sepConj_assoc']; refine cpsTripleWithin_pre_regOwn_under (fun x11gv => ?_)
      have hse : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
      have hqfold := addOne_via_incr_chain (EvmWord.mod (-1 : EvmWord) N)
      simp only at hqfold
      have hv := EvmWord.pow256ModN_runtime_construction N hN
      have e0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
      have e8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
      have e16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
      have e24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
      have e32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
      have e40 : signExtend12 (40 : BitVec 12) = 40#64 := by decide
      have e48 : signExtend12 (48 : BitVec 12) = 48#64 := by decide
      have e56 : signExtend12 (56 : BitVec 12) = 56#64 := by decide
      refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
        (lb_spec_within bt F (bt + 248) x2gv x9gv x10gv x11gv
          ((EvmWord.mod (-1 : EvmWord) N).getLimbN 0) ((EvmWord.mod (-1 : EvmWord) N).getLimbN 1)
          ((EvmWord.mod (-1 : EvmWord) N).getLimbN 2) ((EvmWord.mod (-1 : EvmWord) N).getLimbN 3)
          ((-1 : EvmWord).getLimbN 0) ((-1 : EvmWord).getLimbN 1)
          ((-1 : EvmWord).getLimbN 2) ((-1 : EvmWord).getLimbN 3)
          n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3
          mo1 mo2 mo3 moNC calleeEntry hoffset2 callerAlign2 retAlign hdisj2 hdisjTC)
      · -- pre: my peeled pre → Lb's pre (fold evmWordIs work cells, permute)
        simp only [addmodLbPlusOneFrame, addmodCall1Frame, evmWordIs,
          e0, e8, e16, e24, e32, e40, e48, e56,
          BitVec.add_assoc, BitVec.reduceAdd, add_zero] at hp ⊢
        xperm_hyp hp
      · -- post: Lb's post → goal post (rewrite dividend / remainder to pow256ModN N)
        simp only [hse] at hp
        rw [hqfold, hv] at hp
        exact hp
    -- Reshape addmodCarryAfterCall1 into key's pre (pure permutation).
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) key
    simp only [addmodCarryAfterCall1, addmodAfterCall1Rest, hNdef] at hp ⊢
    xperm_hyp hp
  -- Chain La ;; Lb.
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hla hlb_ready

end EvmAsm.Evm64.AddMod.Compose
