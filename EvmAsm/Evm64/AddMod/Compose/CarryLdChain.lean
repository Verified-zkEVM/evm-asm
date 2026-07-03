/-
  EvmAsm.Evm64.AddMod.Compose.CarryLdChain

  Phase-3 M3d for total ADDMOD (issue #9704): the final Ld chain assembly.

  Chains the four Ld links (mod_add_stage ;; evm_add ;; pass1take_clean ;;
  pass2_owned, byte 460 → 832) over the common region `C`, folds the branch-free
  conditional subtract's per-limb output into `EvmWord.addmod a b N`, and then
  composes the whole carry branch (`evm_addmod_carry_branch_stack_spec_within`,
  byte 160 → 832).

  The one pure step here (`ld_pass2_fromLimbs_sub`) reassembles pass2's four
  borrow-chain output limbs into the word difference `s − (N &&& mask)` via
  `sub_borrow_chain_correct`; everything downstream reuses the already-proven
  `condSub_mask_eq` / `sum_minus_masked_N_eq_addmod` value bridges.
-/

import EvmAsm.Evm64.AddMod.Compose.CarryLd
import EvmAsm.Evm64.AddMod.Compose.CarryCompose
import EvmAsm.Evm64.EvmWordArith.Comparison

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64

/-- Pure fold: pass2's four borrow-chain output limbs (`r0..r3`, with
    `mm_i = n_i &&& maskIn`) reassemble into the word difference
    `fromLimbs ![s0,s1,s2,s3] − (fromLimbs ![n0,n1,n2,n3] &&& fromLimbs (fun _ => maskIn))`.
    Direct application of `sub_borrow_chain_correct` with the divisor limbs
    identified via `getLimb_and` / `getLimb_fromLimbs_const`. -/
theorem ld_pass2_fromLimbs_sub (s0 s1 s2 s3 n0 n1 n2 n3 maskIn : Word) :
    let mm0 := n0 &&& maskIn
    let c0 := if BitVec.ult s0 mm0 then (1 : Word) else 0
    let r0 := s0 - mm0
    let mm1 := n1 &&& maskIn
    let f1 := if BitVec.ult s1 mm1 then (1 : Word) else 0
    let e1 := s1 - mm1
    let g1 := if BitVec.ult e1 c0 then (1 : Word) else 0
    let r1 := e1 - c0
    let c1 := f1 ||| g1
    let mm2 := n2 &&& maskIn
    let f2 := if BitVec.ult s2 mm2 then (1 : Word) else 0
    let e2 := s2 - mm2
    let g2 := if BitVec.ult e2 c1 then (1 : Word) else 0
    let r2 := e2 - c1
    let c2 := f2 ||| g2
    let mm3 := n3 &&& maskIn
    let r3 := (s3 - mm3) - c2
    EvmWord.fromLimbs ![r0, r1, r2, r3]
      = EvmWord.fromLimbs ![s0, s1, s2, s3]
        - (EvmWord.fromLimbs ![n0, n1, n2, n3] &&& EvmWord.fromLimbs (fun _ => maskIn)) := by
  intro mm0 c0 r0 mm1 f1 e1 g1 r1 c1 mm2 f2 e2 g2 r2 c2 mm3 r3
  set a := EvmWord.fromLimbs ![s0, s1, s2, s3] with ha
  set b := EvmWord.fromLimbs ![n0, n1, n2, n3] &&& EvmWord.fromLimbs (fun _ => maskIn) with hb
  -- getLimb of a and b
  have ga0 : a.getLimb 0 = s0 := by rw [ha, EvmWord.getLimb_fromLimbs]; rfl
  have ga1 : a.getLimb 1 = s1 := by rw [ha, EvmWord.getLimb_fromLimbs]; rfl
  have ga2 : a.getLimb 2 = s2 := by rw [ha, EvmWord.getLimb_fromLimbs]; rfl
  have ga3 : a.getLimb 3 = s3 := by rw [ha, EvmWord.getLimb_fromLimbs]; rfl
  have gb0 : b.getLimb 0 = mm0 := by
    rw [hb, EvmWord.getLimb_and, EvmWord.getLimb_fromLimbs, EvmWord.getLimb_fromLimbs_const]; rfl
  have gb1 : b.getLimb 1 = mm1 := by
    rw [hb, EvmWord.getLimb_and, EvmWord.getLimb_fromLimbs, EvmWord.getLimb_fromLimbs_const]; rfl
  have gb2 : b.getLimb 2 = mm2 := by
    rw [hb, EvmWord.getLimb_and, EvmWord.getLimb_fromLimbs, EvmWord.getLimb_fromLimbs_const]; rfl
  have gb3 : b.getLimb 3 = mm3 := by
    rw [hb, EvmWord.getLimb_and, EvmWord.getLimb_fromLimbs, EvmWord.getLimb_fromLimbs_const]; rfl
  have hsub := EvmWord.sub_borrow_chain_correct a b
  simp only [ga0, ga1, ga2, ga3, gb0, gb1, gb2, gb3] at hsub
  obtain ⟨d0, d1, d2, d3⟩ := hsub
  -- The borrow-chain results now match pass2's r_i lets definitionally.
  have hfun : (![r0, r1, r2, r3] : Fin 4 → Word) = (a - b).getLimb := by
    funext i
    fin_cases i
    · simpa [r0, mm0] using d0.symm
    · simpa [r1, e1, c0, mm1, mm0] using d1.symm
    · simpa [r2, e2, c1, f1, g1, e1, c0, mm2, mm1, mm0] using d2.symm
    · simpa [r3, mm3, c2, f2, g2, e2, c1, f1, g1, e1, c0, mm2, mm1, mm0] using d3.symm
  calc EvmWord.fromLimbs ![r0, r1, r2, r3]
      = EvmWord.fromLimbs (a - b).getLimb := by rw [hfun]
    _ = a - b := EvmWord.fromLimbs_getLimb (a - b)

/-- `N &&& fromLimbs (const maskIn) = N &&& condSubMask take` when `maskIn` is the
    64-bit select word `if take then -1 else 0` (i.e. `fromLimbs (const maskIn)`
    is the 256-bit `condSubMask take`). -/
theorem mask_fromLimbs_const_eq (take : Bool) :
    EvmWord.fromLimbs (fun _ => (if take then (-1 : Word) else 0))
      = EvmWord.condSubMask take := by
  cases take with
  | true => decide
  | false => decide

/-- Round-trip: `fromLimbs ![v.getLimbN 0, .., v.getLimbN 3] = v`. -/
theorem fromLimbs_getLimbN_vec (v : EvmWord) :
    EvmWord.fromLimbs ![v.getLimbN 0, v.getLimbN 1, v.getLimbN 2, v.getLimbN 3] = v := by
  have hfun : (![v.getLimbN 0, v.getLimbN 1, v.getLimbN 2, v.getLimbN 3] : Fin 4 → Word)
      = v.getLimb := by
    funext i; fin_cases i <;> simp [EvmWord.getLimb_eq_getLimbN]
  rw [hfun]; exact EvmWord.fromLimbs_getLimb v

-- ============================================================================
-- Ld chain assembly + carry-branch result post
-- ============================================================================

/-- Tail carried (framed) through the cond-subtract links (pass1take, pass2):
    everything the branch-free conditional subtract does not touch — `x1`, `x2`,
    `x9`, the old add-input window at F+0..24 (now junk), the owned div-scratch
    band + `F−160` cell, and the S2 (`r`) / S3 (`m`) park cells. (`x0`, the S1
    (`N`) cells, `x5/x6/x7/x10/x11/x12` and the sum cells are handled explicitly
    by the cond-sub block specs.) -/
def addmodLdCondSubTail (F raVal x2v x9v : Word) (m : EvmWord)
    (r0 r1 r2 r3 p0 p1 p2 p3 : Word) : Assertion :=
  (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ x2v) ** (.x9 ↦ᵣ x9v) **
  evmWordIs F m ** divScratchOwnCallNoX1 F ** memOwn (F + signExtend12 (3936 : BitVec 12)) **
  ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ r0) **
  ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ r1) **
  ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ r2) **
  ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ r3) **
  ((F + signExtend12 (3840 : BitVec 12)) ↦ₘ p0) **
  ((F + signExtend12 (3848 : BitVec 12)) ↦ₘ p1) **
  ((F + signExtend12 (3856 : BitVec 12)) ↦ₘ p2) **
  ((F + signExtend12 (3864 : BitVec 12)) ↦ₘ p3)

theorem addmodLdCondSubTail_pcFree (F raVal x2v x9v : Word) (m : EvmWord)
    (r0 r1 r2 r3 p0 p1 p2 p3 : Word) :
    (addmodLdCondSubTail F raVal x2v x9v m r0 r1 r2 r3 p0 p1 p2 p3).pcFree := by
  unfold addmodLdCondSubTail divScratchOwnCallNoX1 divScratchOwn evmWordIs
  pcFree

/-- Owned result post of the carry branch: `x12 = F+32`, the ADDMOD result at
    F+32..56, everything else shed to `regOwn`/`memOwn`. -/
def addmodLdResultOwned (F : Word) (result : EvmWord) : Assertion :=
  (.x12 ↦ᵣ (F + 32)) ** evmWordIs (F + 32) result **
  regOwn .x0 ** regOwn .x1 ** regOwn .x2 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x9 ** regOwn .x10 ** regOwn .x11 **
  divScratchOwnCallNoX1 F ** memOwn (F + signExtend12 (3936 : BitVec 12)) **
  evmWordOwn F **
  memOwn (F + signExtend12 (3872 : BitVec 12)) ** memOwn (F + signExtend12 (3880 : BitVec 12)) **
  memOwn (F + signExtend12 (3888 : BitVec 12)) ** memOwn (F + signExtend12 (3896 : BitVec 12)) **
  memOwn (F + signExtend12 (3840 : BitVec 12)) ** memOwn (F + signExtend12 (3848 : BitVec 12)) **
  memOwn (F + signExtend12 (3856 : BitVec 12)) ** memOwn (F + signExtend12 (3864 : BitVec 12)) **
  memOwn (F + signExtend12 (3904 : BitVec 12)) ** memOwn (F + signExtend12 (3912 : BitVec 12)) **
  memOwn (F + signExtend12 (3920 : BitVec 12)) ** memOwn (F + signExtend12 (3928 : BitVec 12))

/-- `ld_pass1take_in_C` with the dead-on-entry `x6/x7/x11` inputs (`evm_add`'s
    let-computed limb-3 outputs `carry3b/result3/carry3a`, immediately
    overwritten by pass-1) merely `regOwn` in the pre. This is the shape that
    joins directly onto `ld_evm_add_in_C`'s post without naming those deep
    expressions: the link2→link3 midpoint sheds them to `regOwn`. Proven by
    peeling the three owned registers to generic values (`ld_pass1take_in_C` is
    parametric in `x6Old/x7Old/x11Old`). -/
theorem ld_pass1take_owned
    (bt G carry x10Old : Word)
    (s0 s1 s2 s3 n0 n1 n2 n3 mask : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word)
    (hmask : mask = (0 : Word) -
      ((carry + signExtend12 (0 : BitVec 12)) |||
       (((if BitVec.ult s3 n3 then (1 : Word) else 0) |||
          (if BitVec.ult (s3 - n3)
            ((if BitVec.ult s2 n2 then (1 : Word) else 0) |||
             (if BitVec.ult (s2 - n2)
               ((if BitVec.ult s1 n1 then (1 : Word) else 0) |||
                (if BitVec.ult (s1 - n1)
                  (if BitVec.ult s0 n0 then (1 : Word) else 0)
                  then (1 : Word) else 0))
               then (1 : Word) else 0))
            then (1 : Word) else 0))
         ^^^ signExtend12 (1 : BitVec 12)))) :
    cpsTripleWithin 25 (bt + 612) ((bt + 612) + 100)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
       ((.x12 ↦ᵣ G) ** (.x5 ↦ᵣ carry) ** (.x10 ↦ᵣ x10Old) ** (.x0 ↦ᵣ (0 : Word)) **
        ((G + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
        ((G + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
        ((G + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
        ((G + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
        ((G + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
        ((G + signExtend12 (3880 : BitVec 12)) ↦ₘ n1) **
        ((G + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
        ((G + signExtend12 (3896 : BitVec 12)) ↦ₘ n3)))
      ((.x12 ↦ᵣ G) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x10 ↦ᵣ (carry + signExtend12 (0 : BitVec 12))) ** (.x11 ↦ᵣ mask) **
       (.x0 ↦ᵣ (0 : Word)) **
       ((G + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((G + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       ((G + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
       ((G + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       ((G + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((G + signExtend12 (3880 : BitVec 12)) ↦ₘ n1) **
       ((G + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((G + signExtend12 (3896 : BitVec 12)) ↦ₘ n3)) := by
  refine cpsTripleWithin_pre_regOwn (fun x6g => ?_)
  refine cpsTripleWithin_pre_regOwn_under (fun x7g => ?_)
  rw [← sepConj_assoc']
  refine cpsTripleWithin_pre_regOwn_under (fun x11g => ?_)
  rw [sepConj_assoc']
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp)
    (ld_pass1take_in_C bt G carry x6g x7g x10Old x11g s0 s1 s2 s3 n0 n1 n2 n3 mask
      mo1 mo2 mo3 moNC calleeEntry hmask)
  xperm_hyp hp

-- ============================================================================
-- The full Ld chain (byte 460 → 832): mod_add_stage ;; evm_add ;;
-- pass1take_owned ;; pass2, over C, with the untouched carry-path state framed.
-- ============================================================================

/-- The `mask` word produced by pass1 from the sum/N limbs `s_i`/`n_i`. -/
def ldMask (carry s0 s1 s2 s3 n0 n1 n2 n3 : Word) : Word :=
  (0 : Word) -
    ((carry + signExtend12 (0 : BitVec 12)) |||
     (((if BitVec.ult s3 n3 then (1 : Word) else 0) |||
        (if BitVec.ult (s3 - n3)
          ((if BitVec.ult s2 n2 then (1 : Word) else 0) |||
           (if BitVec.ult (s2 - n2)
             ((if BitVec.ult s1 n1 then (1 : Word) else 0) |||
              (if BitVec.ult (s1 - n1)
                (if BitVec.ult s0 n0 then (1 : Word) else 0)
                then (1 : Word) else 0))
             then (1 : Word) else 0))
          then (1 : Word) else 0))
       ^^^ signExtend12 (1 : BitVec 12)))

/-- **Ld complete** (chain form): the four Ld links over `C`, byte 460 → 832,
    with the ADDMOD carry-path result `(m + rMod) − (N &&& condSubMask take)`
    folded into `x12+0..24` and everything else shed to owned. Keeps `m`, `rMod`,
    `N = fromLimbs ![n]` abstract; the carry-branch compose instantiates
    `m := pow256ModN N`, `rMod := mod (a+b) N` and rewrites the result to
    `EvmWord.addmod a b N` via `sum_minus_masked_N_eq_addmod`. -/
theorem ld_spec_within
    (bt F raVal x2v x6v x7v x9v x10v x11v : Word) (m rMod : EvmWord)
    (n0 n1 n2 n3 r0 r1 r2 r3 dd0 dd1 dd2 dd3 : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word) :
    cpsTripleWithin (((8 + 30) + 25) + 30) (bt + 460) (bt + 832)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** regOwn .x5 **
        ((F + signExtend12 (3840 : BitVec 12)) ↦ₘ m.getLimbN 0) **
        ((F + signExtend12 (3848 : BitVec 12)) ↦ₘ m.getLimbN 1) **
        ((F + signExtend12 (3856 : BitVec 12)) ↦ₘ m.getLimbN 2) **
        ((F + signExtend12 (3864 : BitVec 12)) ↦ₘ m.getLimbN 3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ dd0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ dd1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ dd2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ dd3)) **
       addmodLdModAddFrame F raVal x2v x6v x7v x9v x10v x11v rMod n0 n1 n2 n3 r0 r1 r2 r3)
      (addmodLdResultOwned F
        ((m + rMod) - (EvmWord.fromLimbs ![n0, n1, n2, n3] &&&
          EvmWord.condSubMask
            (decide (m.toNat + rMod.toNat ≥ (EvmWord.fromLimbs ![n0, n1, n2, n3]).toNat))))) := by
  -- abbreviations for the overflow bit (evm_add's x5), the sum limbs, and the mask
  set carry : Word := if m.toNat + rMod.toNat ≥ 2 ^ 256 then (1 : Word) else 0 with hcarrydef
  set s0 := (m + rMod).getLimbN 0 with hs0
  set s1 := (m + rMod).getLimbN 1 with hs1
  set s2 := (m + rMod).getLimbN 2 with hs2
  set s3 := (m + rMod).getLimbN 3 with hs3
  set mask := ldMask carry s0 s1 s2 s3 n0 n1 n2 n3 with hmaskdef
  have e0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have e8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
  have e16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
  have e24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
  -- coordinate-shift identities for the N cells: at x12 = G = F+32, the divisor
  -- `N` parked at S1 (`F−192..−168`) is reached as `(F+32)+signExtend12 3872..3896`,
  -- i.e. `F+signExtend12 3904..3928`.
  have hn0 : (F + 32) + signExtend12 (3872 : BitVec 12) = F + signExtend12 (3904 : BitVec 12) := by
    rw [show signExtend12 (3872 : BitVec 12) = (18446744073709551392 : Word) from by decide,
      show signExtend12 (3904 : BitVec 12) = (18446744073709551424 : Word) from by decide]
    bv_omega
  have hn1 : (F + 32) + signExtend12 (3880 : BitVec 12) = F + signExtend12 (3912 : BitVec 12) := by
    rw [show signExtend12 (3880 : BitVec 12) = (18446744073709551400 : Word) from by decide,
      show signExtend12 (3912 : BitVec 12) = (18446744073709551432 : Word) from by decide]
    bv_omega
  have hn2 : (F + 32) + signExtend12 (3888 : BitVec 12) = F + signExtend12 (3920 : BitVec 12) := by
    rw [show signExtend12 (3888 : BitVec 12) = (18446744073709551408 : Word) from by decide,
      show signExtend12 (3920 : BitVec 12) = (18446744073709551440 : Word) from by decide]
    bv_omega
  have hn3 : (F + 32) + signExtend12 (3896 : BitVec 12) = F + signExtend12 (3928 : BitVec 12) := by
    rw [show signExtend12 (3896 : BitVec 12) = (18446744073709551416 : Word) from by decide,
      show signExtend12 (3928 : BitVec 12) = (18446744073709551448 : Word) from by decide]
    bv_omega
  -- the four links
  have hstage := ld_mod_add_stage_in_C bt F raVal x2v x6v x7v x9v x10v x11v rMod
    (m.getLimbN 0) (m.getLimbN 1) (m.getLimbN 2) (m.getLimbN 3) n0 n1 n2 n3 r0 r1 r2 r3
    dd0 dd1 dd2 dd3 mo1 mo2 mo3 moNC calleeEntry
  rw [show (bt + 460) + 32 = bt + 492 from by bv_omega] at hstage
  have hadd := ld_evm_add_in_C bt F raVal x2v x9v x10v (m.getLimbN 3) x6v x7v x11v m rMod
    n0 n1 n2 n3 r0 r1 r2 r3 (m.getLimbN 0) (m.getLimbN 1) (m.getLimbN 2) (m.getLimbN 3)
    mo1 mo2 mo3 moNC calleeEntry
  simp only at hadd
  rw [show (bt + 492) + 120 = bt + 612 from by bv_omega] at hadd
  have hpass1 := ld_pass1take_owned bt (F + 32) carry x10v s0 s1 s2 s3 n0 n1 n2 n3 mask
    mo1 mo2 mo3 moNC calleeEntry hmaskdef
  rw [show (bt + 612) + 100 = bt + 712 from by bv_omega] at hpass1
  have hpass2 := ld_pass2_in_C bt (F + 32) mask (carry + signExtend12 (0 : BitVec 12))
    s0 s1 s2 s3 n0 n1 n2 n3 mo1 mo2 mo3 moNC calleeEntry
  simp only at hpass2
  rw [show (bt + 712) + 120 = bt + 832 from by bv_omega] at hpass2
  -- frame the untouched carry-path tail around the two cond-sub links
  have hpass1f := cpsTripleWithin_frameR
    (addmodLdCondSubTail F raVal x2v x9v m r0 r1 r2 r3
      (m.getLimbN 0) (m.getLimbN 1) (m.getLimbN 2) (m.getLimbN 3))
    (addmodLdCondSubTail_pcFree F raVal x2v x9v m r0 r1 r2 r3
      (m.getLimbN 0) (m.getLimbN 1) (m.getLimbN 2) (m.getLimbN 3))
    hpass1
  have hpass2f := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** addmodLdCondSubTail F raVal x2v x9v m r0 r1 r2 r3
      (m.getLimbN 0) (m.getLimbN 1) (m.getLimbN 2) (m.getLimbN 3))
    (by rw [addmodLdCondSubTail] ; pcFree)
    hpass2
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?post)
    (cpsTripleWithin_seq_perm_same_cr ?rc
      (cpsTripleWithin_seq_perm_same_cr ?rb
        (cpsTripleWithin_seq_perm_same_cr ?ra hstage hadd) hpass1f) hpass2f)
  case ra =>
    intro h hp
    simp only [addmodLdModAddFrame, addmodLdAddFrame, evmWordIs,
      e0, e8, e16, e24, BitVec.add_assoc, BitVec.reduceAdd, add_zero] at hp ⊢
    xperm_hyp hp
  case rb =>
    intro h hp
    simp only [addmodLdAddFrame, addmodLdCondSubTail, evmWordIs,
      e0, e8, e16, e24, hn0, hn1, hn2, hn3,
      BitVec.add_assoc, BitVec.reduceAdd, add_zero, sepConj_assoc'] at hp ⊢
    exact sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7)
        (sepConj_mono (regIs_implies_regOwn .x11) (fun _ x => x))) h (by xperm_hyp hp)
  case rc =>
    intro h hp
    simp only [addmodLdCondSubTail] at hp ⊢
    xperm_hyp hp
  case post =>
    -- (1) the pass1 borrow chain in `mask` equals `s < N`
    have hb3 := @EvmWord.lt_borrow_chain_correct (m + rMod) (EvmWord.fromLimbs ![n0, n1, n2, n3])
    simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
      EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3,
      EvmWord.getLimbN_fromLimbs_gen_0, EvmWord.getLimbN_fromLimbs_gen_1,
      EvmWord.getLimbN_fromLimbs_gen_2, EvmWord.getLimbN_fromLimbs_gen_3,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      ← hs0, ← hs1, ← hs2, ← hs3] at hb3
    -- (2) hence `mask = if (m+rMod ≥ N) then -1 else 0`
    have hmaskval : mask = if m.toNat + rMod.toNat ≥ (EvmWord.fromLimbs ![n0, n1, n2, n3]).toNat
        then (-1 : Word) else 0 := by
      rw [hmaskdef, ldMask, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
        show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide, add_zero]
      exact EvmWord.condSub_mask_eq m rMod (EvmWord.fromLimbs ![n0, n1, n2, n3]) carry _ hcarrydef hb3
    -- (3) so the pass2 output word equals the ADDMOD carry-path result:
    --     massage `ld_pass2_fromLimbs_sub`'s RHS into the goal's result form
    have hmaskbool : mask =
        if decide (m.toNat + rMod.toNat ≥ (EvmWord.fromLimbs ![n0, n1, n2, n3]).toNat)
        then (-1 : Word) else 0 := by
      rw [hmaskval]
      by_cases hc : m.toNat + rMod.toNat ≥ (EvmWord.fromLimbs ![n0, n1, n2, n3]).toNat <;>
        simp [hc]
    have hfold := ld_pass2_fromLimbs_sub s0 s1 s2 s3 n0 n1 n2 n3 mask
    simp only at hfold
    rw [show EvmWord.fromLimbs ![s0, s1, s2, s3] = m + rMod from by
      rw [hs0, hs1, hs2, hs3]; exact fromLimbs_getLimbN_vec _] at hfold
    simp only [hmaskbool] at hfold
    rw [mask_fromLimbs_const_eq] at hfold
    -- (4) rewrite the goal's result to the pass2 output limbs, expand the
    --     result word into its four cells, and shed everything else valued →
    --     owned via a pointwise `sepConj_mono` chain over the goal's atom
    --     order (the source side is `hq` reordered by `xperm_hyp`).
    simp only [addmodLdResultOwned, addmodLdCondSubTail,
      e0, e8, e16, e24, hn0, hn1, hn2, hn3,
      BitVec.add_assoc, BitVec.reduceAdd, add_zero, sepConj_assoc'] at hq ⊢
    simp only [hmaskbool] at hq
    rw [← hfold]
    simp only [evmWordIs,
      EvmWord.getLimbN_fromLimbs_gen_0, EvmWord.getLimbN_fromLimbs_gen_1,
      EvmWord.getLimbN_fromLimbs_gen_2, EvmWord.getLimbN_fromLimbs_gen_3,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc']
    exact sepConj_mono (fun _ x => x)                                 -- x12
      (sepConj_mono (fun _ x => x)                                    -- out0
      (sepConj_mono (fun _ x => x)                                    -- out1
      (sepConj_mono (fun _ x => x)                                    -- out2
      (sepConj_mono (fun _ x => x)                                    -- out3
      (sepConj_mono (regIs_implies_regOwn .x0)
      (sepConj_mono (regIs_implies_regOwn .x1)
      (sepConj_mono (regIs_implies_regOwn .x2)
      (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7)
      (sepConj_mono (regIs_implies_regOwn .x9)
      (sepConj_mono (regIs_implies_regOwn .x10)
      (sepConj_mono (regIs_implies_regOwn .x11)
      (sepConj_mono (fun _ x => x)                                    -- divScratch
      (sepConj_mono (fun _ x => x)                                    -- memOwn F−160
      (sepConj_mono (fun _ hw => evmWordIs_to_evmWordOwn hw)          -- evmWordOwn F
      (sepConj_mono memIs_implies_memOwn                              -- S2 r cells
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn                              -- S3 p cells
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn                              -- N cells
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        memIs_implies_memOwn))))))))))))))))))))))))))) h (by xperm_hyp hq)

-- ============================================================================
-- The carry branch, complete (byte 160 → 832)
-- ============================================================================

/-- **The ADDMOD carry branch** (byte 160 → 832, over `C`): from the carry-path
    entry (`N ≠ 0`, add carry-out set) through the three MOD calls
    (`(2^256−1) mod N`, `+1`-then-`mod N` = `pow256ModN N`, `r mod N`) and the
    final pre-reduced modular add + branch-free conditional subtract, landing
    the EVM ADDMOD result `EvmWord.addmod a b N` at `sp+64`
    (`addmodLdResultOwned`), with everything else shed to owned. -/
theorem evm_addmod_carry_branch_stack_spec_within
    (bt F x5Old n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 : Word)
    (x1v x2v x6v x7v x9v x10v x11v : Word)
    (sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7 : Word)
    (shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word)
    (a b : EvmWord)
    (hr : EvmWord.fromLimbs ![r0, r1, r2, r3] = a + b)
    (hcarry : (EvmWord.addCarry a b).fst = true)
    (hN : EvmWord.fromLimbs ![n0, n1, n2, n3] ≠ 0)
    (hoffset1 : (bt + 244) + signExtend21 mo1 = calleeEntry)
    (callerAlign1 : ((bt + 244) + 4) &&& ~~~(1 : Word) = (bt + 244) + 4)
    (hoffset2 : (bt + 348) + signExtend21 mo2 = calleeEntry)
    (callerAlign2 : ((bt + 348) + 4) &&& ~~~(1 : Word) = (bt + 348) + 4)
    (hoffset3 : (bt + 452) + signExtend21 mo3 = calleeEntry)
    (callerAlign3 : ((bt + 452) + 4) &&& ~~~(1 : Word) = (bt + 452) + 4)
    (retAlign : ((calleeEntry + div128CallRetOff) + signExtend12 (0 : BitVec 12))
        &&& ~~~(1 : Word) = calleeEntry + div128CallRetOff)
    (hdisj1 : (CodeReq.singleton (bt + 244) (.JAL .x1 mo1)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisj2 : (CodeReq.singleton (bt + 348) (.JAL .x1 mo2)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisj3 : (CodeReq.singleton (bt + 452) (.JAL .x1 mo3)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjTC : (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC).Disjoint
      (evm_mod_callable_code_v5 calleeEntry)) :
    cpsTripleWithin
      (((((21 + (1 + (unifiedDivBound + 1))) + 1) + (((24 + (1 + (unifiedDivBound + 1))) + 1)))
          + ((24 + (1 + (unifiedDivBound + 1))) + 1))
        + (((8 + 30) + 25) + 30))
      (bt + 160) (bt + 832)
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
      (addmodLdResultOwned F
        (EvmWord.addmod a b (EvmWord.fromLimbs ![n0, n1, n2, n3]))) := by
  set N := EvmWord.fromLimbs ![n0, n1, n2, n3] with hNdef
  -- La;;Lb;;Lc (160 → 460)
  have hac3 := evm_addmod_carry_after_call3_spec_within
    bt F x5Old n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3
    x1v x2v x6v x7v x9v x10v x11v
    sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem
    mo1 mo2 mo3 moNC calleeEntry hN
    hoffset1 callerAlign1 hoffset2 callerAlign2 hoffset3 callerAlign3
    retAlign hdisj1 hdisj2 hdisj3 hdisjTC
  rw [show ((bt + 452) + 4) + 4 = bt + 460 from by bv_omega] at hac3
  -- Ld (460 → 832), re-derived with x2/x6/x7/x9/x10/x11 OWNED in its pre and
  -- the result rewritten to `EvmWord.addmod a b N`.
  have hld_ready : cpsTripleWithin (((8 + 30) + 25) + 30) (bt + 460) (bt + 832)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (addmodCarryAfterCall3 F ((bt + 452) + 4)
        (EvmWord.fromLimbs ![r0, r1, r2, r3])
        (EvmWord.mod (EvmWord.fromLimbs ![r0, r1, r2, r3]) N)
        n0 n1 n2 n3 r0 r1 r2 r3
        ((EvmWord.pow256ModN N).getLimbN 0) ((EvmWord.pow256ModN N).getLimbN 1)
        ((EvmWord.pow256ModN N).getLimbN 2) ((EvmWord.pow256ModN N).getLimbN 3))
      (addmodLdResultOwned F (EvmWord.addmod a b N)) := by
    have key : cpsTripleWithin (((8 + 30) + 25) + 30) (bt + 460) (bt + 832)
        (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
        (regOwn .x2 ** regOwn .x6 ** regOwn .x7 ** regOwn .x9 ** regOwn .x10 ** regOwn .x11 **
          ((.x12 ↦ᵣ F) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
           evmWordIs F (EvmWord.fromLimbs ![r0, r1, r2, r3]) **
           evmWordIs (F + 32) (EvmWord.mod (EvmWord.fromLimbs ![r0, r1, r2, r3]) N) **
           divScratchOwnCallNoX1 F ** (.x1 ↦ᵣ ((bt + 452) + 4)) **
           memOwn (F + signExtend12 (3936 : BitVec 12)) **
           addmodCall1Frame F n0 n1 n2 n3 r0 r1 r2 r3
             ((EvmWord.pow256ModN N).getLimbN 0) ((EvmWord.pow256ModN N).getLimbN 1)
             ((EvmWord.pow256ModN N).getLimbN 2) ((EvmWord.pow256ModN N).getLimbN 3)))
        (addmodLdResultOwned F (EvmWord.addmod a b N)) := by
      refine cpsTripleWithin_pre_regOwn (fun x2g => ?_)
      refine cpsTripleWithin_pre_regOwn_under (fun x6g => ?_)
      rw [← sepConj_assoc']; refine cpsTripleWithin_pre_regOwn_under (fun x7g => ?_)
      rw [← sepConj_assoc']; refine cpsTripleWithin_pre_regOwn_under (fun x9g => ?_)
      rw [← sepConj_assoc']; refine cpsTripleWithin_pre_regOwn_under (fun x10g => ?_)
      rw [← sepConj_assoc']; refine cpsTripleWithin_pre_regOwn_under (fun x11g => ?_)
      have e0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
      have e8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
      have e16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
      have e24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
      have hres : (EvmWord.pow256ModN N + EvmWord.mod (EvmWord.fromLimbs ![r0, r1, r2, r3]) N)
          - (N &&& EvmWord.condSubMask
              (decide ((EvmWord.pow256ModN N).toNat
                + (EvmWord.mod (EvmWord.fromLimbs ![r0, r1, r2, r3]) N).toNat ≥ N.toNat)))
          = EvmWord.addmod a b N := by
        rw [hr]; exact EvmWord.sum_minus_masked_N_eq_addmod a b N hN hcarry
      refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_)
        (ld_spec_within bt F ((bt + 452) + 4) x2g x6g x7g x9g x10g x11g
          (EvmWord.pow256ModN N) (EvmWord.mod (EvmWord.fromLimbs ![r0, r1, r2, r3]) N)
          n0 n1 n2 n3 r0 r1 r2 r3
          ((EvmWord.fromLimbs ![r0, r1, r2, r3]).getLimbN 0)
          ((EvmWord.fromLimbs ![r0, r1, r2, r3]).getLimbN 1)
          ((EvmWord.fromLimbs ![r0, r1, r2, r3]).getLimbN 2)
          ((EvmWord.fromLimbs ![r0, r1, r2, r3]).getLimbN 3)
          mo1 mo2 mo3 moNC calleeEntry)
      · simp only [addmodLdModAddFrame, addmodCall1Frame, evmWordIs,
          e0, e8, e16, e24, BitVec.add_assoc, BitVec.reduceAdd, add_zero] at hp ⊢
        xperm_hyp hp
      · rw [hres] at hq; exact hq
    -- Reshape addmodCarryAfterCall3 into key's pre (pure permutation).
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) key
    simp only [addmodCarryAfterCall3, addmodAfterCall3Rest] at hp ⊢
    xperm_hyp hp
  -- Chain (La;;Lb;;Lc) ;; Ld.
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hac3 hld_ready

end EvmAsm.Evm64.AddMod.Compose
