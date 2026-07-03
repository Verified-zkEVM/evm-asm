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

end EvmAsm.Evm64.AddMod.Compose
