/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix17

  PASS 11 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  Pin-application lemmas for the `to`/value walk chain: each `rlp_walk_init` /
  `rlp_walk_next` dispatch GROUP (modules 10/11) followed by its cursor-pinning
  bridge (modules 13/16), yielding a concrete-cursor fall post the MV-shuffle
  glue can consume, plus the first joins of the 6-walk segment.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix16

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## The walk-callee scratch frame

    The regOwn block a `rlp_walk_*` group returns (its `t0..t6` scratch, `x0`,
    and the single physical `bytesRegion`).  It is `pcFree`. -/

/-- The scratch frame each `rlp_walk_*` dispatch group returns. -/
def teerWalkScratch (srcBase : Word) (srcBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes

theorem teerWalkScratch_pcFree (srcBase : Word) (srcBytes : List (BitVec 8)) :
    (teerWalkScratch srcBase srcBytes).pcFree := by
  unfold teerWalkScratch
  repeat' first
    | exact pcFree_regOwn | exact pcFree_regIs | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj

/-! ## `rlp_walk_init`@54 dispatch group + cursor pin (`teerB + 216 → {2856, 224}`) -/

set_option maxRecDepth 8000 in
/-- `rlp_walk_init`@54 group + pin: the short/long list disjunction collapses to
    the single forward list cursor `C` under the per-walk facts `hc1`/`hc2`. -/
theorem teer_walkinit54_pin_spec (wi : RlpWalkInitAssumed fullCode)
    (hwi : wi.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_init)
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat)
    (halign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (C : Word)
    (hc1 : (listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) = C)
    (hc2 : (listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)) = C) :
    cpsBranchWithin ((1 + 81) + 1) (teerB + 216) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes))
      (teerB + 2856) teerFail
      (teerB + 224)
      ((.x1 ↦ᵣ (teerB + 220)) **
        (teerWalkScratch listBase listBytes **
         ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
           (.x12 ↦ᵣ (0 : Word))))) :=
  teer_walkinit_group_pin ((1 + 81) + 1) (teerB + 216) (teerB + 224) (teerB + 220) C
    ((listBase + BitVec.ofNat 64 listOff) + listLen)
    ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))
    ((listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)))
    _ (teerWalkScratch listBase listBytes) hc1 hc2
    (teer_walkinit54_group_spec wi hwi listBase listLen a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn listBytes listOff halign hoff hover hvalid)

/-! ## `rlp_walk_init`@54 group+pin ;; first `to`-walk glue (`teerB + 216 → {2856, 240}`) -/

set_option maxRecDepth 8000 in
/-- Composes the pinned `rlp_walk_init`@54 group with the first `to`-walk glue
    (`teer_toglue0_spec`, snapshot cursor `x24`/end `x25`), reaching the
    `rlp_walk_next`@60 CALL args at `teerB + 240`. -/
theorem teer_walkinit54_toglue0_spec (wi : RlpWalkInitAssumed fullCode)
    (hwi : wi.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_init)
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (v24o v25o : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat)
    (halign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (C : Word)
    (hc1 : (listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) = C)
    (hc2 : (listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)) = C) :
    cpsBranchWithin (((1 + 81) + 1) + 4) (teerB + 216) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes)) **
        ((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25o)))
      (teerB + 2856) teerFail
      (teerB + 240)
      (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
          (.x24 ↦ᵣ C) ** (.x25 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen))) **
        ((.x1 ↦ᵣ (teerB + 220)) ** teerWalkScratch listBase listBytes **
          (.x12 ↦ᵣ (0 : Word)))) := by
  have h1 := cpsBranchWithin_frameR ((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25o))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_walkinit54_pin_spec wi hwi listBase listLen a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn listBytes listOff halign hoff hover hvalid C hc1 hc2)
  have h2 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (teerB + 220)) ** teerWalkScratch listBase listBytes ** (.x12 ↦ᵣ (0 : Word)))
    (by repeat' first
        | exact pcFree_regIs | exact teerWalkScratch_pcFree _ _ | apply pcFree_sepConj)
    (cpsTripleWithin_extend_code teer_mono
      (teer_toglue0_spec C ((listBase + BitVec.ofNat 64 listOff) + listLen) v24o v25o))
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1
    (fun h hq => by xperm_hyp hq)
    h2
    (fun h hq => to_teerFail _ h hq)

/-! ## Pull a top-level existential out of a left sepConj factor -/

/-- `((∃ x, P x) ** Q) → ∃ x, (P x ** Q)`.  Used to lift the residual `∃ len`
    (walk-reported content length) of a pinned `rlp_walk_next` group's fall post
    to the top so the downstream glue join can absorb it via
    `cpsTripleWithin_exists_pre_gen`. -/
theorem sepConj_exists_left {α : Sort _} {P : α → Assertion} {Q : Assertion} :
    ∀ h, ((fun h' => ∃ x, P x h') ** Q) h → ∃ x, (P x ** Q) h := by
  intro h hpq
  obtain ⟨h1, h2, hd, hu, ⟨x, hPx⟩, hQ⟩ := hpq
  exact ⟨x, h1, h2, hd, hu, hPx, hQ⟩

/-! ## `rlp_walk_next`@60 dispatch group + cursor pin (`teerB + 240 → {2856, 248}`) -/

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@60 group + pin: the callee success post `rlpWalkNextOk`
    collapses to the concrete advanced cursor `C` (residual `∃ len` at top),
    under the per-walk fact `hc`. -/
theorem teer_walknext60_pin_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 240) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 248)
      (fun h => ∃ len : Word,
        ((.x1 ↦ᵣ (teerB + 244)) **
          (teerWalkScratch srcBase srcBytes **
           ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) h) :=
  teer_walknext_group_pin ((1 + 87) + 1) (teerB + 240) (teerB + 248) (teerB + 244)
    C endPtr (srcBase + BitVec.ofNat 64 srcOff) srcBytes srcOff
    _ (teerWalkScratch srcBase srcBytes) hc
    (teer_walknext60_group_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)

/-! ## `rlp_walk_next`@60 group+pin ;; `to`-walk glue 1 (`teerB + 240 → {2856, 260}`) -/

set_option maxRecDepth 8000 in
/-- Composes the pinned `rlp_walk_next`@60 group with the 3-MV `to`-walk glue
    (`teer_toglue1_spec`, refresh cursor `x24`, restage `a0`/`a1`), reaching the
    `rlp_walk_next`@65 CALL args at `teerB + 260`.  The residual `∃ len`
    (walk-reported content length, alive in `x12`) is threaded through the glue
    as a frame and re-exposed at the top of the fall post. -/
theorem teer_walknext60_toglue1_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (v24o v25 : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin (((1 + 87) + 1) + 3) (teerB + 240) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes)) **
        ((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25)))
      (teerB + 2856) teerFail
      (teerB + 260)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v25) ** (.x24 ↦ᵣ C) ** (.x25 ↦ᵣ v25)) **
          ((.x1 ↦ᵣ (teerB + 244)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
  have h1 := cpsBranchWithin_frameR ((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_walknext60_pin_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid C hc)
  have h2 : cpsTripleWithin 3 (teerB + 248) (teerB + 260) fullCode
      (fun h => ∃ len : Word,
        (((.x1 ↦ᵣ (teerB + 244)) **
            (teerWalkScratch srcBase srcBytes **
             ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) **
          ((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25))) h)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v25) ** (.x24 ↦ᵣ C) ** (.x25 ↦ᵣ v25)) **
          ((.x1 ↦ᵣ (teerB + 244)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
    apply cpsTripleWithin_exists_pre_gen
    intro len
    have ht := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (teerB + 244)) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len))
      (by repeat' first
          | exact pcFree_regIs | exact teerWalkScratch_pcFree _ _ | apply pcFree_sepConj)
      (cpsTripleWithin_extend_code teer_mono (teer_toglue1_spec C (0 : Word) v24o v25))
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ⟨len, by xperm_hyp hq⟩) ht
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1
    (fun h hq => sepConj_exists_left h hq)
    h2
    (fun h hq => to_teerFail _ h hq)

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
