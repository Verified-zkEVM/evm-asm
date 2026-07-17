/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix21

  PASS 11 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  The **recipient (`to`) capture join** (`teerB + 340 → {2856, 388}`): the first
  "new-shape" boundary of the tx-parse prefix.  Chains the pinned 6th `to`-walk
  dispatch group (`teer_walknext85_pin_spec`, module 19, `teerB + 340 → 348`)
  onto the recipient-capture straight-line block (`teer_recipient_capture_spec`,
  module 2, `teerB + 348 → 388`), which records the recipient content pointer
  (`teer_recipient_ptr = a0 - a2`) and length (`teer_recipient_len = a2`).

  Unlike the `to`-walk glue joins (modules 18/19/20), the capture block CONSUMES
  two of the walk-callee scratch registers concretely — `x5` (the `la`
  materialisation temporary) and `x30` (the pointer subtraction target).  The
  walk group returns them OWNED inside `teerWalkScratch`, so the join unbundles
  `teerWalkScratch` (exposing `x5`/`x30` via
  `cpsTripleWithin_of_forall_regIs_to_regOwn2`) and frames the recipient `.bss`
  cells (`teer_recipient_ptr`/`teer_recipient_len`) alongside the callee-saved
  `to`-snapshot `x24`/`x25`.  This begins the `teerPrefixExtra` mem-cell
  threading: the two recipient cells are peeled off the ambient frame here.

  The `teerB + 388` fall post is the true machine state after the capture: the
  captured recipient pointer/length in the `.bss` cells, the advanced `to`
  cursor snapshot (`x24 = a0`), and the residual walk-callee scratch (with `x5`
  now holding `&teer_recipient_len` and `x30` the recipient pointer — a later
  re-adaptation re-owns them for the `value` walk at `teerB + 388`).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix20

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## The recipient (`to`) capture join (`teerB + 340 → {2856, 388}`) -/

set_option maxRecDepth 8000 in
/-- **6th `to`-walk group+pin ;; recipient capture** (`teerB + 340 → {2856, 388}`).

    Composes the pinned `rlp_walk_next`@85 dispatch group (module 19) with the
    recipient-capture block (module 2).  The join unbundles `teerWalkScratch`
    to expose the two scratch registers the capture consumes concretely
    (`x5`/`x30`), and frames the recipient `.bss` cells + the `to`-snapshot
    `x24`/`x25`. -/
theorem teer_walknext85_capture_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (v24o v25 rpo rlo : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin (((1 + 87) + 1) + 10) (teerB + 340) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes)) **
        (((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25)) **
          ((teerRecipientPtr ↦ₘ rpo) ** (teerRecipientLen ↦ₘ rlo))))
      (teerB + 2856) teerFail
      (teerB + 388)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v25) ** (.x12 ↦ᵣ len) ** (.x24 ↦ᵣ C) **
            (.x25 ↦ᵣ v25)) **
          ((.x1 ↦ᵣ (teerB + 344)) ** (.x5 ↦ᵣ teerRecipientLen) **
            (.x30 ↦ᵣ (C - len)) **
            regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
          ((teerRecipientPtr ↦ₘ (C - len)) ** (teerRecipientLen ↦ₘ len))) h) := by
  -- Block 1: the pinned walk-85 group, framed with the snapshot + recipient cells.
  have h1 := cpsBranchWithin_frameR
    (((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25)) **
      ((teerRecipientPtr ↦ₘ rpo) ** (teerRecipientLen ↦ₘ rlo)))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    (teer_walknext85_pin_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid C hc)
  -- Block 2: recipient capture, unbundling `teerWalkScratch` for `x5`/`x30`.
  have h2 : cpsTripleWithin 10 (teerB + 348) (teerB + 388) fullCode
      (fun h => ∃ len : Word,
        (((.x1 ↦ᵣ (teerB + 344)) **
            (teerWalkScratch srcBase srcBytes **
             ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) **
          (((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25)) **
            ((teerRecipientPtr ↦ₘ rpo) ** (teerRecipientLen ↦ₘ rlo)))) h)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v25) ** (.x12 ↦ᵣ len) ** (.x24 ↦ᵣ C) **
            (.x25 ↦ᵣ v25)) **
          ((.x1 ↦ᵣ (teerB + 344)) ** (.x5 ↦ᵣ teerRecipientLen) **
            (.x30 ↦ᵣ (C - len)) **
            regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
          ((teerRecipientPtr ↦ₘ (C - len)) ** (teerRecipientLen ↦ₘ len))) h) := by
    apply cpsTripleWithin_exists_pre_gen
    intro len
    -- The capture block, universally over its two consumed scratch registers.
    have hcap : cpsTripleWithin 10 (teerB + 348) (teerB + 388) fullCode
        ((((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** (.x25 ↦ᵣ v25) **
            (.x24 ↦ᵣ v24o) ** (teerRecipientPtr ↦ₘ rpo) ** (teerRecipientLen ↦ₘ rlo)) **
          ((.x1 ↦ᵣ (teerB + 344)) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
            regOwn .x29 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion srcBase srcBytes)) **
          regOwn .x5 ** regOwn .x30)
        (fun h =>
          (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v25) ** (.x12 ↦ᵣ len) ** (.x24 ↦ᵣ C) **
              (.x25 ↦ᵣ v25)) **
            ((.x1 ↦ᵣ (teerB + 344)) ** (.x5 ↦ᵣ teerRecipientLen) **
              (.x30 ↦ᵣ (C - len)) **
              regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
              (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
            ((teerRecipientPtr ↦ₘ (C - len)) ** (teerRecipientLen ↦ₘ len))) h) := by
      apply cpsTripleWithin_of_forall_regIs_to_regOwn2
      intro v5o v30o
      exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
        (cpsTripleWithin_frameR
          ((.x1 ↦ᵣ (teerB + 344)) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
            regOwn .x29 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion srcBase srcBytes)
          (by repeat' first
              | exact pcFree_regIs | exact pcFree_regOwn | exact bytesRegion_pcFree _ _
              | apply pcFree_sepConj)
          (cpsTripleWithin_extend_code teer_mono
            (teer_recipient_capture_spec C (0 : Word) len v25 v30o v5o v24o rpo rlo)))
    exact cpsTripleWithin_weaken
      (fun h hp => by simp only [teerWalkScratch] at hp; xperm_hyp hp)
      (fun h hq => ⟨len, by xperm_hyp hq⟩)
      hcap
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1 (fun h hq => sepConj_exists_left h hq) h2 (fun h hq => to_teerFail _ h hq)

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
