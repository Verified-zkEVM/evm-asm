/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix19

  PASS 11 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  The remaining `to`/value-walk `rlp_walk_next` cursor pins (sites 70/75/80/85)
  and the pinned-group ;; MV-shuffle-glue compositions for the middle of the
  6-walk segment (`walknext65 ;; toglue2`, `walknext70 ;; toglue3`,
  `walknext75 ;; toglue4`, `walknext80 ;; toglue5`).  Each composition mirrors
  the proven `teer_walknext60_toglue1_spec` (module 17): frame the pinned group
  with the callee-saved `x24`/`x25` snapshot, thread the residual `∃ len`
  (walk-reported content length in `x12`) through the 3-MV glue via
  `cpsTripleWithin_exists_pre_gen`, and re-expose it at the top of the fall post.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix18

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## Remaining `to`/value-walk `rlp_walk_next` cursor pins (70/75/80/85) -/

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@70 group + pin (`teerB + 280 → {2856, 288}`). -/
theorem teer_walknext70_pin_spec (wn : RlpWalkNextAssumed fullCode)
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
    cpsBranchWithin ((1 + 87) + 1) (teerB + 280) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 288)
      (fun h => ∃ len : Word,
        ((.x1 ↦ᵣ (teerB + 284)) **
          (teerWalkScratch srcBase srcBytes **
           ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) h) :=
  teer_walknext_group_pin ((1 + 87) + 1) (teerB + 280) (teerB + 288) (teerB + 284)
    C endPtr (srcBase + BitVec.ofNat 64 srcOff) srcBytes srcOff
    _ (teerWalkScratch srcBase srcBytes) hc
    (teer_walknext70_group_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@75 group + pin (`teerB + 300 → {2856, 308}`). -/
theorem teer_walknext75_pin_spec (wn : RlpWalkNextAssumed fullCode)
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
    cpsBranchWithin ((1 + 87) + 1) (teerB + 300) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 308)
      (fun h => ∃ len : Word,
        ((.x1 ↦ᵣ (teerB + 304)) **
          (teerWalkScratch srcBase srcBytes **
           ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) h) :=
  teer_walknext_group_pin ((1 + 87) + 1) (teerB + 300) (teerB + 308) (teerB + 304)
    C endPtr (srcBase + BitVec.ofNat 64 srcOff) srcBytes srcOff
    _ (teerWalkScratch srcBase srcBytes) hc
    (teer_walknext75_group_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@80 group + pin (`teerB + 320 → {2856, 328}`). -/
theorem teer_walknext80_pin_spec (wn : RlpWalkNextAssumed fullCode)
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
    cpsBranchWithin ((1 + 87) + 1) (teerB + 320) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 328)
      (fun h => ∃ len : Word,
        ((.x1 ↦ᵣ (teerB + 324)) **
          (teerWalkScratch srcBase srcBytes **
           ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) h) :=
  teer_walknext_group_pin ((1 + 87) + 1) (teerB + 320) (teerB + 328) (teerB + 324)
    C endPtr (srcBase + BitVec.ofNat 64 srcOff) srcBytes srcOff
    _ (teerWalkScratch srcBase srcBytes) hc
    (teer_walknext80_group_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@85 group + pin (`teerB + 340 → {2856, 348}`). -/
theorem teer_walknext85_pin_spec (wn : RlpWalkNextAssumed fullCode)
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
    cpsBranchWithin ((1 + 87) + 1) (teerB + 340) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail
      (teerB + 348)
      (fun h => ∃ len : Word,
        ((.x1 ↦ᵣ (teerB + 344)) **
          (teerWalkScratch srcBase srcBytes **
           ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) h) :=
  teer_walknext_group_pin ((1 + 87) + 1) (teerB + 340) (teerB + 348) (teerB + 344)
    C endPtr (srcBase + BitVec.ofNat 64 srcOff) srcBytes srcOff
    _ (teerWalkScratch srcBase srcBytes) hc
    (teer_walknext85_group_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)

/-! ## `rlp_walk_next`@65 group+pin ;; `to`-walk glue 2 (`teerB + 260 → {2856, 280}`) -/

set_option maxRecDepth 8000 in
/-- Composes the pinned `rlp_walk_next`@65 group with the 3-MV `to`-walk glue
    (`teer_toglue2_spec`), reaching the `rlp_walk_next`@70 CALL args at
    `teerB + 280`.  Mirrors `teer_walknext60_toglue1_spec`. -/
theorem teer_walknext65_toglue2_spec (wn : RlpWalkNextAssumed fullCode)
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
    cpsBranchWithin (((1 + 87) + 1) + 3) (teerB + 260) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes)) **
        ((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25)))
      (teerB + 2856) teerFail
      (teerB + 280)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v25) ** (.x24 ↦ᵣ C) ** (.x25 ↦ᵣ v25)) **
          ((.x1 ↦ᵣ (teerB + 264)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
  have h1 := cpsBranchWithin_frameR ((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_walknext65_pin_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid C hc)
  have h2 : cpsTripleWithin 3 (teerB + 268) (teerB + 280) fullCode
      (fun h => ∃ len : Word,
        (((.x1 ↦ᵣ (teerB + 264)) **
            (teerWalkScratch srcBase srcBytes **
             ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) **
          ((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25))) h)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v25) ** (.x24 ↦ᵣ C) ** (.x25 ↦ᵣ v25)) **
          ((.x1 ↦ᵣ (teerB + 264)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
    apply cpsTripleWithin_exists_pre_gen
    intro len
    have ht := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (teerB + 264)) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len))
      (by repeat' first
          | exact pcFree_regIs | exact teerWalkScratch_pcFree _ _ | apply pcFree_sepConj)
      (cpsTripleWithin_extend_code teer_mono (teer_toglue2_spec C (0 : Word) v24o v25))
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ⟨len, by xperm_hyp hq⟩) ht
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1
    (fun h hq => sepConj_exists_left h hq)
    h2
    (fun h hq => to_teerFail _ h hq)

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
