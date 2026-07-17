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

/-! ## 6-walk segment through walk-2 (`teerB + 216 → {2856, 280}`)

    Extends `teer_walk01_spec` by the `rlp_walk_next`@65 group+pin ;; glue 2.
    The boundary join threads the residual `∃ len` (walk-1 content length in
    `x12`) into the walk-2 group PRE via `cpsBranchWithin_exists_pre` (the walk
    group is universally quantified over its `a2Old = x12` arg) and applies the
    scratch adaptor.  The walk-2 input cursor matches walk-1's output `C1` via
    the offset correspondence `listBase + srcOff2 = C1`. -/
set_option maxRecDepth 8000 in
theorem teer_walk012_spec (wi : RlpWalkInitAssumed fullCode)
    (hwi : wi.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_init)
    (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (listBytes : List (BitVec 8)) (listOff srcOff1 srcOff2 : Nat)
    (halign : listBase.toNat % 8 = 0)
    (hoff : listOff < listBytes.length) (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hoff1 : srcOff1 < listBytes.length) (hover1 : listBase.toNat + srcOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff1) = true)
    (hoff2 : srcOff2 < listBytes.length) (hover2 : listBase.toNat + srcOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff2) = true)
    (C0 C1 C2 : Word)
    (hc1 : (listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) = C0)
    (hc2 : (listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)) = C0)
    (hoc1 : listBase + BitVec.ofNat 64 srcOff1 = C0)
    (hoc2 : listBase + BitVec.ofNat 64 srcOff2 = C1)
    (hcw1 : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode listBytes srcOff1
        (listBase + BitVec.ofNat 64 srcOff1) ((listBase + BitVec.ofNat 64 listOff) + listLen)
        next len → next = C1)
    (hcw2 : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode listBytes srcOff2
        (listBase + BitVec.ofNat 64 srcOff2) ((listBase + BitVec.ofNat 64 listOff) + listLen)
        next len → next = C2) :
    cpsBranchWithin
      (((((1 + 81) + 1) + 4) + (((1 + 87) + 1) + 3)) + (((1 + 87) + 1) + 3))
      (teerB + 216) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes)) **
        ((.x24 ↦ᵣ t0Old) ** (.x25 ↦ᵣ t1Old)))
      (teerB + 2856) teerFail
      (teerB + 280)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C2) ** (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
            (.x24 ↦ᵣ C2) ** (.x25 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen))) **
          ((.x1 ↦ᵣ (teerB + 264)) ** teerWalkScratch listBase listBytes **
            (.x12 ↦ᵣ len))) h) := by
  have hW01 := teer_walk01_spec wi hwi wn hwn listBase listLen a2Old t0Old t1Old t2Old
    t3Old t4Old t5Old t6Old raIn listBytes listOff srcOff1 halign hoff hover hvalid
    hoff1 hover1 hvalid1 C0 C1 hc1 hc2 hoc1 hcw1
  -- Walk-2 block: scratch-adapted, x12-abstracted for the incoming `∃ len`.
  have hB2 : ∀ len : Word,
      cpsBranchWithin (((1 + 87) + 1) + 3) (teerB + 260) fullCode
        (((.x1 ↦ᵣ (teerB + 244)) **
          ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff2)) **
            (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ len) **
            teerWalkScratch listBase listBytes)) **
          ((.x24 ↦ᵣ C1) ** (.x25 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen))))
        (teerB + 2856) teerFail (teerB + 280)
        (fun h => ∃ len' : Word,
          (((.x10 ↦ᵣ C2) ** (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
              (.x24 ↦ᵣ C2) ** (.x25 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen))) **
            ((.x1 ↦ᵣ (teerB + 264)) ** teerWalkScratch listBase listBytes **
              (.x12 ↦ᵣ len'))) h) := by
    intro len
    exact teer_walk_scratch_regOwn_adaptor (teerB + 244)
      (listBase + BitVec.ofNat 64 srcOff2) ((listBase + BitVec.ofNat 64 listOff) + listLen)
      len listBase listBytes
      ((.x24 ↦ᵣ C1) ** (.x25 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)))
      (fun s0 s1 s2 s3 s4 s5 s6 =>
        teer_walknext65_toglue2_spec wn hwn listBase
          ((listBase + BitVec.ofNat 64 listOff) + listLen) len
          s0 s1 s2 s3 s4 s5 s6 (teerB + 244) C1
          ((listBase + BitVec.ofNat 64 listOff) + listLen) listBytes srcOff2
          halign hoff2 hover2 hvalid2 C2 hcw2)
  exact cpsBranchWithin_seq_cpsBranchWithin_with_perm_same_cr hW01
    (fun h hq => by
      obtain ⟨len, hbody⟩ := hq
      exact ⟨len, by rw [hoc2]; xperm_hyp hbody⟩)
    (cpsBranchWithin_exists_pre hB2)
    (fun h hq => to_teerFail _ h hq) (fun h hq => to_teerFail _ h hq)

/-! ## `rlp_walk_next`@70 group+pin ;; `to`-walk glue 3 (`teerB + 280 → {2856, 300}`) -/

set_option maxRecDepth 8000 in
theorem teer_walknext70_toglue3_spec (wn : RlpWalkNextAssumed fullCode)
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
    cpsBranchWithin (((1 + 87) + 1) + 3) (teerB + 280) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes)) **
        ((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25)))
      (teerB + 2856) teerFail
      (teerB + 300)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v25) ** (.x24 ↦ᵣ C) ** (.x25 ↦ᵣ v25)) **
          ((.x1 ↦ᵣ (teerB + 284)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
  have h1 := cpsBranchWithin_frameR ((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_walknext70_pin_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid C hc)
  have h2 : cpsTripleWithin 3 (teerB + 288) (teerB + 300) fullCode
      (fun h => ∃ len : Word,
        (((.x1 ↦ᵣ (teerB + 284)) **
            (teerWalkScratch srcBase srcBytes **
             ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) **
          ((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25))) h)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v25) ** (.x24 ↦ᵣ C) ** (.x25 ↦ᵣ v25)) **
          ((.x1 ↦ᵣ (teerB + 284)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
    apply cpsTripleWithin_exists_pre_gen
    intro len
    have ht := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (teerB + 284)) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len))
      (by repeat' first
          | exact pcFree_regIs | exact teerWalkScratch_pcFree _ _ | apply pcFree_sepConj)
      (cpsTripleWithin_extend_code teer_mono (teer_toglue3_spec C (0 : Word) v24o v25))
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ⟨len, by xperm_hyp hq⟩) ht
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1 (fun h hq => sepConj_exists_left h hq) h2 (fun h hq => to_teerFail _ h hq)

/-! ## `rlp_walk_next`@75 group+pin ;; `to`-walk glue 4 (`teerB + 300 → {2856, 320}`) -/

set_option maxRecDepth 8000 in
theorem teer_walknext75_toglue4_spec (wn : RlpWalkNextAssumed fullCode)
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
    cpsBranchWithin (((1 + 87) + 1) + 3) (teerB + 300) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes)) **
        ((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25)))
      (teerB + 2856) teerFail
      (teerB + 320)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v25) ** (.x24 ↦ᵣ C) ** (.x25 ↦ᵣ v25)) **
          ((.x1 ↦ᵣ (teerB + 304)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
  have h1 := cpsBranchWithin_frameR ((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_walknext75_pin_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid C hc)
  have h2 : cpsTripleWithin 3 (teerB + 308) (teerB + 320) fullCode
      (fun h => ∃ len : Word,
        (((.x1 ↦ᵣ (teerB + 304)) **
            (teerWalkScratch srcBase srcBytes **
             ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) **
          ((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25))) h)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v25) ** (.x24 ↦ᵣ C) ** (.x25 ↦ᵣ v25)) **
          ((.x1 ↦ᵣ (teerB + 304)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
    apply cpsTripleWithin_exists_pre_gen
    intro len
    have ht := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (teerB + 304)) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len))
      (by repeat' first
          | exact pcFree_regIs | exact teerWalkScratch_pcFree _ _ | apply pcFree_sepConj)
      (cpsTripleWithin_extend_code teer_mono (teer_toglue4_spec C (0 : Word) v24o v25))
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ⟨len, by xperm_hyp hq⟩) ht
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1 (fun h hq => sepConj_exists_left h hq) h2 (fun h hq => to_teerFail _ h hq)

/-! ## `rlp_walk_next`@80 group+pin ;; `to`-walk glue 5 (`teerB + 320 → {2856, 340}`) -/

set_option maxRecDepth 8000 in
theorem teer_walknext80_toglue5_spec (wn : RlpWalkNextAssumed fullCode)
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
    cpsBranchWithin (((1 + 87) + 1) + 3) (teerB + 320) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes)) **
        ((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25)))
      (teerB + 2856) teerFail
      (teerB + 340)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v25) ** (.x24 ↦ᵣ C) ** (.x25 ↦ᵣ v25)) **
          ((.x1 ↦ᵣ (teerB + 324)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
  have h1 := cpsBranchWithin_frameR ((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_walknext80_pin_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid C hc)
  have h2 : cpsTripleWithin 3 (teerB + 328) (teerB + 340) fullCode
      (fun h => ∃ len : Word,
        (((.x1 ↦ᵣ (teerB + 324)) **
            (teerWalkScratch srcBase srcBytes **
             ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) **
          ((.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25))) h)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ v25) ** (.x24 ↦ᵣ C) ** (.x25 ↦ᵣ v25)) **
          ((.x1 ↦ᵣ (teerB + 324)) ** teerWalkScratch srcBase srcBytes **
            (.x12 ↦ᵣ len))) h) := by
    apply cpsTripleWithin_exists_pre_gen
    intro len
    have ht := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (teerB + 324)) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len))
      (by repeat' first
          | exact pcFree_regIs | exact teerWalkScratch_pcFree _ _ | apply pcFree_sepConj)
      (cpsTripleWithin_extend_code teer_mono (teer_toglue5_spec C (0 : Word) v24o v25))
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ⟨len, by xperm_hyp hq⟩) ht
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1 (fun h hq => sepConj_exists_left h hq) h2 (fun h hq => to_teerFail _ h hq)

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
