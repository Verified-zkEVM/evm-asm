/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix25

  PASS 11 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  The **authorization-list walk segment chain** (`teerB + 440 → {2856, 644}`):
  the x21/x22 analogue of `teer_towalk_seg_spec` (module 20).  Chains the
  `rlp_walk_init`@110 group+pin ;; first glue (module 23) with the nine
  `walknext ;; alglue` compositions (sites 116/…/156, module 24) via the
  `teer_alglue_extend` combinator (module 23), reaching the `rlp_walk_next`@161
  CALL args at `teerB + 644`.  The final `walknext161 ;; authlist_setup`
  boundary (`teer_walknext161_authlist_spec`, module 24) closes the segment to
  `teerB + 676` (the `rlp_list_count_items` call).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix24

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## First auth-list walk boundary (`teerB + 440 → {2856, 484}`)

    `rlp_walk_init`@110 group+pin ;; first glue ;; `rlp_walk_next`@116 group+pin
    ;; glue.  Mirrors `teer_walk01_spec`. -/
set_option maxRecDepth 8000 in
theorem teer_authwalk01_spec (wi : RlpWalkInitAssumed fullCode)
    (hwi : wi.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_init)
    (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (v21o v22o : Word)
    (listBytes : List (BitVec 8)) (listOff srcOff1 : Nat)
    (halign : listBase.toNat % 8 = 0)
    (hoff : listOff < listBytes.length) (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hoff1 : srcOff1 < listBytes.length) (hover1 : listBase.toNat + srcOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff1) = true)
    (C0 C1 : Word)
    (hc1 : (listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) = C0)
    (hc2 : (listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)) = C0)
    (hoc : listBase + BitVec.ofNat 64 srcOff1 = C0)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode listBytes srcOff1
        (listBase + BitVec.ofNat 64 srcOff1) ((listBase + BitVec.ofNat 64 listOff) + listLen)
        next len → next = C1) :
    cpsBranchWithin ((((1 + 81) + 1) + 4) + (((1 + 87) + 1) + 3)) (teerB + 440) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes)) **
        ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o)))
      (teerB + 2856) teerFail (teerB + 484)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C1) ** (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
            (.x21 ↦ᵣ C1) ** (.x22 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen))) **
          ((.x1 ↦ᵣ (teerB + 468)) ** teerWalkScratch listBase listBytes **
            (.x12 ↦ᵣ len))) h) := by
  have hB0 := teer_walkinit110_alglue0_spec wi hwi listBase listLen a2Old t0Old t1Old t2Old
    t3Old t4Old t5Old t6Old raIn v21o v22o listBytes listOff halign hoff hover hvalid
    C0 hc1 hc2
  have hB1 := teer_walk_scratch_regOwn_adaptor (teerB + 444)
    (listBase + BitVec.ofNat 64 srcOff1) ((listBase + BitVec.ofNat 64 listOff) + listLen)
    (0 : Word) listBase listBytes
    ((.x21 ↦ᵣ C0) ** (.x22 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)))
    (fun t0 t1 t2 t3 t4 t5 t6 =>
      teer_walknext116_alglue1_spec wn hwn listBase
        ((listBase + BitVec.ofNat 64 listOff) + listLen) (0 : Word)
        t0 t1 t2 t3 t4 t5 t6 (teerB + 444) C0
        ((listBase + BitVec.ofNat 64 listOff) + listLen) listBytes srcOff1
        halign hoff1 hover1 hvalid1 C1 hc)
  exact cpsBranchWithin_seq_cpsBranchWithin_with_perm_same_cr hB0
    (fun h hq => by rw [hoc]; xperm_hyp hq) hB1
    (fun h hq => to_teerFail _ h hq) (fun h hq => to_teerFail _ h hq)

/-! ## The auth-list walk segment through walk-9 (`teerB + 440 → {2856, 644}`)

    Chains `teer_authwalk01_spec` with walks 121/…/156 via `teer_alglue_extend`. -/
set_option maxRecDepth 8000 in
theorem teer_authwalk_seg_spec (wi : RlpWalkInitAssumed fullCode)
    (hwi : wi.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_init)
    (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (v21o v22o : Word)
    (listBytes : List (BitVec 8))
    (listOff srcOff1 srcOff2 srcOff3 srcOff4 srcOff5 srcOff6 srcOff7 srcOff8 srcOff9 : Nat)
    (halign : listBase.toNat % 8 = 0)
    (hoff : listOff < listBytes.length) (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hoff1 : srcOff1 < listBytes.length) (hover1 : listBase.toNat + srcOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff1) = true)
    (hoff2 : srcOff2 < listBytes.length) (hover2 : listBase.toNat + srcOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff2) = true)
    (hoff3 : srcOff3 < listBytes.length) (hover3 : listBase.toNat + srcOff3 < 2 ^ 64)
    (hvalid3 : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff3) = true)
    (hoff4 : srcOff4 < listBytes.length) (hover4 : listBase.toNat + srcOff4 < 2 ^ 64)
    (hvalid4 : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff4) = true)
    (hoff5 : srcOff5 < listBytes.length) (hover5 : listBase.toNat + srcOff5 < 2 ^ 64)
    (hvalid5 : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff5) = true)
    (hoff6 : srcOff6 < listBytes.length) (hover6 : listBase.toNat + srcOff6 < 2 ^ 64)
    (hvalid6 : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff6) = true)
    (hoff7 : srcOff7 < listBytes.length) (hover7 : listBase.toNat + srcOff7 < 2 ^ 64)
    (hvalid7 : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff7) = true)
    (hoff8 : srcOff8 < listBytes.length) (hover8 : listBase.toNat + srcOff8 < 2 ^ 64)
    (hvalid8 : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff8) = true)
    (hoff9 : srcOff9 < listBytes.length) (hover9 : listBase.toNat + srcOff9 < 2 ^ 64)
    (hvalid9 : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff9) = true)
    (C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 : Word)
    (hc1 : (listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) = C0)
    (hc2 : (listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)) = C0)
    (hoc1 : listBase + BitVec.ofNat 64 srcOff1 = C0)
    (hoc2 : listBase + BitVec.ofNat 64 srcOff2 = C1)
    (hoc3 : listBase + BitVec.ofNat 64 srcOff3 = C2)
    (hoc4 : listBase + BitVec.ofNat 64 srcOff4 = C3)
    (hoc5 : listBase + BitVec.ofNat 64 srcOff5 = C4)
    (hoc6 : listBase + BitVec.ofNat 64 srcOff6 = C5)
    (hoc7 : listBase + BitVec.ofNat 64 srcOff7 = C6)
    (hoc8 : listBase + BitVec.ofNat 64 srcOff8 = C7)
    (hoc9 : listBase + BitVec.ofNat 64 srcOff9 = C8)
    (hcw1 : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode listBytes srcOff1
        (listBase + BitVec.ofNat 64 srcOff1) ((listBase + BitVec.ofNat 64 listOff) + listLen)
        next len → next = C1)
    (hcw2 : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode listBytes srcOff2
        (listBase + BitVec.ofNat 64 srcOff2) ((listBase + BitVec.ofNat 64 listOff) + listLen)
        next len → next = C2)
    (hcw3 : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode listBytes srcOff3
        (listBase + BitVec.ofNat 64 srcOff3) ((listBase + BitVec.ofNat 64 listOff) + listLen)
        next len → next = C3)
    (hcw4 : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode listBytes srcOff4
        (listBase + BitVec.ofNat 64 srcOff4) ((listBase + BitVec.ofNat 64 listOff) + listLen)
        next len → next = C4)
    (hcw5 : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode listBytes srcOff5
        (listBase + BitVec.ofNat 64 srcOff5) ((listBase + BitVec.ofNat 64 listOff) + listLen)
        next len → next = C5)
    (hcw6 : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode listBytes srcOff6
        (listBase + BitVec.ofNat 64 srcOff6) ((listBase + BitVec.ofNat 64 listOff) + listLen)
        next len → next = C6)
    (hcw7 : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode listBytes srcOff7
        (listBase + BitVec.ofNat 64 srcOff7) ((listBase + BitVec.ofNat 64 listOff) + listLen)
        next len → next = C7)
    (hcw8 : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode listBytes srcOff8
        (listBase + BitVec.ofNat 64 srcOff8) ((listBase + BitVec.ofNat 64 listOff) + listLen)
        next len → next = C8)
    (hcw9 : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode listBytes srcOff9
        (listBase + BitVec.ofNat 64 srcOff9) ((listBase + BitVec.ofNat 64 listOff) + listLen)
        next len → next = C9) :
    cpsBranchWithin
      (((((1 + 81) + 1) + 4) + (((1 + 87) + 1) + 3)) +
        ((((1 + 87) + 1) + 3) + ((((1 + 87) + 1) + 3) + ((((1 + 87) + 1) + 3) +
          ((((1 + 87) + 1) + 3) + ((((1 + 87) + 1) + 3) + ((((1 + 87) + 1) + 3) +
            ((((1 + 87) + 1) + 3) + (((1 + 87) + 1) + 3)))))))))
      (teerB + 440) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes)) **
        ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o)))
      (teerB + 2856) teerFail (teerB + 644)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C9) ** (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
            (.x21 ↦ᵣ C9) ** (.x22 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen))) **
          ((.x1 ↦ᵣ (teerB + 628)) ** teerWalkScratch listBase listBytes **
            (.x12 ↦ᵣ len))) h) := by
  have h01 := teer_authwalk01_spec wi hwi wn hwn listBase listLen a2Old t0Old t1Old t2Old
    t3Old t4Old t5Old t6Old raIn v21o v22o listBytes listOff srcOff1 halign hoff hover hvalid
    hoff1 hover1 hvalid1 C0 C1 hc1 hc2 hoc1 hcw1
  have h2 := teer_alglue_extend C1 C2
    ((listBase + BitVec.ofNat 64 listOff) + listLen) (teerB + 468) (teerB + 488)
    listBase listBytes srcOff2 _ hoc2 h01
    (fun len t0 t1 t2 t3 t4 t5 t6 =>
      teer_walknext121_alglue2_spec wn hwn listBase
        ((listBase + BitVec.ofNat 64 listOff) + listLen) len t0 t1 t2 t3 t4 t5 t6
        (teerB + 468) C1 ((listBase + BitVec.ofNat 64 listOff) + listLen) listBytes srcOff2
        halign hoff2 hover2 hvalid2 C2 hcw2)
  have h3 := teer_alglue_extend C2 C3
    ((listBase + BitVec.ofNat 64 listOff) + listLen) (teerB + 488) (teerB + 508)
    listBase listBytes srcOff3 _ hoc3 h2
    (fun len t0 t1 t2 t3 t4 t5 t6 =>
      teer_walknext126_alglue3_spec wn hwn listBase
        ((listBase + BitVec.ofNat 64 listOff) + listLen) len t0 t1 t2 t3 t4 t5 t6
        (teerB + 488) C2 ((listBase + BitVec.ofNat 64 listOff) + listLen) listBytes srcOff3
        halign hoff3 hover3 hvalid3 C3 hcw3)
  have h4 := teer_alglue_extend C3 C4
    ((listBase + BitVec.ofNat 64 listOff) + listLen) (teerB + 508) (teerB + 528)
    listBase listBytes srcOff4 _ hoc4 h3
    (fun len t0 t1 t2 t3 t4 t5 t6 =>
      teer_walknext131_alglue4_spec wn hwn listBase
        ((listBase + BitVec.ofNat 64 listOff) + listLen) len t0 t1 t2 t3 t4 t5 t6
        (teerB + 508) C3 ((listBase + BitVec.ofNat 64 listOff) + listLen) listBytes srcOff4
        halign hoff4 hover4 hvalid4 C4 hcw4)
  have h5 := teer_alglue_extend C4 C5
    ((listBase + BitVec.ofNat 64 listOff) + listLen) (teerB + 528) (teerB + 548)
    listBase listBytes srcOff5 _ hoc5 h4
    (fun len t0 t1 t2 t3 t4 t5 t6 =>
      teer_walknext136_alglue5_spec wn hwn listBase
        ((listBase + BitVec.ofNat 64 listOff) + listLen) len t0 t1 t2 t3 t4 t5 t6
        (teerB + 528) C4 ((listBase + BitVec.ofNat 64 listOff) + listLen) listBytes srcOff5
        halign hoff5 hover5 hvalid5 C5 hcw5)
  have h6 := teer_alglue_extend C5 C6
    ((listBase + BitVec.ofNat 64 listOff) + listLen) (teerB + 548) (teerB + 568)
    listBase listBytes srcOff6 _ hoc6 h5
    (fun len t0 t1 t2 t3 t4 t5 t6 =>
      teer_walknext141_alglue6_spec wn hwn listBase
        ((listBase + BitVec.ofNat 64 listOff) + listLen) len t0 t1 t2 t3 t4 t5 t6
        (teerB + 548) C5 ((listBase + BitVec.ofNat 64 listOff) + listLen) listBytes srcOff6
        halign hoff6 hover6 hvalid6 C6 hcw6)
  have h7 := teer_alglue_extend C6 C7
    ((listBase + BitVec.ofNat 64 listOff) + listLen) (teerB + 568) (teerB + 588)
    listBase listBytes srcOff7 _ hoc7 h6
    (fun len t0 t1 t2 t3 t4 t5 t6 =>
      teer_walknext146_alglue7_spec wn hwn listBase
        ((listBase + BitVec.ofNat 64 listOff) + listLen) len t0 t1 t2 t3 t4 t5 t6
        (teerB + 568) C6 ((listBase + BitVec.ofNat 64 listOff) + listLen) listBytes srcOff7
        halign hoff7 hover7 hvalid7 C7 hcw7)
  have h8 := teer_alglue_extend C7 C8
    ((listBase + BitVec.ofNat 64 listOff) + listLen) (teerB + 588) (teerB + 608)
    listBase listBytes srcOff8 _ hoc8 h7
    (fun len t0 t1 t2 t3 t4 t5 t6 =>
      teer_walknext151_alglue8_spec wn hwn listBase
        ((listBase + BitVec.ofNat 64 listOff) + listLen) len t0 t1 t2 t3 t4 t5 t6
        (teerB + 588) C7 ((listBase + BitVec.ofNat 64 listOff) + listLen) listBytes srcOff8
        halign hoff8 hover8 hvalid8 C8 hcw8)
  have h9 := teer_alglue_extend C8 C9
    ((listBase + BitVec.ofNat 64 listOff) + listLen) (teerB + 608) (teerB + 628)
    listBase listBytes srcOff9 _ hoc9 h8
    (fun len t0 t1 t2 t3 t4 t5 t6 =>
      teer_walknext156_alglue9_spec wn hwn listBase
        ((listBase + BitVec.ofNat 64 listOff) + listLen) len t0 t1 t2 t3 t4 t5 t6
        (teerB + 608) C8 ((listBase + BitVec.ofNat 64 listOff) + listLen) listBytes srcOff9
        halign hoff9 hover9 hvalid9 C9 hcw9)
  exact h9

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
