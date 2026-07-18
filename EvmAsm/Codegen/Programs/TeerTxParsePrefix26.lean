/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix26

  PASS 11 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  Two closing joins for the tx-parse prefix walk chain:

    * `teer_value_reinit_spec` (`teerB + 388 → {2856, 440}`): the `value` walk
      group+pin ;; `value ≠ 0` flag block (module 22) ;; re-init cursor block
      (module 3).  `x8`/`x9`/`x21`/`x22`/`teer_inner_off` are framed through the
      `value` block (untouched there) and consumed by the re-init block, which
      reloads `teer_inner_off` into `x6` (one owned-register unbundle) and
      recomputes the inner-payload cursor `x21 = x8 + inner_off`, length
      `x22 = x9 - inner_off`.

    * `teer_authwalk_full_spec` (`teerB + 440 → {2856, 676}`): the auth-list
      walk segment through walk-9 (`teer_authwalk_seg_spec`, module 25) ;; the
      final `rlp_walk_next`@161 group ;; `authlist_setup` boundary
      (`teer_walknext161_authlist_spec`, module 24), joined via the scratch
      adaptor + `hoc10` cursor correspondence + `∃ len` join, mirroring
      `teer_alglue_extend`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix25

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## `value` walk ;; `value ≠ 0` flag ;; re-init cursor (`teerB + 388 → {2856, 440}`) -/

set_option maxRecDepth 8000 in
/-- **`value` walk group+pin ;; `value ≠ 0` flag ;; re-init cursor**
    (`teerB + 388 → {2856, 440}`).  Chains `teer_walknext97_value_spec`
    (module 22, `teerB + 388 → 412`) onto the re-init cursor block
    (`teer_reinit_cursor_spec`, module 3, `teerB + 412 → 440`).  `x8`/`x9`/
    `x21`/`x22`/`teer_inner_off` frame through the `value` block and are consumed
    by the re-init; the block reloads `teer_inner_off` into `x6` (one owned
    unbundle) and recomputes the inner-payload cursor/length. -/
theorem teer_value_reinit_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (vno v8 v9 v21o v22o ioff : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin ((((1 + 87) + 1) + 4) + 7) (teerB + 388) fullCode
      ((((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes)) **
        (teerValueNonzero ↦ₘ vno)) **
        ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o) **
          (teerInnerOff ↦ₘ ioff)))
      (teerB + 2856) teerFail
      (teerB + 440)
      (fun h => ∃ len : Word,
        (((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x5 ↦ᵣ teerInnerOff) ** (.x6 ↦ᵣ ioff) **
            (.x10 ↦ᵣ (v8 + ioff)) ** (.x11 ↦ᵣ (v9 - ioff)) **
            (.x21 ↦ᵣ (v8 + ioff)) ** (.x22 ↦ᵣ (v9 - ioff)) **
            (teerInnerOff ↦ₘ ioff)) **
          ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
            (.x30 ↦ᵣ (if BitVec.ult (0 : Word) len then (1 : Word) else 0)) **
            (.x1 ↦ᵣ (teerB + 392)) **
            regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
            bytesRegion srcBase srcBytes **
            (teerValueNonzero ↦ₘ (if BitVec.ult (0 : Word) len then (1 : Word) else 0)))) h) := by
  -- Block 1: the `value` walk group+pin ;; flag block, framed with x8/x9/x21/x22/inner_off.
  have h1 := cpsBranchWithin_frameR
    ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o) ** (teerInnerOff ↦ₘ ioff))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    (teer_walknext97_value_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn vno srcBytes srcOff halign hoff hover hvalid C hc)
  -- Block 2: the re-init cursor block, unbundling x6, framing the carried cells.
  have h2 : cpsTripleWithin 7 (teerB + 412) (teerB + 440) fullCode
      (fun h => ∃ len : Word,
        ((((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
              (.x30 ↦ᵣ (if BitVec.ult (0 : Word) len then (1 : Word) else 0)) **
              (.x5 ↦ᵣ teerValueNonzero)) **
            ((.x1 ↦ᵣ (teerB + 392)) **
              regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
              bytesRegion srcBase srcBytes) **
            (teerValueNonzero ↦ₘ (if BitVec.ult (0 : Word) len then (1 : Word) else 0))) **
          ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o) **
            (teerInnerOff ↦ₘ ioff))) h)
      (fun h => ∃ len : Word,
        (((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x5 ↦ᵣ teerInnerOff) ** (.x6 ↦ᵣ ioff) **
            (.x10 ↦ᵣ (v8 + ioff)) ** (.x11 ↦ᵣ (v9 - ioff)) **
            (.x21 ↦ᵣ (v8 + ioff)) ** (.x22 ↦ᵣ (v9 - ioff)) **
            (teerInnerOff ↦ₘ ioff)) **
          ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
            (.x30 ↦ᵣ (if BitVec.ult (0 : Word) len then (1 : Word) else 0)) **
            (.x1 ↦ᵣ (teerB + 392)) **
            regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
            bytesRegion srcBase srcBytes **
            (teerValueNonzero ↦ₘ (if BitVec.ult (0 : Word) len then (1 : Word) else 0)))) h) := by
    apply cpsTripleWithin_exists_pre_gen
    intro len
    have hre : cpsTripleWithin 7 (teerB + 412) (teerB + 440) fullCode
        (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
            (.x30 ↦ᵣ (if BitVec.ult (0 : Word) len then (1 : Word) else 0)) **
            (.x5 ↦ᵣ teerValueNonzero) ** (.x1 ↦ᵣ (teerB + 392)) **
            regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
            bytesRegion srcBase srcBytes **
            (teerValueNonzero ↦ₘ (if BitVec.ult (0 : Word) len then (1 : Word) else 0)) **
            (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o) **
            (teerInnerOff ↦ₘ ioff)) **
          regOwn .x6)
        (fun h =>
          (((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x5 ↦ᵣ teerInnerOff) ** (.x6 ↦ᵣ ioff) **
              (.x10 ↦ᵣ (v8 + ioff)) ** (.x11 ↦ᵣ (v9 - ioff)) **
              (.x21 ↦ᵣ (v8 + ioff)) ** (.x22 ↦ᵣ (v9 - ioff)) **
              (teerInnerOff ↦ₘ ioff)) **
            ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
              (.x30 ↦ᵣ (if BitVec.ult (0 : Word) len then (1 : Word) else 0)) **
              (.x1 ↦ᵣ (teerB + 392)) **
              regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
              bytesRegion srcBase srcBytes **
              (teerValueNonzero ↦ₘ (if BitVec.ult (0 : Word) len then (1 : Word) else 0)))) h) := by
      apply cpsTripleWithin_of_forall_regIs_to_regOwn
      intro v6
      exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
        (cpsTripleWithin_frameR
          ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
            (.x30 ↦ᵣ (if BitVec.ult (0 : Word) len then (1 : Word) else 0)) **
            (.x1 ↦ᵣ (teerB + 392)) **
            regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
            bytesRegion srcBase srcBytes **
            (teerValueNonzero ↦ₘ (if BitVec.ult (0 : Word) len then (1 : Word) else 0)))
          (by repeat' first
              | exact pcFree_regIs | exact pcFree_memIs | exact pcFree_regOwn
              | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj)
          (cpsTripleWithin_extend_code teer_mono
            (teer_reinit_cursor_spec v8 v9 teerValueNonzero v6 C (0 : Word) v21o v22o ioff)))
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ⟨len, by xperm_hyp hq⟩)
      hre
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1 (fun h hq => sepConj_exists_left h hq) h2 (fun h hq => to_teerFail _ h hq)

/-! ## Auth-list walk full segment (`teerB + 440 → {2856, 676}`) -/

set_option maxRecDepth 8000 in
/-- **Auth-list walk full segment** (`teerB + 440 → {2856, 676}`).  Chains
    `teer_authwalk_seg_spec` (module 25, `teerB + 440 → 644`) onto the final
    `rlp_walk_next`@161 group ;; `authlist_setup` boundary
    (`teer_walknext161_authlist_spec`, module 24, `teerB + 644 → 676`) via the
    scratch adaptor + walk-10 cursor correspondence `hoc10`, mirroring
    `teer_alglue_extend`. -/
theorem teer_authwalk_full_spec (wi : RlpWalkInitAssumed fullCode)
    (hwi : wi.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_init)
    (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (v21o v22o : Word)
    (listBytes : List (BitVec 8))
    (listOff srcOff1 srcOff2 srcOff3 srcOff4 srcOff5 srcOff6 srcOff7 srcOff8 srcOff9
      srcOff10 : Nat)
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
    (hoff10 : srcOff10 < listBytes.length) (hover10 : listBase.toNat + srcOff10 < 2 ^ 64)
    (hvalid10 : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff10) = true)
    (C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 : Word)
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
    (hoc10 : listBase + BitVec.ofNat 64 srcOff10 = C9)
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
        next len → next = C9)
    (hcw10 : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode listBytes srcOff10
        (listBase + BitVec.ofNat 64 srcOff10) ((listBase + BitVec.ofNat 64 listOff) + listLen)
        next len → next = C10) :
    cpsBranchWithin
      ((((((1 + 81) + 1) + 4) + (((1 + 87) + 1) + 3)) +
        ((((1 + 87) + 1) + 3) + ((((1 + 87) + 1) + 3) + ((((1 + 87) + 1) + 3) +
          ((((1 + 87) + 1) + 3) + ((((1 + 87) + 1) + 3) + ((((1 + 87) + 1) + 3) +
            ((((1 + 87) + 1) + 3) + (((1 + 87) + 1) + 3))))))))) +
        (((1 + 87) + 1) + 6))
      (teerB + 440) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes)) **
        ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o)))
      (teerB + 2856) teerFail (teerB + 676)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ (C10 - len)) ** (.x11 ↦ᵣ len) ** (.x12 ↦ᵣ teerAuthCount) **
            (.x21 ↦ᵣ (C10 - len)) ** (.x22 ↦ᵣ len)) **
          ((.x1 ↦ᵣ (teerB + 648)) ** teerWalkScratch listBase listBytes)) h) := by
  have hseg := teer_authwalk_seg_spec wi hwi wn hwn listBase listLen a2Old t0Old t1Old t2Old
    t3Old t4Old t5Old t6Old raIn v21o v22o listBytes listOff srcOff1 srcOff2 srcOff3 srcOff4
    srcOff5 srcOff6 srcOff7 srcOff8 srcOff9 halign hoff hover hvalid hoff1 hover1 hvalid1
    hoff2 hover2 hvalid2 hoff3 hover3 hvalid3 hoff4 hover4 hvalid4 hoff5 hover5 hvalid5
    hoff6 hover6 hvalid6 hoff7 hover7 hvalid7 hoff8 hover8 hvalid8 hoff9 hover9 hvalid9
    C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 hc1 hc2 hoc1 hoc2 hoc3 hoc4 hoc5 hoc6 hoc7 hoc8 hoc9
    hcw1 hcw2 hcw3 hcw4 hcw5 hcw6 hcw7 hcw8 hcw9
  have hB : ∀ len : Word,
      cpsBranchWithin (((1 + 87) + 1) + 6) (teerB + 644) fullCode
        (((.x1 ↦ᵣ (teerB + 628)) **
          ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff10)) **
            (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
            (.x12 ↦ᵣ len) ** teerWalkScratch listBase listBytes)) **
          ((.x21 ↦ᵣ C9) ** (.x22 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen))))
        (teerB + 2856) teerFail (teerB + 676)
        (fun h => ∃ len' : Word,
          (((.x10 ↦ᵣ (C10 - len')) ** (.x11 ↦ᵣ len') ** (.x12 ↦ᵣ teerAuthCount) **
              (.x21 ↦ᵣ (C10 - len')) ** (.x22 ↦ᵣ len')) **
            ((.x1 ↦ᵣ (teerB + 648)) ** teerWalkScratch listBase listBytes)) h) := by
    intro len
    exact teer_walk_scratch_regOwn_adaptor (teerB + 628)
      (listBase + BitVec.ofNat 64 srcOff10) ((listBase + BitVec.ofNat 64 listOff) + listLen)
      len listBase listBytes
      ((.x21 ↦ᵣ C9) ** (.x22 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)))
      (fun t0 t1 t2 t3 t4 t5 t6 =>
        teer_walknext161_authlist_spec wn hwn listBase
          ((listBase + BitVec.ofNat 64 listOff) + listLen) len t0 t1 t2 t3 t4 t5 t6
          (teerB + 628) C9 ((listBase + BitVec.ofNat 64 listOff) + listLen) listBytes srcOff10
          halign hoff10 hover10 hvalid10 C10 hcw10)
  exact cpsBranchWithin_seq_cpsBranchWithin_with_perm_same_cr hseg
    (fun h hq => by
      obtain ⟨len, hbody⟩ := hq
      exact ⟨len, by rw [hoc10]; xperm_hyp hbody⟩)
    (cpsBranchWithin_exists_pre hB)
    (fun h hq => to_teerFail _ h hq) (fun h hq => to_teerFail _ h hq)

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
