/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix20

  PASS 11 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  Extends the 6-walk `to`/value-walk segment through walks 3/4/5
  (`teerB + 216 → 300 → 320 → 340`) by chaining the `walknext70/75/80 ;;
  toglueK` compositions (module 19) onto `teer_walk012_spec` (module 19).  Each
  boundary join is the established `∃ len` branch-branch recipe:
  `cpsBranchWithin_exists_pre` to thread the incoming content length into the
  next group's `x12`, `teer_walk_scratch_regOwn_adaptor` to bridge the scratch
  ownership, and the parse-success offset correspondence
  `listBase + srcOff = C_prev` to align the cursor.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix19

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## One-step `to`-walk segment extension combinator

    Chains a segment branch (`teerB + 216 → prevPC`, fall post = the pinned
    walk cursor `Cprev`/end `endc` with the `∃ len` content length and the
    walk scratch) onto a `walknextNN ;; toglueK` block, threading `∃ len` into
    the next group's `x12`, adapting the scratch, and aligning the cursor via
    the offset correspondence.  The `to`-walk keeps its snapshot cursor in `x24`
    and (fixed) end in `x25`. -/
set_option maxRecDepth 8000 in
theorem teer_towalk_extend
    {nPrev : Nat} {prevPC nextPC : Word}
    (Cprev Cnext endc raPrev nextMid : Word)
    (srcBase : Word) (srcBytes : List (BitVec 8)) (srcOffNext : Nat)
    (P : Assertion)
    (hoc : srcBase + BitVec.ofNat 64 srcOffNext = Cprev)
    (hprev : cpsBranchWithin nPrev (teerB + 216) fullCode P
      (teerB + 2856) teerFail prevPC
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ Cprev) ** (.x11 ↦ᵣ endc) ** (.x24 ↦ᵣ Cprev) ** (.x25 ↦ᵣ endc)) **
          ((.x1 ↦ᵣ raPrev) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len))) h))
    (hnextAll : ∀ len t0 t1 t2 t3 t4 t5 t6 : Word,
      cpsBranchWithin (((1 + 87) + 1) + 3) prevPC fullCode
        (((.x1 ↦ᵣ raPrev) **
          ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOffNext)) ** (.x11 ↦ᵣ endc) **
            (.x12 ↦ᵣ len) **
            (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) ** (.x28 ↦ᵣ t3) **
            (.x29 ↦ᵣ t4) ** (.x30 ↦ᵣ t5) ** (.x31 ↦ᵣ t6) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion srcBase srcBytes)) **
          ((.x24 ↦ᵣ Cprev) ** (.x25 ↦ᵣ endc)))
        (teerB + 2856) teerFail nextPC
        (fun h => ∃ len' : Word,
          (((.x10 ↦ᵣ Cnext) ** (.x11 ↦ᵣ endc) ** (.x24 ↦ᵣ Cnext) ** (.x25 ↦ᵣ endc)) **
            ((.x1 ↦ᵣ nextMid) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len'))) h)) :
    cpsBranchWithin (nPrev + (((1 + 87) + 1) + 3)) (teerB + 216) fullCode P
      (teerB + 2856) teerFail nextPC
      (fun h => ∃ len' : Word,
        (((.x10 ↦ᵣ Cnext) ** (.x11 ↦ᵣ endc) ** (.x24 ↦ᵣ Cnext) ** (.x25 ↦ᵣ endc)) **
          ((.x1 ↦ᵣ nextMid) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len'))) h) := by
  have hB : ∀ len : Word,
      cpsBranchWithin (((1 + 87) + 1) + 3) prevPC fullCode
        (((.x1 ↦ᵣ raPrev) **
          ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOffNext)) ** (.x11 ↦ᵣ endc) **
            (.x12 ↦ᵣ len) ** teerWalkScratch srcBase srcBytes)) **
          ((.x24 ↦ᵣ Cprev) ** (.x25 ↦ᵣ endc)))
        (teerB + 2856) teerFail nextPC
        (fun h => ∃ len' : Word,
          (((.x10 ↦ᵣ Cnext) ** (.x11 ↦ᵣ endc) ** (.x24 ↦ᵣ Cnext) ** (.x25 ↦ᵣ endc)) **
            ((.x1 ↦ᵣ nextMid) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len'))) h) := by
    intro len
    exact teer_walk_scratch_regOwn_adaptor raPrev
      (srcBase + BitVec.ofNat 64 srcOffNext) endc len srcBase srcBytes
      ((.x24 ↦ᵣ Cprev) ** (.x25 ↦ᵣ endc))
      (fun t0 t1 t2 t3 t4 t5 t6 => hnextAll len t0 t1 t2 t3 t4 t5 t6)
  exact cpsBranchWithin_seq_cpsBranchWithin_with_perm_same_cr hprev
    (fun h hq => by
      obtain ⟨len, hbody⟩ := hq
      exact ⟨len, by rw [hoc]; xperm_hyp hbody⟩)
    (cpsBranchWithin_exists_pre hB)
    (fun h hq => to_teerFail _ h hq) (fun h hq => to_teerFail _ h hq)

/-! ## The `to`/value walk segment through walk-5 (`teerB + 216 → {2856, 340}`)

    Chains `teer_walk012_spec` with walks 3/4/5 via `teer_towalk_extend`.  Threads
    the five `to`-walk offsets and their parse-success cursor correspondences /
    forward-cursor facts. -/
set_option maxRecDepth 8000 in
theorem teer_towalk_seg_spec (wi : RlpWalkInitAssumed fullCode)
    (hwi : wi.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_init)
    (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (listBytes : List (BitVec 8))
    (listOff srcOff1 srcOff2 srcOff3 srcOff4 srcOff5 : Nat)
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
    (C0 C1 C2 C3 C4 C5 : Word)
    (hc1 : (listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) = C0)
    (hc2 : (listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)) = C0)
    (hoc1 : listBase + BitVec.ofNat 64 srcOff1 = C0)
    (hoc2 : listBase + BitVec.ofNat 64 srcOff2 = C1)
    (hoc3 : listBase + BitVec.ofNat 64 srcOff3 = C2)
    (hoc4 : listBase + BitVec.ofNat 64 srcOff4 = C3)
    (hoc5 : listBase + BitVec.ofNat 64 srcOff5 = C4)
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
        next len → next = C5) :
    cpsBranchWithin
      ((((((1 + 81) + 1) + 4) + (((1 + 87) + 1) + 3)) + (((1 + 87) + 1) + 3)) +
        (((1 + 87) + 1) + 3) + (((1 + 87) + 1) + 3) + (((1 + 87) + 1) + 3))
      (teerB + 216) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes)) **
        ((.x24 ↦ᵣ t0Old) ** (.x25 ↦ᵣ t1Old)))
      (teerB + 2856) teerFail
      (teerB + 340)
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ C5) ** (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
            (.x24 ↦ᵣ C5) ** (.x25 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen))) **
          ((.x1 ↦ᵣ (teerB + 324)) ** teerWalkScratch listBase listBytes **
            (.x12 ↦ᵣ len))) h) := by
  have hW012 := teer_walk012_spec wi hwi wn hwn listBase listLen a2Old t0Old t1Old t2Old
    t3Old t4Old t5Old t6Old raIn listBytes listOff srcOff1 srcOff2 halign hoff hover hvalid
    hoff1 hover1 hvalid1 hoff2 hover2 hvalid2 C0 C1 C2 hc1 hc2 hoc1 hoc2 hcw1 hcw2
  have hW0123 := teer_towalk_extend C2 C3
    ((listBase + BitVec.ofNat 64 listOff) + listLen) (teerB + 264) (teerB + 284)
    listBase listBytes srcOff3 _ hoc3 hW012
    (fun len t0 t1 t2 t3 t4 t5 t6 =>
      teer_walknext70_toglue3_spec wn hwn listBase
        ((listBase + BitVec.ofNat 64 listOff) + listLen) len t0 t1 t2 t3 t4 t5 t6
        (teerB + 264) C2 ((listBase + BitVec.ofNat 64 listOff) + listLen) listBytes srcOff3
        halign hoff3 hover3 hvalid3 C3 hcw3)
  have hW01234 := teer_towalk_extend C3 C4
    ((listBase + BitVec.ofNat 64 listOff) + listLen) (teerB + 284) (teerB + 304)
    listBase listBytes srcOff4 _ hoc4 hW0123
    (fun len t0 t1 t2 t3 t4 t5 t6 =>
      teer_walknext75_toglue4_spec wn hwn listBase
        ((listBase + BitVec.ofNat 64 listOff) + listLen) len t0 t1 t2 t3 t4 t5 t6
        (teerB + 284) C3 ((listBase + BitVec.ofNat 64 listOff) + listLen) listBytes srcOff4
        halign hoff4 hover4 hvalid4 C4 hcw4)
  have hW012345 := teer_towalk_extend C4 C5
    ((listBase + BitVec.ofNat 64 listOff) + listLen) (teerB + 304) (teerB + 324)
    listBase listBytes srcOff5 _ hoc5 hW01234
    (fun len t0 t1 t2 t3 t4 t5 t6 =>
      teer_walknext80_toglue5_spec wn hwn listBase
        ((listBase + BitVec.ofNat 64 listOff) + listLen) len t0 t1 t2 t3 t4 t5 t6
        (teerB + 304) C4 ((listBase + BitVec.ofNat 64 listOff) + listLen) listBytes srcOff5
        halign hoff5 hover5 hvalid5 C5 hcw5)
  exact hW012345

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
