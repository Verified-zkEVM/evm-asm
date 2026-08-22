/-
  EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelMachineArms

  Short/long-arm validate-call adapters and the `sharedCode ∪ validateCR`
  mono helpers for #12419 (split from RlpWalkNextStrictFuelMachineCont,
  itself split from RlpWalkNextStrictFuelMachine, for the Programs
  1500-line cap).
-/

import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelMachine

namespace EvmAsm.Codegen.RlpWalkNextStrictFuel

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP

/-! ## Core long-header bound split

The long-list header check is in the verified core, before control reaches the
shared list arm.  Its taken edge is the common status-3 block (`a1 = 3`,
`a2 = 0`); its fallthrough is the only edge on which the core may inspect the
length field.  Keep that fact as a two-exit branch contract rather than making
the header-fit predicate an input premise of `SharedListArmInputs`.
The latter would silently remove the measured truncated-header path.
-/

theorem shared_core_long_header_window_branch
    (endPtr headerEnd : Word) :
    cpsBranchWithin 1 (RlpWalkNextStrictTie.C + 56)
      RlpWalkNextStrictTie.coreCode
      ((regIs .x11 endPtr) ** (regIs .x29 headerEnd))
      (RlpWalkNextStrictTie.C + 364)
        ((regIs .x11 endPtr) ** (regIs .x29 headerEnd) **
          pure (BitVec.ult endPtr headerEnd))
      (RlpWalkNextStrictTie.C + 60)
        ((regIs .x11 endPtr) ** (regIs .x29 headerEnd) **
          pure (¬ BitVec.ult endPtr headerEnd)) := by
  have h := bltu_spec_gen_within .x11 .x29 (308 : BitVec 13)
    endPtr headerEnd (RlpWalkNextStrictTie.C + 56)
  rw [show RlpWalkNextStrictTie.C + 56 + signExtend13 (308 : BitVec 13) =
      RlpWalkNextStrictTie.C + 364 by
        rw [show signExtend13 (308 : BitVec 13) = (308 : Word) from by decide]
        bv_omega,
      show RlpWalkNextStrictTie.C + 56 + 4 = RlpWalkNextStrictTie.C + 60 by
        bv_omega] at h
  have hmono : ∀ a i,
      CodeReq.singleton (RlpWalkNextStrictTie.C + 56)
        (.BLTU .x11 .x29 (308 : BitVec 13)) a = some i →
      RlpWalkNextStrictTie.coreCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr
      RlpWalkNextStrictTie.C rlp_walk_next_prog 14
      (RlpWalkNextStrictTie.C + 56)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by bv_omega))
  exact cpsBranchWithin_extend_code hmono h

/-- The taken edge of `shared_core_long_header_window_branch` reaches the
    common core bound block.  This is kept public at the codegen layer so the
    shared wrapper can attach the concrete status-3 output, rather than
    treating the branch predicate as an unexplained caller premise. -/
theorem shared_core_long_header_bound_block
    (cursor endPtr raVal a2Old : Word) :
    cpsTripleWithin 3 (RlpWalkNextStrictTie.C + 364)
      (raVal &&& ~~~1) RlpWalkNextStrictTie.coreCode
      ((regIs .x10 cursor) ** (regIs .x11 endPtr) **
        (regIs .x12 a2Old) ** (regIs .x1 raVal))
      ((regIs .x10 cursor) ** (regIs .x11 (3 : Word)) **
        (regIs .x12 (0 : Word)) ** (regIs .x1 raVal)) := by
  have h0 := li_spec_gen_within .x11 endPtr (3 : Word)
    (RlpWalkNextStrictTie.C + 364) (by decide)
  have h1 := li_spec_gen_within .x12 a2Old (0 : Word)
    (RlpWalkNextStrictTie.C + 368) (by decide)
  have h2 := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12)
    (RlpWalkNextStrictTie.C + 372)
  simp only [signExtend12_0] at h2
  have hblock : cpsTripleWithin 3 (RlpWalkNextStrictTie.C + 364)
      (raVal &&& ~~~1) (rlp_walk_next_code RlpWalkNextStrictTie.C)
      ((regIs .x11 endPtr) ** (regIs .x12 a2Old) ** (regIs .x1 raVal))
      ((regIs .x11 (3 : Word)) ** (regIs .x12 (0 : Word)) **
        (regIs .x1 raVal)) := by
    runBlock h0 h1 h2
  have hblock' := cpsTripleWithin_frameR (regIs .x10 cursor)
    (by exact pcFree_regIs) hblock
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => by xperm_chunked hp) hblock'

/-! The region-backed loop edge.  The older `shared_long_prefix_one_iter`
    packages the loaded bytes in one dword atom, which is useful for the
    closed single-dword residual but cannot cover a length field crossing an
    eight-byte boundary.  This edge consumes `bytesRegion_lbu_within` instead;
    the caller supplies only the actual byte index and ordinary region facts.
-/

theorem shared_long_prefix_one_iter_region
    (base : Word) (bytes : List (BitVec 8)) (i : Nat)
    (acc cursor remaining oldByte : Word)
    (hne : remaining ≠ 0)
    (hcursor : cursor = base + BitVec.ofNat 64 i)
    (halign : base.toNat % 8 = 0)
    (hi : i < bytes.length)
    (hover : base.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess cursor = true) :
    cpsTripleWithin 7 (RlpWalkNextStrictTie.S + 108)
      (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
      ((regIs .x30 acc) ** (regIs .x29 cursor) **
        (regIs .x28 remaining) ** (regIs .x31 oldByte) **
        (regIs .x0 (0 : Word)) ** bytesRegion base bytes)
      ((regIs .x30
          ((acc <<< 8) ||| ((bytes[i]'hi).zeroExtend 64))) **
        (regIs .x29 (cursor + 1)) ** (regIs .x28 (remaining - 1)) **
        (regIs .x31 ((bytes[i]'hi).zeroExtend 64)) **
        (regIs .x0 (0 : Word)) ** bytesRegion base bytes) := by
  have hbr0 := shared_long_prefix_branch remaining
  have hntaken0 := cpsBranchWithin_ntakenStripPure2 hbr0 (by
    intro _ hQt
    obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
    exact absurd ((sepConj_pure_right _).mp h_rest).2 hne)
  have hntaken := cpsTripleWithin_frameR
    ((regIs .x30 acc) ** (regIs .x29 cursor) **
      (regIs .x31 oldByte) ** bytesRegion base bytes)
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _)
    hntaken0
  have hshift0 := shared_long_prefix_shift acc
  have hshift := cpsTripleWithin_frameR
    ((regIs .x29 cursor) ** (regIs .x28 remaining) **
      (regIs .x31 oldByte) ** (regIs .x0 (0 : Word)) **
      bytesRegion base bytes)
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _)
    hshift0
  have hregion_valid :
      isValidByteAccess (base + BitVec.ofNat 64 i) = true := by
    simpa [hcursor] using hvalid
  have hload0 := bytesRegion_lbu_within .x31 .x29 base oldByte
    (RlpWalkNextStrictTie.S + 116) bytes i (by decide)
    halign hi hover hregion_valid
  have hloadMono : ∀ a j,
      CodeReq.singleton (RlpWalkNextStrictTie.S + 116)
        (.LBU .x31 .x29 (0 : BitVec 12)) a = some j →
      RlpWalkNextStrictTie.sharedCode a = some j :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr
      RlpWalkNextStrictTie.S rlpWalkNextShared_prog 29
      (RlpWalkNextStrictTie.S + 116)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by bv_omega))
  have hload := cpsTripleWithin_extend_code hloadMono hload0
  have hload' :
      cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 116)
        (RlpWalkNextStrictTie.S + 120) RlpWalkNextStrictTie.sharedCode
        ((regIs .x29 cursor) ** (regIs .x31 oldByte) **
          bytesRegion base bytes)
        ((regIs .x29 cursor) **
          (regIs .x31 ((bytes[i]'hi).zeroExtend 64)) **
          bytesRegion base bytes) := by
    have hpc :
        BitVec.ofNat 64 GuestAddrs.rlp_walk_next_shared + 120 =
          BitVec.ofNat 64 GuestAddrs.rlp_walk_next_shared + 116 + 4 := by
      bv_omega
    convert hload using 1 <;> norm_num [hcursor, hpc]
  have hload'' := cpsTripleWithin_frameR
    ((regIs .x30 (acc <<< 8)) ** (regIs .x28 remaining) **
      (regIs .x0 (0 : Word)))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs)
    hload'
  have hacc0 := shared_long_prefix_accumulate_byte (acc <<< 8)
    ((bytes[i]'hi).zeroExtend 64)
  have hacc := cpsTripleWithin_frameR
    ((regIs .x29 cursor) ** (regIs .x28 remaining) **
      (regIs .x0 (0 : Word)) ** bytesRegion base bytes)
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _)
    hacc0
  have hcur0 := shared_long_prefix_cursor_increment cursor remaining
  have hcur := cpsTripleWithin_frameR
    ((regIs .x30
        ((acc <<< 8) ||| ((bytes[i]'hi).zeroExtend 64))) **
      (regIs .x31 ((bytes[i]'hi).zeroExtend 64)) **
      (regIs .x0 (0 : Word)) ** bytesRegion base bytes)
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _)
    hcur0
  have hdec0 := shared_long_prefix_decrement remaining (cursor + 1)
  have hdec := cpsTripleWithin_frameR
    ((regIs .x30
        ((acc <<< 8) ||| ((bytes[i]'hi).zeroExtend 64))) **
      (regIs .x31 ((bytes[i]'hi).zeroExtend 64)) **
      (regIs .x0 (0 : Word)) ** bytesRegion base bytes)
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _)
    hdec0
  have hback0 := shared_long_prefix_loop_backedge (cursor + 1) (remaining - 1)
  have hback := cpsTripleWithin_frameR
    ((regIs .x30
        ((acc <<< 8) ||| ((bytes[i]'hi).zeroExtend 64))) **
      (regIs .x31 ((bytes[i]'hi).zeroExtend 64)) **
      bytesRegion base bytes)
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _)
    hback0
  have s1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hntaken hshift
  have s2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s1 hload''
  have s3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s2 hacc
  have s4 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s3 hcur
  have s5 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s4 hdec
  have s6 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s5 hback
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => by xperm_chunked hp) s6

/-! The region-backed loop can be iterated at an arbitrary absolute byte
offset.  The offset is separate from the loop counter because the list
payload begins inside the caller-owned region (`listBase + 1`). -/

theorem shared_long_prefix_region_loop_exists
    (base : Word) (bytes : List (BitVec 8)) (n : Nat) (hn : n ≤ 8)
    (acc cursor oldByte stash : Word) (offset : Nat)
    (halign : base.toNat % 8 = 0)
    (hwin : ∀ i, i < n →
      cursor + BitVec.ofNat 64 i =
          base + BitVec.ofNat 64 (offset + i) ∧
        offset + i < bytes.length ∧
        base.toNat + (offset + i) < 2 ^ 64 ∧
        isValidByteAccess (base + BitVec.ofNat 64 (offset + i)) = true) :
    ∃ accOut cursorOut lastByte,
      cpsTripleWithin (7 * n) (RlpWalkNextStrictTie.S + 108)
        (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
        ((regIs .x30 acc) ** (regIs .x29 cursor) **
          (regIs .x28 (BitVec.ofNat 64 n)) ** (regIs .x13 stash) **
          (regIs .x31 oldByte) **
          (regIs .x0 (0 : Word)) ** bytesRegion base bytes)
        ((regIs .x30 accOut) ** (regIs .x29 cursorOut) **
          (regIs .x28 (0 : Word)) ** (regIs .x13 stash) **
          (regIs .x31 lastByte) **
          (regIs .x0 (0 : Word)) ** bytesRegion base bytes) := by
  induction n generalizing acc cursor oldByte offset with
  | zero =>
      refine ⟨acc, cursor, oldByte, ?_⟩
      have hrefl := cpsTripleWithin_refl
        (addr := RlpWalkNextStrictTie.S + 108)
        (P :=
          ((regIs .x30 acc) ** (regIs .x29 cursor) **
            (regIs .x28 (0 : Word)) ** (regIs .x13 stash) **
            (regIs .x31 oldByte) **
            (regIs .x0 (0 : Word)) ** bytesRegion base bytes))
        (fun _ hp => hp)
      have hcode := cpsTripleWithin_extend_code
        (cr := CodeReq.empty) (cr' := RlpWalkNextStrictTie.sharedCode)
        (fun _ _ h => nomatch h) hrefl
      exact hcode
  | succ k ih =>
      have hne := word_ofNat_succ_ne_zero' k (by omega)
      obtain ⟨hcursor0, hi0, hover0, hvalid0⟩ := hwin 0 (by omega)
      have hcursor0' : cursor = base + BitVec.ofNat 64 offset := by
        simpa using hcursor0
      have hi0' : offset < bytes.length := by simpa using hi0
      have hover0' : base.toNat + offset < 2 ^ 64 := by simpa using hover0
      have hvalid0' : isValidByteAccess cursor = true := by
        rw [hcursor0']
        simpa using hvalid0
      have hiter := shared_long_prefix_one_iter_region base bytes offset
        acc cursor (BitVec.ofNat 64 (k + 1)) oldByte hne hcursor0'
        halign hi0' hover0' hvalid0'
      have hwin' : ∀ i, i < k →
          (cursor + 1) + BitVec.ofNat 64 i =
              base + BitVec.ofNat 64 (offset + 1 + i) ∧
            offset + 1 + i < bytes.length ∧
            base.toNat + (offset + 1 + i) < 2 ^ 64 ∧
            isValidByteAccess
              (base + BitVec.ofNat 64 (offset + 1 + i)) = true := by
        intro i hi
        obtain ⟨hcursor_i, hi_i, hover_i, hvalid_i⟩ :=
          hwin (i + 1) (by omega)
        have hoff : offset + (i + 1) = offset + 1 + i := by omega
        rw [cursor_add_ofNat_succ cursor i, hoff] at hcursor_i
        rw [hoff] at hi_i hover_i hvalid_i
        exact ⟨hcursor_i, hi_i, hover_i, hvalid_i⟩
      obtain ⟨accOut, cursorOut, lastByte, hrest⟩ :=
        ih (hn := by omega)
          (acc :=
            ((acc <<< 8) ||| ((bytes[offset]'hi0).zeroExtend 64)))
          (cursor := cursor + 1)
          (oldByte := (bytes[offset]'hi0).zeroExtend 64)
          (offset := offset + 1) hwin'
      have hrem : BitVec.ofNat 64 (k + 1) - (1 : Word) =
          BitVec.ofNat 64 k := word_ofNat_succ_sub_one k
      have hiter' : cpsTripleWithin 7 (RlpWalkNextStrictTie.S + 108)
          (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
          ((regIs .x30 acc) ** (regIs .x29 cursor) **
            (regIs .x28 (BitVec.ofNat 64 (k + 1))) **
            (regIs .x13 stash) ** (regIs .x31 oldByte) **
            (regIs .x0 (0 : Word)) **
            bytesRegion base bytes)
          ((regIs .x30
              ((acc <<< 8) ||| ((bytes[offset]'hi0).zeroExtend 64))) **
            (regIs .x29 (cursor + 1)) **
            (regIs .x28 (BitVec.ofNat 64 k)) **
            (regIs .x13 stash) **
            (regIs .x31 ((bytes[offset]'hi0).zeroExtend 64)) **
            (regIs .x0 (0 : Word)) ** bytesRegion base bytes) := by
        rw [← hrem]
        have hiterF := cpsTripleWithin_frameR (regIs .x13 stash)
          (by exact pcFree_regIs) hiter
        exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
          (fun _ hp => by xperm_chunked hp) hiterF
      have hcomp := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_chunked hp) hiter' hrest
      have hsteps : 7 * (k + 1) = 7 + 7 * k := by omega
      refine ⟨accOut, cursorOut, lastByte, ?_⟩
      rw [hsteps]
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hp => by xperm_chunked hp) hcomp

/-! ## Short / long arms to the validate call at `S+156` -/

/-- Short-list arm: payload start + handoff, ready for `JAL` validate. -/
theorem shared_short_arm_to_validate_call
    (listBase oldPayload old10 : Word) :
    cpsTripleWithin 2 (RlpWalkNextStrictTie.S + 148)
      (RlpWalkNextStrictTie.S + 156) RlpWalkNextStrictTie.sharedCode
      ((regIs .x5 listBase) ** (regIs .x12 oldPayload) ** (regIs .x10 old10))
      ((regIs .x5 listBase) ** (regIs .x12 (listBase + 1)) **
        (regIs .x10 (listBase + 1))) := by
  have hstart0 := shared_short_list_payload_start listBase oldPayload
  have hstart := cpsTripleWithin_frameR (regIs .x10 old10)
    (by exact pcFree_regIs) hstart0
  have hhand0 := shared_payload_handoff (listBase + 1) old10
  have hhand := cpsTripleWithin_frameR (regIs .x5 listBase)
    (by exact pcFree_regIs) hhand0
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hstart hhand
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hseq

/-- Long-list payload setup through handoff: `S+136` → `S+156`. -/
theorem shared_long_payload_to_validate_call
    (cursor pfx oldOut old10 : Word) :
    cpsTripleWithin 4 (RlpWalkNextStrictTie.S + 136)
      (RlpWalkNextStrictTie.S + 156) RlpWalkNextStrictTie.sharedCode
      ((regIs .x12 oldOut) ** (regIs .x5 cursor) ** (regIs .x13 pfx) **
        (regIs .x10 old10))
      ((regIs .x12 (cursor + pfx + 1)) ** (regIs .x5 cursor) **
        (regIs .x13 pfx) ** (regIs .x10 (cursor + pfx + 1))) := by
  have hsetup0 := shared_long_prefix_zero_payload_setup cursor pfx oldOut
  have hsetup := cpsTripleWithin_frameR (regIs .x10 old10)
    (by exact pcFree_regIs) hsetup0
  have hhand0 := shared_payload_handoff (cursor + pfx + 1) old10
  have hhand := cpsTripleWithin_frameR
    ((regIs .x5 cursor) ** (regIs .x13 pfx))
    (by apply pcFree_sepConj <;> exact pcFree_regIs) hhand0
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hsetup hhand
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hseq

/-! Compose a dependent region-backed long-prefix loop with the remainder of
the long arm.  The loop witness is intentionally an explicit input here: it
is the child-indexed part to be supplied by the mutual induction builder, not
a hidden restriction on the arm.  In particular, this theorem only changes
the representation of the loop's readable bytes; it does not assume a
single-dword window or a header-fit outcome.
-/

theorem shared_long_prefix_region_to_validate_call
    (base : Word) (bytes : List (BitVec 8)) (n : Nat)
    (pfx listBase old7 oldRem old13 old29 oldAcc oldByte oldOut old10 : Word)
    (accOut cursorOut lastByte : Word)
    (hrem : pfx - 247 = BitVec.ofNat 64 n)
    (hloop :
      cpsTripleWithin (7 * n) (RlpWalkNextStrictTie.S + 108)
        (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
        ((regIs .x30 (0 : Word)) **
          (regIs .x29 (listBase + 1)) **
          (regIs .x28 (BitVec.ofNat 64 n)) **
          (regIs .x13 (BitVec.ofNat 64 n)) **
          (regIs .x31 oldByte) ** (regIs .x0 (0 : Word)) **
          bytesRegion base bytes)
        ((regIs .x30 accOut) ** (regIs .x29 cursorOut) **
          (regIs .x28 (0 : Word)) ** (regIs .x13 (BitVec.ofNat 64 n)) **
          (regIs .x31 lastByte) **
          (regIs .x0 (0 : Word)) ** bytesRegion base bytes)) :
    cpsTripleWithin (5 + (7 * n + 1) + 4) (RlpWalkNextStrictTie.S + 88)
      (RlpWalkNextStrictTie.S + 156) RlpWalkNextStrictTie.sharedCode
      ((regIs .x6 pfx) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
        (regIs .x13 old13) ** (regIs .x5 listBase) **
        (regIs .x29 old29) ** (regIs .x30 oldAcc) **
        (regIs .x31 oldByte) ** (regIs .x12 oldOut) **
        (regIs .x10 old10) ** (regIs .x0 (0 : Word)) **
        bytesRegion base bytes)
      ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
        (regIs .x28 (0 : Word)) **
        (regIs .x13 (BitVec.ofNat 64 n)) **
        (regIs .x5 listBase) ** (regIs .x29 cursorOut) **
        (regIs .x30 accOut) ** (regIs .x31 lastByte) **
        (regIs .x12 (listBase + BitVec.ofNat 64 n + 1)) **
        (regIs .x10 (listBase + BitVec.ofNat 64 n + 1)) **
        (regIs .x0 (0 : Word)) ** bytesRegion base bytes) := by
  have hpre0 := shared_long_prefix_preamble
    pfx listBase old7 oldRem old13 old29 oldAcc
  have hpre := cpsTripleWithin_frameR
    ((regIs .x12 oldOut) ** (regIs .x10 old10) **
      (regIs .x31 oldByte) ** (regIs .x0 (0 : Word)) **
      bytesRegion base bytes)
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _)
    hpre0
  have hpreN :
      cpsTripleWithin 5 (RlpWalkNextStrictTie.S + 88)
        (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
        (((regIs .x6 pfx) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
          (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
          (regIs .x30 oldAcc)) ** (regIs .x12 oldOut) **
          (regIs .x10 old10) **
          (regIs .x31 oldByte) ** (regIs .x0 (0 : Word)) **
          bytesRegion base bytes)
        (((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
          (regIs .x28 (BitVec.ofNat 64 n)) **
          (regIs .x13 (BitVec.ofNat 64 n)) **
          (regIs .x5 listBase) ** (regIs .x29 (listBase + 1)) **
          (regIs .x30 (0 : Word))) ** (regIs .x12 oldOut) **
          (regIs .x10 old10) ** (regIs .x31 oldByte) **
          (regIs .x0 (0 : Word)) ** bytesRegion base bytes) := by
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hp => by rw [← hrem]; exact hp) hpre
  have hbr0 := shared_long_prefix_branch (0 : Word)
  have htaken0 := cpsBranchWithin_takenStripPure2 hbr0 (by
    intro _ hQf
    obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
    exact absurd rfl ((sepConj_pure_right _).mp h_rest).2)
  have htaken := cpsTripleWithin_frameR
    ((regIs .x30 accOut) ** (regIs .x29 cursorOut) **
      (regIs .x13 (BitVec.ofNat 64 n)) ** (regIs .x31 lastByte) **
      bytesRegion base bytes)
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _)
    htaken0
  have hloopExit0 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hloop htaken
  have hloopExit := cpsTripleWithin_frameR
    ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
      (regIs .x5 listBase) ** (regIs .x12 oldOut) **
      (regIs .x10 old10))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs)
    hloopExit0
  have hto0 := shared_long_payload_to_validate_call
    listBase (BitVec.ofNat 64 n) oldOut old10
  have hto := cpsTripleWithin_frameR
    ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
      (regIs .x28 (0 : Word)) ** (regIs .x29 cursorOut) **
      (regIs .x30 accOut) ** (regIs .x31 lastByte) **
      (regIs .x0 (0 : Word)) ** bytesRegion base bytes)
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _)
    hto0
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hpreN hloopExit
  have hseq' := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hseq hto
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => by xperm_chunked hp) hseq'

/-! The builder-facing form obtains the loop witness from the per-byte region
induction.  `offset` is the absolute offset of `listBase + 1` in the caller's
region; this is the relation that lets the loop cross dword boundaries. -/

theorem shared_long_prefix_region_to_validate_call_exists
    (base : Word) (bytes : List (BitVec 8)) (n : Nat) (hn : n ≤ 8)
    (pfx listBase old7 oldRem old13 old29 oldAcc oldByte oldOut old10 : Word)
    (offset : Nat) (hrem : pfx - 247 = BitVec.ofNat 64 n)
    (halign : base.toNat % 8 = 0)
    (hwin : ∀ i, i < n →
      (listBase + 1) + BitVec.ofNat 64 i =
          base + BitVec.ofNat 64 (offset + i) ∧
        offset + i < bytes.length ∧
        base.toNat + (offset + i) < 2 ^ 64 ∧
        isValidByteAccess
          (base + BitVec.ofNat 64 (offset + i)) = true) :
    ∃ accOut cursorOut lastByte,
      cpsTripleWithin (5 + (7 * n + 1) + 4) (RlpWalkNextStrictTie.S + 88)
        (RlpWalkNextStrictTie.S + 156) RlpWalkNextStrictTie.sharedCode
        ((regIs .x6 pfx) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
          (regIs .x13 old13) ** (regIs .x5 listBase) **
          (regIs .x29 old29) ** (regIs .x30 oldAcc) **
          (regIs .x31 oldByte) ** (regIs .x12 oldOut) **
          (regIs .x10 old10) ** (regIs .x0 (0 : Word)) **
          bytesRegion base bytes)
        ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
          (regIs .x28 (0 : Word)) **
          (regIs .x13 (BitVec.ofNat 64 n)) **
          (regIs .x5 listBase) ** (regIs .x29 cursorOut) **
          (regIs .x30 accOut) ** (regIs .x31 lastByte) **
          (regIs .x12 (listBase + BitVec.ofNat 64 n + 1)) **
          (regIs .x10 (listBase + BitVec.ofNat 64 n + 1)) **
          (regIs .x0 (0 : Word)) ** bytesRegion base bytes) := by
  obtain ⟨accOut, cursorOut, lastByte, hloop⟩ :=
    shared_long_prefix_region_loop_exists base bytes n hn (0 : Word)
      (listBase + 1) oldByte (BitVec.ofNat 64 n) offset halign hwin
  exact ⟨accOut, cursorOut, lastByte,
    shared_long_prefix_region_to_validate_call base bytes n
      pfx listBase old7 oldRem old13 old29 oldAcc oldByte oldOut old10
      accOut cursorOut lastByte hrem hloop⟩

/-! Consume the selector's successful long-header result.  The loop's source
    window starts at `cursorOff + 1`; every byte is therefore justified by the
    core's successful header-fit fact and the caller's byte-access predicate.
    No header relation is added to `SharedListArmInputs`: it is published by
    `SharedListSelection.hlongHeader` and consumed here. -/
theorem shared_long_prefix_region_from_selector
    {bytes : List (BitVec 8)} {base : Word} {floor parentFuel : Nat}
    {cursorOff endOff : Nat}
    {spV sp raVal exit_ endPtr pfx listBase depth : Word}
    {oldPayload old10 oldOut old7 oldRem old13 old29 oldAcc : Word}
    {P : Assertion} (accOld byteOld : Word)
    (h : SharedListArmInputs bytes base floor parentFuel cursorOff endOff spV sp
      raVal exit_ endPtr pfx listBase depth oldPayload old10 oldOut old7
      oldRem old13 old29 oldAcc P)
    (n : Nat) (hn : n ≤ 8)
    (hrem : pfx - (247 : Word) = BitVec.ofNat 64 n)
    (hpayloadStart : h.selector.payloadStart = cursorOff + 1 + n)
    (hheaderFit : cursorOff + n < endOff) :
    ∃ accOut cursorOut lastByte,
      cpsTripleWithin (5 + (7 * n + 1) + 4) (RlpWalkNextStrictTie.S + 88)
        (RlpWalkNextStrictTie.S + 156) RlpWalkNextStrictTie.sharedCode
        (((regIs .x6 pfx) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
          (regIs .x13 old13) ** (regIs .x5 listBase) **
          (regIs .x29 old29) ** (regIs .x30 accOld) **
          (regIs .x31 byteOld) ** (regIs .x12 oldOut) **
          (regIs .x10 old10) ** (regIs .x0 (0 : Word)) **
          bytesRegion base bytes) ** P)
        (((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
          (regIs .x28 (0 : Word)) **
          (regIs .x13 (BitVec.ofNat 64 n)) ** (regIs .x5 listBase) **
          (regIs .x29 cursorOut) ** (regIs .x30 accOut) **
          (regIs .x31 lastByte) **
          (regIs .x12 (listBase + BitVec.ofNat 64 n + 1)) **
          (regIs .x10 (listBase + BitVec.ofNat 64 n + 1)) **
          (regIs .x0 (0 : Word)) ** bytesRegion base bytes) ** P) := by
  have hwin : ∀ i, i < n →
      (listBase + 1) + BitVec.ofNat 64 i =
          base + BitVec.ofNat 64 (cursorOff + 1 + i) ∧
        cursorOff + 1 + i < bytes.length ∧
        base.toNat + (cursorOff + 1 + i) < 2 ^ 64 ∧
        isValidByteAccess
          (base + BitVec.ofNat 64 (cursorOff + 1 + i)) = true := by
    intro i hi
    have hfit_i0 : cursorOff + 1 + i ≤ cursorOff + n := by omega
    have hfit_i : cursorOff + 1 + i < endOff :=
      lt_of_le_of_lt hfit_i0 hheaderFit
    have hlen_i : cursorOff + 1 + i < bytes.length :=
      lt_of_lt_of_le hfit_i h.selector.houter
    have hsum : base.toNat + (cursorOff + 1 + i) <
        base.toNat + bytes.length := Nat.add_lt_add_left hlen_i _
    have hover_i : base.toNat + (cursorOff + 1 + i) < 2 ^ 64 :=
      lt_trans hsum h.hover
    have hvalid_i := h.hvalid (cursorOff + 1 + i) hfit_i
    refine ⟨?_, hlen_i, hover_i, hvalid_i⟩
    rw [h.hlistBase]
    bv_omega
  obtain ⟨accOut, cursorOut, lastByte, hcall⟩ :=
    shared_long_prefix_region_to_validate_call_exists base bytes n hn
      pfx listBase old7 oldRem old13 old29 accOld byteOld oldOut old10
      (cursorOff + 1) hrem h.hbase_aligned hwin
  refine ⟨accOut, cursorOut, lastByte, ?_⟩
  exact cpsTripleWithin_frameR P h.hP hcall

/-! The owner-facing form of the selector arm.  The concrete loop theorem
    above is intentionally precise about the accumulator, cursor, and last
    byte it produces.  The caller only needs those three registers as owned
    scratch after the loop, so peel the two input scratch registers and weaken
    the three concrete outputs here. -/
theorem shared_long_prefix_region_from_selector_own
    {bytes : List (BitVec 8)} {base : Word} {floor parentFuel : Nat}
    {cursorOff endOff : Nat}
    {spV sp raVal exit_ endPtr pfx listBase depth : Word}
    {oldPayload old10 oldOut old7 oldRem old13 old29 oldAcc : Word}
    {P : Assertion} (h : SharedListArmInputs bytes base floor parentFuel cursorOff endOff spV sp
      raVal exit_ endPtr pfx listBase depth oldPayload old10 oldOut old7
      oldRem old13 old29 oldAcc P)
    (n : Nat) (hn : n ≤ 8)
    (hrem : pfx - (247 : Word) = BitVec.ofNat 64 n)
    (hpayloadStart : h.selector.payloadStart = cursorOff + 1 + n)
    (hheaderFit : cursorOff + n < endOff) :
    cpsTripleWithin (5 + (7 * n + 1) + 4) (RlpWalkNextStrictTie.S + 88)
      (RlpWalkNextStrictTie.S + 156) RlpWalkNextStrictTie.sharedCode
      (((regIs .x6 pfx) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
        (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
        (regOwn .x30) ** (regOwn .x31) ** (regIs .x12 oldOut) **
        (regIs .x10 old10) ** (regIs .x0 (0 : Word)) **
        bytesRegion base bytes) ** P)
      (((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
        (regIs .x28 (0 : Word)) ** (regIs .x13 (BitVec.ofNat 64 n)) **
        (regIs .x5 listBase) ** (regOwn .x29) ** (regOwn .x30) **
        (regOwn .x31) ** (regIs .x12 (listBase + BitVec.ofNat 64 n + 1)) **
        (regIs .x10 (listBase + BitVec.ofNat 64 n + 1)) **
        (regIs .x0 (0 : Word)) ** bytesRegion base bytes) ** P) := by
  have hconcrete : ∀ accOld byteOld,
      cpsTripleWithin (5 + (7 * n + 1) + 4) (RlpWalkNextStrictTie.S + 88)
        (RlpWalkNextStrictTie.S + 156) RlpWalkNextStrictTie.sharedCode
        (((regIs .x6 pfx) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
          (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
          (regIs .x12 oldOut) ** (regIs .x10 old10) **
          (regIs .x0 (0 : Word)) ** bytesRegion base bytes ** P) **
          (regIs .x30 accOld) ** (regIs .x31 byteOld))
        (((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
          (regIs .x28 (0 : Word)) ** (regIs .x13 (BitVec.ofNat 64 n)) **
          (regIs .x5 listBase) ** (regOwn .x29) ** (regOwn .x30) **
          (regOwn .x31) ** (regIs .x12 (listBase + BitVec.ofNat 64 n + 1)) **
          (regIs .x10 (listBase + BitVec.ofNat 64 n + 1)) **
          (regIs .x0 (0 : Word)) ** bytesRegion base bytes) ** P) := by
    intro accOld byteOld
    obtain ⟨accOut, cursorOut, lastByte, hloop⟩ :=
      shared_long_prefix_region_from_selector accOld byteOld h n hn hrem
        hpayloadStart hheaderFit
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => ?_) hloop
    have hinner : ∀ hs,
        ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
          (regIs .x28 (0 : Word)) ** (regIs .x13 (BitVec.ofNat 64 n)) **
          (regIs .x5 listBase) ** (regIs .x29 cursorOut) **
          (regIs .x30 accOut) ** (regIs .x31 lastByte) **
          (regIs .x12 (listBase + BitVec.ofNat 64 n + 1)) **
          (regIs .x10 (listBase + BitVec.ofNat 64 n + 1)) **
          (regIs .x0 (0 : Word)) ** bytesRegion base bytes) hs →
        ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
          (regIs .x28 (0 : Word)) ** (regIs .x13 (BitVec.ofNat 64 n)) **
          (regIs .x5 listBase) ** (regOwn .x29) ** (regOwn .x30) **
          (regOwn .x31) **
          (regIs .x12 (listBase + BitVec.ofNat 64 n + 1)) **
          (regIs .x10 (listBase + BitVec.ofNat 64 n + 1)) **
          (regIs .x0 (0 : Word)) ** bytesRegion base bytes) hs := by
      intro hs hp
      exact (sepConj_mono (fun _ x => x)
        (sepConj_mono (fun _ x => x)
          (sepConj_mono (fun _ x => x)
            (sepConj_mono (fun _ x => x)
              (sepConj_mono (fun _ x => x)
                (sepConj_mono (regIs_implies_regOwn .x29)
                  (sepConj_mono (regIs_implies_regOwn .x30)
                    (sepConj_mono (regIs_implies_regOwn .x31)
                      (fun _ x => x))))))))) hs hp
    have hp' := (sepConj_mono_left hinner) _ hp
    exact hp'
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hp => hp)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x31)
      (P := ((regIs .x6 pfx) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
        (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
        (regIs .x12 oldOut) ** (regIs .x10 old10) **
        (regIs .x0 (0 : Word)) ** bytesRegion base bytes ** P) **
        (regOwn .x30)) (fun byteOld => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hp => hp)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x30)
      (P := ((regIs .x6 pfx) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
        (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
        (regIs .x12 oldOut) ** (regIs .x10 old10) **
        (regIs .x0 (0 : Word)) ** bytesRegion base bytes ** P) **
        (regIs .x31 byteOld)) (fun accOld => ?_))
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
    (hconcrete accOld byteOld)

/-- Zero-length long-prefix arm from loop entry through validate call:
`remaining = 0` at `S+108` → payload setup → `S+156`. -/
theorem shared_long_zero_remaining_to_validate_call
    (cursor pfx oldOut old10 oldAcc : Word) :
    cpsTripleWithin 6 (RlpWalkNextStrictTie.S + 104)
      (RlpWalkNextStrictTie.S + 156) RlpWalkNextStrictTie.sharedCode
      ((regIs .x30 oldAcc) ** (regIs .x28 (0 : Word)) **
        (regIs .x0 (0 : Word)) ** (regIs .x12 oldOut) **
        (regIs .x5 cursor) ** (regIs .x13 pfx) ** (regIs .x10 old10))
      ((regIs .x30 (0 : Word)) ** (regIs .x28 (0 : Word)) **
        (regIs .x0 (0 : Word)) ** (regIs .x12 (cursor + pfx + 1)) **
        (regIs .x5 cursor) ** (regIs .x13 pfx) **
        (regIs .x10 (cursor + pfx + 1))) := by
  have hexit0 := shared_long_prefix_zero_remaining_to_payload_base oldAcc
  have hexit := cpsTripleWithin_frameR
    ((regIs .x12 oldOut) ** (regIs .x5 cursor) ** (regIs .x13 pfx) **
      (regIs .x10 old10))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs)
    hexit0
  have hto0 := shared_long_payload_to_validate_call cursor pfx oldOut old10
  have hto := cpsTripleWithin_frameR
    ((regIs .x30 (0 : Word)) ** (regIs .x28 (0 : Word)) **
      (regIs .x0 (0 : Word)))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs)
    hto0
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hexit hto
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hseq

/-- Short arm through the validate call return at `S+160`, under an abstract
validate callee.  Code is `sharedCode ∪ validateCR` so the setup (shared) and
call (singleton ⊆ shared ∪ validate) share one `CodeReq`.  Continuation after
`S+160` (depth-dec + status) remains open under `SharedListArmsFromValidateGoal`. -/
theorem shared_short_arm_validate_call
    {nVal : Nat} {α : Type} {P : Assertion} {post : α → Assertion}
    (listBase oldPayload old10 oldRa : Word)
    (hP : P.pcFree)
    (hval : cpsTripleWithin nVal (GuestAddrs.rlp_validate_payload : Word)
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word)) validateCR
      ((regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
        (regIs .x5 listBase) ** (regIs .x12 (listBase + 1)) **
        (regIs .x10 (listBase + 1)) ** P)
      (cpsDepPost post)) :
    cpsTripleWithin (2 + (1 + nVal)) (RlpWalkNextStrictTie.S + 148)
      (RlpWalkNextStrictTie.S + 160)
      (RlpWalkNextStrictTie.sharedCode.union validateCR)
      ((regIs .x5 listBase) ** (regIs .x12 oldPayload) ** (regIs .x10 old10) **
        (regIs .x1 oldRa) ** P)
      (cpsDepPost post) := by
  have hsetup0 := shared_short_arm_to_validate_call listBase oldPayload old10
  have hsetup := cpsTripleWithin_frameR ((regIs .x1 oldRa) ** P)
    (by apply pcFree_sepConj <;> first | exact pcFree_regIs | exact hP) hsetup0
  have hsetupFlat :
      cpsTripleWithin 2 (RlpWalkNextStrictTie.S + 148)
        (RlpWalkNextStrictTie.S + 156) RlpWalkNextStrictTie.sharedCode
        ((regIs .x5 listBase) ** (regIs .x12 oldPayload) ** (regIs .x10 old10) **
          (regIs .x1 oldRa) ** P)
        ((regIs .x1 oldRa) **
          (regIs .x5 listBase) ** (regIs .x12 (listBase + 1)) **
          (regIs .x10 (listBase + 1)) ** P) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp) hsetup
  have hsetupU := cpsTripleWithin_extend_code
    (cr := RlpWalkNextStrictTie.sharedCode)
    (cr' := RlpWalkNextStrictTie.sharedCode.union validateCR)
    (fun _ _ h => CodeReq.union_hit h) hsetupFlat
  have hcall0 := validate_call_dep_hcallee (n := nVal) (α := α)
    (P := (regIs .x5 listBase) ** (regIs .x12 (listBase + 1)) **
      (regIs .x10 (listBase + 1)) ** P)
    (post := post) oldRa
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact hP)
    hval
  have hsharedValDisj :
      RlpWalkNextStrictTie.sharedCode.Disjoint validateCR :=
    CodeReq.ofProg_disjoint_range_len
      RlpWalkNextStrictTie.S rlpWalkNextShared_prog 52
      validateEntry rlpValidatePayloadOffline_prog 23
      RlpWalkNextStrictTie.shared_length (by rfl) (by
        intro k1 k2 hk1 hk2 heq
        have hS : RlpWalkNextStrictTie.S.toNat =
            GuestAddrs.rlp_walk_next_shared := by decide
        have hV : validateEntry.toNat =
            GuestAddrs.rlp_validate_payload := by decide
        simp only [GuestAddrs.rlp_walk_next_shared,
          GuestAddrs.rlp_validate_payload] at hS hV
        have h := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hS, hV] at h
        omega)
  have hjalMono :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 39 (RlpWalkNextStrictTie.S + 156)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hmono :
      ∀ a i,
        ((CodeReq.singleton (RlpWalkNextStrictTie.S + 156)
          (.JAL .x1 (jalOff GuestAddrs.rlp_validate_payload
            (GuestAddrs.rlp_walk_next_shared + 156)))).union validateCR) a = some i →
        (RlpWalkNextStrictTie.sharedCode.union validateCR) a = some i :=
    CodeReq.union_split_mono
      (fun a i h => CodeReq.union_hit (hjalMono a i h))
      (fun a i h =>
        CodeReq.union_skip
          (by
            rcases hsharedValDisj a with hnone | hnone
            · exact hnone
            · simp [hnone] at h)
          h)
  have hcallU := cpsTripleWithin_extend_code hmono hcall0
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hsetupU hcallU

/-! Shared helpers for `sharedCode ∪ validateCR` mono, factored for the short
and long validate-call adapters. -/
theorem shared_validateCR_disjoint :
    RlpWalkNextStrictTie.sharedCode.Disjoint validateCR :=
  CodeReq.ofProg_disjoint_range_len
    RlpWalkNextStrictTie.S rlpWalkNextShared_prog 52
    validateEntry rlpValidatePayloadOffline_prog 23
    RlpWalkNextStrictTie.shared_length (by rfl) (by
      intro k1 k2 hk1 hk2 heq
      have hS : RlpWalkNextStrictTie.S.toNat =
          GuestAddrs.rlp_walk_next_shared := by decide
      have hV : validateEntry.toNat =
          GuestAddrs.rlp_validate_payload := by decide
      simp only [GuestAddrs.rlp_walk_next_shared,
        GuestAddrs.rlp_validate_payload] at hS hV
      have h := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hS, hV] at h
      omega)

theorem shared_jal_validate_mono :
    ∀ a i,
      ((CodeReq.singleton (RlpWalkNextStrictTie.S + 156)
        (.JAL .x1 (jalOff GuestAddrs.rlp_validate_payload
          (GuestAddrs.rlp_walk_next_shared + 156)))).union validateCR) a = some i →
      (RlpWalkNextStrictTie.sharedCode.union validateCR) a = some i := by
  have hjalMono :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 39 (RlpWalkNextStrictTie.S + 156)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  exact CodeReq.union_split_mono
    (fun a i h => CodeReq.union_hit (hjalMono a i h))
    (fun a i h =>
      CodeReq.union_skip
        (by
          rcases shared_validateCR_disjoint a with hnone | hnone
          · exact hnone
          · simp [hnone] at h)
        h)

/-- Long arm through the validate call return at `S+160`, under an abstract
validate callee.  Twin of `shared_short_arm_validate_call`; setup is the
payload path from `S+136`. -/
theorem shared_long_arm_validate_call
    {nVal : Nat} {α : Type} {P : Assertion} {post : α → Assertion}
    (cursor pfx oldOut old10 oldRa : Word)
    (hP : P.pcFree)
    (hval : cpsTripleWithin nVal (GuestAddrs.rlp_validate_payload : Word)
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word)) validateCR
      ((regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
        (regIs .x12 (cursor + pfx + 1)) ** (regIs .x5 cursor) **
        (regIs .x13 pfx) ** (regIs .x10 (cursor + pfx + 1)) ** P)
      (cpsDepPost post)) :
    cpsTripleWithin (4 + (1 + nVal)) (RlpWalkNextStrictTie.S + 136)
      (RlpWalkNextStrictTie.S + 160)
      (RlpWalkNextStrictTie.sharedCode.union validateCR)
      ((regIs .x12 oldOut) ** (regIs .x5 cursor) ** (regIs .x13 pfx) **
        (regIs .x10 old10) ** (regIs .x1 oldRa) ** P)
      (cpsDepPost post) := by
  have hsetup0 := shared_long_payload_to_validate_call cursor pfx oldOut old10
  have hsetup := cpsTripleWithin_frameR ((regIs .x1 oldRa) ** P)
    (by apply pcFree_sepConj <;> first | exact pcFree_regIs | exact hP) hsetup0
  have hsetupFlat :
      cpsTripleWithin 4 (RlpWalkNextStrictTie.S + 136)
        (RlpWalkNextStrictTie.S + 156) RlpWalkNextStrictTie.sharedCode
        ((regIs .x12 oldOut) ** (regIs .x5 cursor) ** (regIs .x13 pfx) **
          (regIs .x10 old10) ** (regIs .x1 oldRa) ** P)
        ((regIs .x1 oldRa) **
          (regIs .x12 (cursor + pfx + 1)) ** (regIs .x5 cursor) **
          (regIs .x13 pfx) ** (regIs .x10 (cursor + pfx + 1)) ** P) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp) hsetup
  have hsetupU := cpsTripleWithin_extend_code
    (cr := RlpWalkNextStrictTie.sharedCode)
    (cr' := RlpWalkNextStrictTie.sharedCode.union validateCR)
    (fun _ _ h => CodeReq.union_hit h) hsetupFlat
  have hcall0 := validate_call_dep_hcallee (n := nVal) (α := α)
    (P := (regIs .x12 (cursor + pfx + 1)) ** (regIs .x5 cursor) **
      (regIs .x13 pfx) ** (regIs .x10 (cursor + pfx + 1)) ** P)
    (post := post) oldRa
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact hP)
    hval
  have hcallU := cpsTripleWithin_extend_code shared_jal_validate_mono hcall0
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hsetupU hcallU

/-- After validate returns at `S+160`: depth decrement then the status branch
head at `S+164`.  The full success/failure tails stay in
`shared_validate_status_dep`; this lemma only lands the depth edge so the
status contract can attach. -/
theorem shared_validate_return_depth
    (depth : Word) (P : Assertion) (hP : P.pcFree) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 160)
      (RlpWalkNextStrictTie.S + 164) RlpWalkNextStrictTie.sharedCode
      ((regIs .x9 depth) ** P) ((regIs .x9 (depth - 1)) ** P) := by
  have h := shared_depth_decrement depth
  exact cpsTripleWithin_frameR P hP h

/-- Dependent-post sequencing on a single `CodeReq` (continuation lives in the
same image as the call).  Twin of `cpsTripleWithin_seq_dep_post` without a
disjointness obligation. -/
theorem cpsTripleWithin_seq_dep_post_same_cr
    {α : Type} {nSteps1 nSteps2 : Nat} {entry mid exit_ : Word}
    {cr : CodeReq} {P R : Assertion} {post : α → Assertion}
    (h1 : cpsTripleWithin nSteps1 entry mid cr P (cpsDepPost post))
    (h2 : ∀ a, cpsTripleWithin nSteps2 mid exit_ cr (post a) R) :
    cpsTripleWithin (nSteps1 + nSteps2) entry exit_ cr P R := by
  intro Frame hFrame s hcr hP hpc
  obtain ⟨k1, hk1, s1, hstep1, hpc1, hQR⟩ :=
    h1 Frame hFrame s hcr hP hpc
  have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
  obtain ⟨hWhole, hCompat, hQ, hFrame', hdisj, hunion, hpost, hR⟩ := hQR
  obtain ⟨a, hpost_a⟩ := hpost
  have hpostFrame : (post a ** Frame).holdsFor s1 :=
    ⟨hWhole, hCompat, hQ, hFrame', hdisj, hunion, hpost_a, hR⟩
  obtain ⟨k2, hk2, s2, hstep2, hpc2, hR2⟩ :=
    h2 a Frame hFrame s1 hcr' hpostFrame hpc1
  exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2,
    stepN_add_eq hstep1 hstep2, hpc2, hR2⟩

/-! Long LIST arm through the validator call.  The selector supplies `n`,
the payload-start equation, and the header-fit inequality; the region lemma
consumes those facts and publishes the three loop scratch registers as
ownership.  The validator premise is deliberately stated with the complete
call-site frame, so this theorem is an adapter to a real callee triple rather
than a free-standing arm claim. -/
theorem shared_list_arm_goal_long_compose
    {bytes : List (BitVec 8)} {base : Word} {floor parentFuel : Nat}
    {cursorOff endOff : Nat}
    {spV sp raVal exit_ endPtr pfx listBase depth : Word}
    {oldPayload old10 oldOut old7 oldRem old13 old29 oldAcc : Word}
    {P : Assertion} {nVal : Nat} {α : Type} {post : α → Assertion}
    (h : SharedListArmInputs bytes base floor parentFuel cursorOff endOff spV sp
      raVal exit_ endPtr pfx listBase depth oldPayload old10 oldOut old7
      oldRem old13 old29 oldAcc P)
    (hlong : ¬ BitVec.ult pfx (248 : Word))
    (hval : ∀ n, n ≤ 8 →
      cpsTripleWithin nVal (GuestAddrs.rlp_validate_payload : Word)
        ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word)) validateCR
        ((regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
          (regIs .x12 (listBase + BitVec.ofNat 64 n + 1)) **
          (regIs .x5 listBase) ** (regIs .x13 (BitVec.ofNat 64 n)) **
          (regIs .x10 (listBase + BitVec.ofNat 64 n + 1)) **
          (regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
          (regIs .x28 (0 : Word)) ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (regIs .x0 (0 : Word)) **
          bytesRegion base bytes **
          sharedValidateCallRemainder spV sp endPtr **
          ⌜ValidateFuel bytes (cycleFuel h.selector.payloadStart
            h.selector.payloadEnd) h.selector.payloadStart
            h.selector.payloadEnd⌝ ** P)
        (cpsDepPost post)) :
    ∃ nLong, cpsTripleWithin nLong (RlpWalkNextStrictTie.S + 88)
      (RlpWalkNextStrictTie.S + 160)
      (RlpWalkNextStrictTie.sharedCode.union validateCR)
      (((regIs .x6 pfx) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
        (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
        regOwn .x30 ** regOwn .x31 ** (regIs .x12 oldOut) **
        (regIs .x10 old10) ** (regIs .x1 raVal) **
        (regIs .x0 (0 : Word)) ** bytesRegion base bytes **
        ⌜sharedPrefixByteAt bytes cursorOff pfx⌝ **
        ⌜¬ BitVec.ult pfx (192 : Word)⌝ **
        ⌜BitVec.ult depth (1024 : Word)⌝ **
        ⌜cursorOff < h.selector.payloadStart⌝ **
        ⌜h.selector.payloadStart ≤ h.selector.payloadEnd⌝ **
        ⌜¬ BitVec.ult pfx (248 : Word)⌝ **
        sharedValidateCallRemainder spV sp endPtr **
        ⌜ValidateFuel bytes (cycleFuel h.selector.payloadStart
          h.selector.payloadEnd) h.selector.payloadStart
          h.selector.payloadEnd⌝) ** P)
      (cpsDepPost post) := by
  obtain ⟨n, hn, hrem, hpayloadStart, hheaderFit⟩ :=
    h.selector.hlongHeader pfx h.hprefix hlong
  let leftovers : Assertion :=
    ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
      (regIs .x28 (0 : Word)) ** regOwn .x29 ** regOwn .x30 **
      regOwn .x31 ** (regIs .x0 (0 : Word)) ** bytesRegion base bytes **
      sharedValidateCallRemainder spV sp endPtr **
      ⌜ValidateFuel bytes (cycleFuel h.selector.payloadStart
        h.selector.payloadEnd) h.selector.payloadStart
        h.selector.payloadEnd⌝ ** P)
  have hleftPc : leftovers.pcFree := by
    simp only [leftovers]
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memOwn
      | exact bytesRegion_pcFree _ _
      | exact pcFree_pure
      | exact h.hP
  have hregion0 := shared_long_prefix_region_from_selector_own h n hn hrem
    hpayloadStart hheaderFit
  have hregion := cpsTripleWithin_frameR
    ((regIs .x1 raVal) ** sharedValidateCallRemainder spV sp endPtr **
      ⌜ValidateFuel bytes (cycleFuel h.selector.payloadStart
        h.selector.payloadEnd) h.selector.payloadStart
        h.selector.payloadEnd⌝)
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memOwn
        | exact pcFree_pure) hregion0
  have hregionU := cpsTripleWithin_extend_code
    (cr := RlpWalkNextStrictTie.sharedCode)
    (cr' := RlpWalkNextStrictTie.sharedCode.union validateCR)
    (fun _ _ hcode => CodeReq.union_hit hcode) hregion
  have hcall0 := validate_call_dep_hcallee (n := nVal) (α := α)
    (P := (regIs .x12 (listBase + BitVec.ofNat 64 n + 1)) **
      (regIs .x5 listBase) ** (regIs .x13 (BitVec.ofNat 64 n)) **
      (regIs .x10 (listBase + BitVec.ofNat 64 n + 1)) ** leftovers)
    (post := post) raVal
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_regOwn
        | exact pcFree_memOwn
        | exact bytesRegion_pcFree _ _
        | exact pcFree_pure
        | exact h.hP)
    (hval n hn)
  have hcallU := cpsTripleWithin_extend_code shared_jal_validate_mono hcall0
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hregionU hcallU
  refine ⟨(5 + (7 * n + 1) + 4) + (1 + nVal), ?_⟩
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hp => hp) hseq
  drop_pure hp
  have hp' := (sepConj_pure_right _).2 ⟨hp, h.selector.hvalidate⟩
  xperm_chunked hp'

/-! ## Composition check for the amended list-arm goal (GH #12457)

`SharedListArmsFromValidateGoal`'s short-arm conclusion is stated under
`sharedCode.union validateCR`; this theorem composes that conclusion with
`shared_short_arm_validate_call` and shows the chain typechecks: the goal's
precondition (register pins plus the six pure selector atoms) weakens to the
call lemma's precondition by dropping the pure atoms, and the code
requirement is syntactically the amended one.  This is the conclusion-side
oracle the anti-vacuity rubric asks for: a statement none of its intended
adjacent lemmas can chain to is wrong, not merely weak. -/

theorem shared_list_arm_goal_short_compose
    {bytes : List (BitVec 8)} {base : Word} {floor parentFuel : Nat}
    {cursorOff endOff : Nat}
    {spV sp raVal exit_ endPtr pfx listBase depth : Word}
    {oldPayload old10 oldOut old7 oldRem old13 old29 oldAcc : Word}
    {P : Assertion} {nVal : Nat} {post : ValidateResult → Assertion}
    (h : SharedListArmInputs bytes base floor parentFuel cursorOff endOff spV sp
      raVal exit_ endPtr pfx listBase depth oldPayload old10 oldOut old7
      oldRem old13 old29 oldAcc P)
    (hval : cpsTripleWithin nVal (GuestAddrs.rlp_validate_payload : Word)
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word)) validateCR
      ((regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
        (regIs .x5 listBase) ** (regIs .x12 (listBase + 1)) **
        (regIs .x10 (listBase + 1)) **
        sharedValidateCallRemainder spV sp endPtr **
        ⌜ValidateFuel bytes (cycleFuel h.selector.payloadStart
          h.selector.payloadEnd) h.selector.payloadStart
          h.selector.payloadEnd⌝ ** P)
      (cpsDepPost post)) :
    cpsTripleWithin (2 + (1 + nVal)) (RlpWalkNextStrictTie.S + 148)
      (RlpWalkNextStrictTie.S + 160)
      (RlpWalkNextStrictTie.sharedCode.union validateCR)
      (((regIs .x5 listBase) ** (regIs .x12 oldPayload) **
        (regIs .x10 old10) ** (regIs .x1 raVal) **
        ⌜sharedPrefixByteAt bytes cursorOff pfx⌝ **
        ⌜¬ BitVec.ult pfx (192 : Word)⌝ **
        ⌜BitVec.ult depth (1024 : Word)⌝ **
        ⌜cursorOff < h.selector.payloadStart⌝ **
        ⌜h.selector.payloadStart ≤ h.selector.payloadEnd⌝ **
        ⌜BitVec.ult pfx (248 : Word)⌝ **
        sharedValidateCallRemainder spV sp endPtr **
        ⌜ValidateFuel bytes (cycleFuel h.selector.payloadStart
          h.selector.payloadEnd) h.selector.payloadStart
          h.selector.payloadEnd⌝) ** P)
      (cpsDepPost post) := by
  have hCallP :
      (sharedValidateCallRemainder spV sp endPtr **
        ⌜ValidateFuel bytes (cycleFuel h.selector.payloadStart
          h.selector.payloadEnd) h.selector.payloadStart
          h.selector.payloadEnd⌝ ** P).pcFree := by
    simp only [sharedValidateCallRemainder]
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memOwn
      | exact pcFree_pure
      | exact h.hP
  refine cpsTripleWithin_weaken (fun _ hgoal => ?_) (fun _ hp => hp)
    (shared_short_arm_validate_call listBase oldPayload old10 raVal hCallP hval)
  drop_pure hgoal
  have hgoal' := (sepConj_pure_right _).2 ⟨hgoal, h.selector.hvalidate⟩
  xperm_hyp hgoal'

end EvmAsm.Codegen.RlpWalkNextStrictFuel
