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
      validateEntry rlpValidatePayload_prog 23
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
    validateEntry rlpValidatePayload_prog 23
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

/-- Short arm through validate return, then an abstract continuation at
`S+160` for every dependent result.  This is the shape
`SharedListArmsFromValidateGoal` needs for the short side once the
continuation (depth + status) is supplied from the Validate-family witness. -/
theorem shared_short_arm_validate_then_cont
    {nVal nCont : Nat} {α : Type} {P R : Assertion} {post : α → Assertion}
    (listBase oldPayload old10 oldRa exit_ : Word)
    (hP : P.pcFree)
    (hval : cpsTripleWithin nVal (GuestAddrs.rlp_validate_payload : Word)
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word)) validateCR
      ((regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
        (regIs .x5 listBase) ** (regIs .x12 (listBase + 1)) **
        (regIs .x10 (listBase + 1)) ** P)
      (cpsDepPost post))
    (hcont : ∀ a, cpsTripleWithin nCont (RlpWalkNextStrictTie.S + 160) exit_
      (RlpWalkNextStrictTie.sharedCode.union validateCR) (post a) R) :
    cpsTripleWithin (2 + (1 + nVal) + nCont) (RlpWalkNextStrictTie.S + 148) exit_
      (RlpWalkNextStrictTie.sharedCode.union validateCR)
      ((regIs .x5 listBase) ** (regIs .x12 oldPayload) ** (regIs .x10 old10) **
        (regIs .x1 oldRa) ** P)
      R :=
  cpsTripleWithin_seq_dep_post_same_cr
    (shared_short_arm_validate_call listBase oldPayload old10 oldRa hP hval)
    hcont

/-- Long-arm twin of `shared_short_arm_validate_then_cont`. -/
theorem shared_long_arm_validate_then_cont
    {nVal nCont : Nat} {α : Type} {P R : Assertion} {post : α → Assertion}
    (cursor pfx oldOut old10 oldRa exit_ : Word)
    (hP : P.pcFree)
    (hval : cpsTripleWithin nVal (GuestAddrs.rlp_validate_payload : Word)
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word)) validateCR
      ((regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
        (regIs .x12 (cursor + pfx + 1)) ** (regIs .x5 cursor) **
        (regIs .x13 pfx) ** (regIs .x10 (cursor + pfx + 1)) ** P)
      (cpsDepPost post))
    (hcont : ∀ a, cpsTripleWithin nCont (RlpWalkNextStrictTie.S + 160) exit_
      (RlpWalkNextStrictTie.sharedCode.union validateCR) (post a) R) :
    cpsTripleWithin (4 + (1 + nVal) + nCont) (RlpWalkNextStrictTie.S + 136) exit_
      (RlpWalkNextStrictTie.sharedCode.union validateCR)
      ((regIs .x12 oldOut) ** (regIs .x5 cursor) ** (regIs .x13 pfx) **
        (regIs .x10 old10) ** (regIs .x1 oldRa) ** P)
      R :=
  cpsTripleWithin_seq_dep_post_same_cr
    (shared_long_arm_validate_call cursor pfx oldOut old10 oldRa hP hval)
    hcont

end EvmAsm.Codegen.RlpWalkNextStrictFuel
