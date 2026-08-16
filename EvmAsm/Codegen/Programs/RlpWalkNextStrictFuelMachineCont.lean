/-
  EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelMachineCont

  Shared LIST-arm validate-call adapters and depth+status continuation
  for #12419 (split from RlpWalkNextStrictFuelMachine for the Programs
  1500-line cap).
-/

import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelMachine

namespace EvmAsm.Codegen.RlpWalkNextStrictFuel

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP


/-- Long-arm `pfx = 247` (zero length-of-length): preamble then immediate
zero-remaining exit to payload base `S+136`. -/
theorem shared_long_prefix_preamble_zero_to_payload
    (listBase old7 oldRem old13 old29 oldAcc : Word) :
    cpsTripleWithin 6 (RlpWalkNextStrictTie.S + 88)
      (RlpWalkNextStrictTie.S + 136) RlpWalkNextStrictTie.sharedCode
      ((regIs .x6 (247 : Word)) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
        (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
        (regIs .x30 oldAcc) ** (regIs .x0 (0 : Word)))
      ((regIs .x6 (247 : Word)) ** (regIs .x7 (247 : Word)) **
        (regIs .x28 (0 : Word)) ** (regIs .x13 (0 : Word)) **
        (regIs .x5 listBase) ** (regIs .x29 (listBase + 1)) **
        (regIs .x30 (0 : Word)) ** (regIs .x0 (0 : Word))) := by
  have hpre0 := shared_long_prefix_preamble (247 : Word) listBase old7 oldRem
    old13 old29 oldAcc
  have hpre := cpsTripleWithin_frameR (regIs .x0 (0 : Word))
    (by exact pcFree_regIs) hpre0
  -- After preamble: remaining = 247 - 247 = 0 at S+108; take zero exit.
  have hbr0 := shared_long_prefix_branch (0 : Word)
  have htaken0 := cpsBranchWithin_takenStripPure2 hbr0 (by
    intro _ hQf
    obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
    exact absurd rfl ((sepConj_pure_right _).mp h_rest).2)
  have htaken := cpsTripleWithin_frameR
    ((regIs .x6 (247 : Word)) ** (regIs .x7 (247 : Word)) **
      (regIs .x13 (0 : Word)) ** (regIs .x5 listBase) **
      (regIs .x29 (listBase + 1)) ** (regIs .x30 (0 : Word)))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs)
    htaken0
  have hrem0 : (247 : Word) - 247 = 0 := by decide
  have hpre' : cpsTripleWithin 5 (RlpWalkNextStrictTie.S + 88)
      (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
      ((regIs .x6 (247 : Word)) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
        (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
        (regIs .x30 oldAcc) ** (regIs .x0 (0 : Word)))
      ((regIs .x6 (247 : Word)) ** (regIs .x7 (247 : Word)) **
        (regIs .x28 (0 : Word)) ** (regIs .x13 (0 : Word)) **
        (regIs .x5 listBase) ** (regIs .x29 (listBase + 1)) **
        (regIs .x30 (0 : Word)) ** (regIs .x0 (0 : Word))) := by
    have hpre1 : cpsTripleWithin 5 (RlpWalkNextStrictTie.S + 88)
        (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
        ((regIs .x6 (247 : Word)) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
          (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
          (regIs .x30 oldAcc) ** (regIs .x0 (0 : Word)))
        ((regIs .x6 (247 : Word)) ** (regIs .x7 (247 : Word)) **
          (regIs .x28 ((247 : Word) - 247)) ** (regIs .x13 ((247 : Word) - 247)) **
          (regIs .x5 listBase) ** (regIs .x29 (listBase + 1)) **
          (regIs .x30 (0 : Word)) ** (regIs .x0 (0 : Word))) :=
      cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hp => by xperm_hyp hp) hpre
    simpa [hrem0] using hpre1
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hpre' htaken
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hseq

/-- Long-arm preamble + `n`-byte length decode to payload base. Requires
`pfx - 247 = ofNat n` so the remaining counter matches the loop fuel. -/
theorem shared_long_prefix_preamble_n_iter_to_payload
    (n : Nat) (hn : n ≤ 8)
    (pfx listBase old7 oldRem old13 old29 oldAcc oldByte
      dwordAddr wordVal : Word)
    (hrem : pfx - 247 = BitVec.ofNat 64 n)
    (hwin : ∀ i, i < n →
      alignToDword ((listBase + 1) + BitVec.ofNat 64 i) = dwordAddr ∧
      isValidByteAccess ((listBase + 1) + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin (5 + (7 * n + 1)) (RlpWalkNextStrictTie.S + 88)
      (RlpWalkNextStrictTie.S + 136) RlpWalkNextStrictTie.sharedCode
      ((regIs .x6 pfx) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
        (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
        (regIs .x30 oldAcc) ** (regIs .x31 oldByte) **
        (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
      ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
        (regIs .x28 (0 : Word)) ** (regIs .x13 (BitVec.ofNat 64 n)) **
        (regIs .x5 listBase) **
        (regIs .x29 ((listBase + 1) + BitVec.ofNat 64 n)) **
        (regIs .x30 (sharedLongAcc wordVal (0 : Word) (listBase + 1) n)) **
        (regIs .x31 (sharedLongLastByte wordVal (listBase + 1) oldByte n)) **
        (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
  have hpre0 := shared_long_prefix_preamble pfx listBase old7 oldRem
    old13 old29 oldAcc
  have hpre := cpsTripleWithin_frameR
    ((regIs .x31 oldByte) ** (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs)
    hpre0
  have hloop0 := shared_long_prefix_n_iter n hn (0 : Word) (listBase + 1)
    oldByte dwordAddr wordVal hwin
  have hloop := cpsTripleWithin_frameR
    ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
      (regIs .x13 (BitVec.ofNat 64 n)) ** (regIs .x5 listBase))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs)
    hloop0
  have hpre' : cpsTripleWithin 5 (RlpWalkNextStrictTie.S + 88)
      (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
      ((regIs .x6 pfx) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
        (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
        (regIs .x30 oldAcc) ** (regIs .x31 oldByte) **
        (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
      ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
        (regIs .x28 (BitVec.ofNat 64 n)) ** (regIs .x13 (BitVec.ofNat 64 n)) **
        (regIs .x5 listBase) ** (regIs .x29 (listBase + 1)) **
        (regIs .x30 (0 : Word)) ** (regIs .x31 oldByte) **
        (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
    have hpre1 : cpsTripleWithin 5 (RlpWalkNextStrictTie.S + 88)
        (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
        ((regIs .x6 pfx) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
          (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
          (regIs .x30 oldAcc) ** (regIs .x31 oldByte) **
          (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
        ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
          (regIs .x28 (pfx - 247)) ** (regIs .x13 (pfx - 247)) **
          (regIs .x5 listBase) ** (regIs .x29 (listBase + 1)) **
          (regIs .x30 (0 : Word)) ** (regIs .x31 oldByte) **
          (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) :=
      cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hp => by xperm_chunked hp) hpre
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hp => by
        rw [← hrem]
        exact hp) hpre1
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hpre' hloop
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => by xperm_chunked hp) hseq

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

/-! ## Depth + status continuation after validate return

`shared_validate_status_dep` already merges success/failure from `S+164`.
These lemmas attach the depth decrement at `S+160` and collapse the two
status exits (same PC) to a single post when both arms imply it. -/

/-- Precondition at `S+160` for depth+status: depth register plus the status
branch frame already used by `shared_validate_status_dep`. -/
def sharedAfterValidatePre
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    (endPtr sp raVal cursor outerNext outerStatus outerLen depth : Word)
    (r : ValidateResult) : Assertion :=
  ((regIs .x9 depth) **
    (((regIs .x10 r.status) ** (regIs .x0 (0 : Word))) **
      ((sharedValidateStatusFrame sp raVal cursor outerNext outerStatus
        outerLen r) **
        ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)))

/-- Status precondition matching `shared_validate_status_dep` (no depth). -/
private def sharedValidateStatusPre
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    (endPtr sp raVal cursor outerNext outerStatus outerLen : Word)
    (r : ValidateResult) : Assertion :=
  (((regIs .x10 r.status) ** (regIs .x0 (0 : Word))) **
    ((sharedValidateStatusFrame sp raVal cursor outerNext outerStatus
      outerLen r) **
      ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝))

theorem shared_after_validate_depth_status
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    (endPtr sp raVal cursor outerNext outerStatus outerLen depth : Word)
    (r : ValidateResult) :
    cpsNBranchWithin 15 (RlpWalkNextStrictTie.S + 160)
      RlpWalkNextStrictTie.sharedCode
      (sharedAfterValidatePre (bytes := bytes) (base := base) (floor := floor)
        (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
        endPtr sp raVal cursor outerNext outerStatus outerLen depth r)
      [(raVal &&& ~~~1,
        ((regIs .x9 (depth - 1)) **
          sharedValidateStatusSuccessPost (bytes := bytes) (base := base)
            (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
            (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
            outerLen r)),
       (raVal &&& ~~~1,
        ((regIs .x9 (depth - 1)) **
          sharedValidateStatusFailurePost (bytes := bytes) (base := base)
            (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
            (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
            outerLen r))] := by
  let statusPre :=
    sharedValidateStatusPre (bytes := bytes) (base := base) (floor := floor)
      (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
      endPtr sp raVal cursor outerNext outerStatus outerLen r
  have hdepth :
      cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 160)
        (RlpWalkNextStrictTie.S + 164) RlpWalkNextStrictTie.sharedCode
        (sharedAfterValidatePre (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen depth r)
        ((regIs .x9 (depth - 1)) ** statusPre) := by
    simpa [sharedAfterValidatePre, sharedValidateStatusPre, statusPre] using
      (shared_validate_return_depth depth statusPre (by pcf_validate_cps))
  have hstatus0 := shared_validate_status_dep (bytes := bytes) (base := base)
    (floor := floor) (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
    endPtr sp raVal cursor outerNext outerStatus outerLen r
  -- Frame depth on the RIGHT; mid is then `statusPre ** x9`, which permutes
  -- from the depth-post `x9 ** statusPre`.
  have hstatusFr :
      cpsNBranchWithin 14 (RlpWalkNextStrictTie.S + 164)
        RlpWalkNextStrictTie.sharedCode
        (statusPre ** (regIs .x9 (depth - 1)))
        [(raVal &&& ~~~1,
          (sharedValidateStatusSuccessPost (bytes := bytes) (base := base)
            (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
            (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
            outerLen r **
            (regIs .x9 (depth - 1)))),
         (raVal &&& ~~~1,
          (sharedValidateStatusFailurePost (bytes := bytes) (base := base)
            (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
            (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
            outerLen r **
            (regIs .x9 (depth - 1))))] := by
    simpa [sharedValidateStatusPre, statusPre] using
      (cpsNBranchWithin_frameR
        (by exact pcFree_regIs : (regIs .x9 (depth - 1)).pcFree) hstatus0)
  have hseq :=
    cpsTripleWithin_seq_cpsNBranchWithin_perm_same_cr
      (fun _ hp => by xperm_chunked hp) hdepth hstatusFr
  refine cpsNBranchWithin_weaken_posts hseq ?_
  intro ex hmem
  cases hmem with
  | head =>
    refine ⟨_, List.Mem.head _, rfl, fun _ hp => by xperm_chunked hp⟩
  | tail _ htail =>
    cases htail with
    | head =>
      refine ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, fun _ hp => by
        xperm_chunked hp⟩
    | tail _ hnil =>
      exact nomatch hnil

/-- Collapse depth+status to a single exit post `R` when both arms imply it. -/
theorem shared_after_validate_cont
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    {R : Assertion}
    (endPtr sp raVal cursor outerNext outerStatus outerLen depth : Word)
    (r : ValidateResult)
    (hsucc : ∀ hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusSuccessPost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp)
    (hfail : ∀ hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusFailurePost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp) :
    cpsTripleWithin 15 (RlpWalkNextStrictTie.S + 160) (raVal &&& ~~~1)
      RlpWalkNextStrictTie.sharedCode
      (sharedAfterValidatePre (bytes := bytes) (base := base) (floor := floor)
        (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
        endPtr sp raVal cursor outerNext outerStatus outerLen depth r)
      R := by
  have hbr :=
    shared_after_validate_depth_status (bytes := bytes) (base := base)
      (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
      (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus outerLen
      depth r
  intro Frame hFrame s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, ex, hmem, hpc', hQR⟩ :=
    hbr Frame hFrame s hcr hPR hpc
  cases hmem with
  | head =>
    -- `ex = (raVal &&& ~~~1, successPost)`; `hpc'` already targets the exit.
    exact ⟨k, hk, s', hstep, hpc', by
      obtain ⟨hw, hc, hq, hf, hd, hu, hQ, hF⟩ := hQR
      exact ⟨hw, hc, hq, hf, hd, hu, hsucc _ hQ, hF⟩⟩
  | tail _ htail =>
    cases htail with
    | head =>
      exact ⟨k, hk, s', hstep, hpc', by
        obtain ⟨hw, hc, hq, hf, hd, hu, hQ, hF⟩ := hQR
        exact ⟨hw, hc, hq, hf, hd, hu, hfail _ hQ, hF⟩⟩
    | tail _ hnil =>
      exact nomatch hnil

/-- `hcont` witness for `*_validate_then_cont`: every validate result continues
through depth+status to `raVal &&& ~~~1` with post `R`, once both status arms
imply `R`.  Extended onto `sharedCode ∪ validateCR`. -/
theorem shared_after_validate_cont_family
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    {R : Assertion}
    (endPtr sp raVal cursor outerNext outerStatus outerLen depth : Word)
    (hsucc : ∀ r hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusSuccessPost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp)
    (hfail : ∀ r hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusFailurePost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp) :
    ∀ r, cpsTripleWithin 15 (RlpWalkNextStrictTie.S + 160) (raVal &&& ~~~1)
      (RlpWalkNextStrictTie.sharedCode.union validateCR)
      (sharedAfterValidatePre (bytes := bytes) (base := base) (floor := floor)
        (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
        endPtr sp raVal cursor outerNext outerStatus outerLen depth r)
      R := fun r =>
  cpsTripleWithin_extend_code
    (fun _ _ h => CodeReq.union_hit h)
    (shared_after_validate_cont (bytes := bytes) (base := base)
      (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
      (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus outerLen
      depth r (hsucc r) (hfail r))

/-- Caller ambient preserved across the validate call and combined with
`validateResultPost` to recover `sharedAfterValidatePre`. -/
def sharedValidateCallerAmbient
    (sp raVal cursor outerNext outerStatus outerLen depth : Word) : Assertion :=
  ((regIs .x9 depth) ** (regIs .x0 (0 : Word)) **
    (regIs .x1 (RlpWalkNextStrictTie.S + 160)) ** (regIs .x2 sp) **
    (memIs sp raVal) ** (memIs (sp + 8) cursor) **
    (memIs (sp + 24) outerNext) ** (memIs (sp + 32) outerStatus) **
    (memIs (sp + 40) outerLen))

/-- Shared cells that may sit in validate's ambient `P` at call entry: depth and
outer spills, excluding `x0`/`x1`/`x2` which the validate ABI owns.  Using this
(instead of full `sharedValidateCallerAmbient`) in `*_validate_then_status`'s
`hval` avoids a separating double-claim on `x1`. -/
def sharedValidateCallerRest
    (sp raVal cursor outerNext outerStatus outerLen depth : Word) : Assertion :=
  ((regIs .x9 depth) **
    (memIs sp raVal) ** (memIs (sp + 8) cursor) **
    (memIs (sp + 24) outerNext) ** (memIs (sp + 32) outerStatus) **
    (memIs (sp + 40) outerLen))

theorem sharedValidateCallerAmbient_of_rest
    (sp raVal cursor outerNext outerStatus outerLen depth : Word) :
    ∀ hp,
      ((regIs .x1 (RlpWalkNextStrictTie.S + 160)) ** (regIs .x2 sp) **
        (regIs .x0 (0 : Word)) **
        sharedValidateCallerRest sp raVal cursor outerNext outerStatus
          outerLen depth) hp →
      sharedValidateCallerAmbient sp raVal cursor outerNext outerStatus
        outerLen depth hp := by
  intro hp h
  simp only [sharedValidateCallerAmbient, sharedValidateCallerRest] at h ⊢
  xperm_chunked h

/-- Validate scratch after return: values forgotten, ownership retained. -/
def validateCallerSlack (sp_v : Word) : Assertion :=
  ((memOwn sp_v) ** (memOwn (sp_v + 8)) ** (memOwn (sp_v + 16)))

theorem sharedAfterValidatePre_of_validate_return
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    (endPtr sp raVal cursor outerNext outerStatus outerLen depth : Word)
    (r : ValidateResult) :
    ∀ hp,
      (sharedValidateCallerAmbient sp raVal cursor outerNext outerStatus
        outerLen depth **
        validateResultPost bytes base floor cursorOff endOff fuel endPtr r) hp →
      sharedAfterValidatePre (bytes := bytes) (base := base) (floor := floor)
        (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
        endPtr sp raVal cursor outerNext outerStatus outerLen depth r hp := by
  intro hp h
  -- Unfold both sides; `sharedValidateStatusFrame` is the caller ambient
  -- with `x11`/`x12` taken from the validate result.
  simp only [sharedAfterValidatePre,
    sharedValidateCallerAmbient, sharedValidateStatusFrame,
    validateResultPost] at h ⊢
  xperm_chunked h

/-- `hcont` when the validate callee returns `validateResultPost` framed by
the caller ambient: weaken to `sharedAfterValidatePre`, then run
depth+status. -/
theorem shared_after_validate_cont_from_result
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    {R : Assertion}
    (endPtr sp raVal cursor outerNext outerStatus outerLen depth : Word)
    (r : ValidateResult)
    (hsucc : ∀ hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusSuccessPost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp)
    (hfail : ∀ hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusFailurePost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp) :
    cpsTripleWithin 15 (RlpWalkNextStrictTie.S + 160) (raVal &&& ~~~1)
      (RlpWalkNextStrictTie.sharedCode.union validateCR)
      (sharedValidateCallerAmbient sp raVal cursor outerNext outerStatus
        outerLen depth **
        validateResultPost bytes base floor cursorOff endOff fuel endPtr r)
      R :=
  cpsTripleWithin_weaken
    (sharedAfterValidatePre_of_validate_return (bytes := bytes) (base := base)
      (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
      (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus outerLen
      depth r)
    (fun _ hp => hp)
    (cpsTripleWithin_extend_code
      (fun _ _ h => CodeReq.union_hit h)
      (shared_after_validate_cont (bytes := bytes) (base := base)
        (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
        (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus outerLen
        depth r hsucc hfail))

/-- Same continuation with validate scratch `memOwn` framed through (precise SL
keeps those cells after `validateCyclePost_to_callerAmbient`). -/
theorem shared_after_validate_cont_from_result_frame_slack
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    {R : Assertion}
    (endPtr sp raVal cursor outerNext outerStatus outerLen depth sp_v : Word)
    (r : ValidateResult)
    (hsucc : ∀ hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusSuccessPost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp)
    (hfail : ∀ hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusFailurePost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp) :
    cpsTripleWithin 15 (RlpWalkNextStrictTie.S + 160) (raVal &&& ~~~1)
      (RlpWalkNextStrictTie.sharedCode.union validateCR)
      (sharedValidateCallerAmbient sp raVal cursor outerNext outerStatus
        outerLen depth **
        validateResultPost bytes base floor cursorOff endOff fuel endPtr r **
        validateCallerSlack sp_v)
      (R ** validateCallerSlack sp_v) := by
  have hslack : (validateCallerSlack sp_v).pcFree := by
    simp only [validateCallerSlack]
    pcf_validate_cps
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => hp)
    (cpsTripleWithin_frameR (validateCallerSlack sp_v) hslack
      (shared_after_validate_cont_from_result (bytes := bytes) (base := base)
        (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
        (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus outerLen
        depth r hsucc hfail))

/-- Short arm through validate + depth/status when the callee's dependent post
is `callerAmbient ** validateResultPost`.  The `hval` pre uses
`sharedValidateCallerRest` plus ABI `x0`/`x2` (not full ambient) so `x1` is
claimed only once. -/
theorem shared_short_arm_validate_then_status
    {nVal : Nat} {bytes : List (BitVec 8)} {base : Word}
    {floor cursorOff endOff fuel : Nat} {R : Assertion}
    (listBase oldPayload old10 oldRa endPtr sp raVal cursor outerNext
      outerStatus outerLen depth : Word)
    (hsucc : ∀ r hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusSuccessPost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp)
    (hfail : ∀ r hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusFailurePost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp)
    (hval : cpsTripleWithin nVal (GuestAddrs.rlp_validate_payload : Word)
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word)) validateCR
      ((regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
        (regIs .x5 listBase) ** (regIs .x12 (listBase + 1)) **
        (regIs .x10 (listBase + 1)) **
        (regIs .x2 sp) ** (regIs .x0 (0 : Word)) **
        sharedValidateCallerRest sp raVal cursor outerNext outerStatus
          outerLen depth)
      (cpsDepPost (fun r =>
        sharedValidateCallerAmbient sp raVal cursor outerNext outerStatus
          outerLen depth **
          validateResultPost bytes base floor cursorOff endOff fuel endPtr r))) :
    cpsTripleWithin (2 + (1 + nVal) + 15) (RlpWalkNextStrictTie.S + 148)
      (raVal &&& ~~~1) (RlpWalkNextStrictTie.sharedCode.union validateCR)
      ((regIs .x5 listBase) ** (regIs .x12 oldPayload) ** (regIs .x10 old10) **
        (regIs .x1 oldRa) **
        (regIs .x2 sp) ** (regIs .x0 (0 : Word)) **
        sharedValidateCallerRest sp raVal cursor outerNext outerStatus
          outerLen depth)
      R :=
  shared_short_arm_validate_then_cont listBase oldPayload old10 oldRa
    (raVal &&& ~~~1)
    (by pcf_validate_cps) hval
    (fun r =>
      shared_after_validate_cont_from_result (bytes := bytes) (base := base)
        (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
        (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus outerLen
        depth r (hsucc r) (hfail r))

/-- Long-arm twin of `shared_short_arm_validate_then_status`. -/
theorem shared_long_arm_validate_then_status
    {nVal : Nat} {bytes : List (BitVec 8)} {base : Word}
    {floor cursorOff endOff fuel : Nat} {R : Assertion}
    (cursorVal pfx oldOut old10 oldRa endPtr sp raVal cursor outerNext
      outerStatus outerLen depth : Word)
    (hsucc : ∀ r hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusSuccessPost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp)
    (hfail : ∀ r hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusFailurePost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp)
    (hval : cpsTripleWithin nVal (GuestAddrs.rlp_validate_payload : Word)
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word)) validateCR
      ((regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
        (regIs .x12 (cursorVal + pfx + 1)) ** (regIs .x5 cursorVal) **
        (regIs .x13 pfx) ** (regIs .x10 (cursorVal + pfx + 1)) **
        (regIs .x2 sp) ** (regIs .x0 (0 : Word)) **
        sharedValidateCallerRest sp raVal cursor outerNext outerStatus
          outerLen depth)
      (cpsDepPost (fun r =>
        sharedValidateCallerAmbient sp raVal cursor outerNext outerStatus
          outerLen depth **
          validateResultPost bytes base floor cursorOff endOff fuel endPtr r))) :
    cpsTripleWithin (4 + (1 + nVal) + 15) (RlpWalkNextStrictTie.S + 136)
      (raVal &&& ~~~1) (RlpWalkNextStrictTie.sharedCode.union validateCR)
      ((regIs .x12 oldOut) ** (regIs .x5 cursorVal) ** (regIs .x13 pfx) **
        (regIs .x10 old10) ** (regIs .x1 oldRa) **
        (regIs .x2 sp) ** (regIs .x0 (0 : Word)) **
        sharedValidateCallerRest sp raVal cursor outerNext outerStatus
          outerLen depth)
      R :=
  shared_long_arm_validate_then_cont cursorVal pfx oldOut old10 oldRa
    (raVal &&& ~~~1)
    (by pcf_validate_cps) hval
    (fun r =>
      shared_after_validate_cont_from_result (bytes := bytes) (base := base)
        (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
        (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus outerLen
        depth r (hsucc r) (hfail r))


/-- `validateCyclePost` is the dependent-post packaging of the validate
return frame + preserved pre resources + `validateResultPost`. -/
theorem validateCyclePost_eq_cpsDepPost
    (bytes : List (BitVec 8)) (base : Word) (floor fuel cursorOff endOff : Nat)
    (sp raVal : Word) (P : Assertion) :
    validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P =
      cpsDepPost (fun r =>
        ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) **
          (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
          memOwn (sp + 8) **
          (memIs (sp + 16) (base + BitVec.ofNat 64 endOff)) **
          regOwn .x5 **
          bytesRegion base bytes **
          ⌜ValidateFuel bytes fuel cursorOff endOff⌝ **
          (validateResultPost bytes base floor cursorOff endOff fuel
            (base + BitVec.ofNat 64 endOff) r) ** P)) := rfl

/-! ## Entry → knot composition

`validate_entry_to_knot_cps` lands at `V+36` with the post-prologue frame
(`x2 = sp`, spills filled).  `ValidateMachineContract.proof` is packaged against
`validateCyclePre` (entry-shaped `x2 = sp+32`) at that same PC — that packaging
does not match the machine mid-state.  The bind below is the honest interface:
sequence entry→knot with a knot body whose precondition is the real
post-prologue frame. -/

/-- Nonempty, well-ordered payload: prologue through precheck not-taken,
landing at the knot entry `V+36` with the post-prologue frame. -/
theorem validate_entry_to_knot_cps
    (sp raVal cursor endPtr x5Old : Word)
    (hne : cursor ≠ endPtr) (horder : endPtr.ult cursor ≠ true) :
    cpsTripleWithin 9 validateEntry (validateEntry + 36) validateCR
      ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
        (regIs .x11 endPtr) ** (regIs .x5 x5Old) **
        memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16))
      ((regIs .x2 sp) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
        (regIs .x5 endPtr) ** (regIs .x11 endPtr) **
        (memIs sp raVal) ** (memIs (sp + 8) cursor) **
        (memIs (sp + 16) endPtr)) := by
  have hpro := validate_prologue_cps sp raVal cursor endPtr
  have hpro' := cpsTripleWithin_frameR (regIs .x5 x5Old) (by pcf_validate_cps) hpro
  have hload := validate_loads_cps sp cursor endPtr x5Old endPtr
  have hload' := cpsTripleWithin_frameR
    ((regIs .x1 raVal) ** (memIs sp raVal)) (by pcf_validate_cps) hload
  have hempty := validate_empty_branch_cps cursor endPtr
  have hntakenEmpty0 := cpsBranchWithin_ntakenStripPure2 hempty (by
    intro _ hQt
    obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
    exact absurd ((sepConj_pure_right _).mp h_rest).2 hne)
  have hntakenEmpty := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x11 endPtr) ** (regIs .x1 raVal) **
      (memIs sp raVal) ** (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr))
    (by pcf_validate_cps) hntakenEmpty0
  have hpre := validate_precheck_branch_cps cursor endPtr
  have hntakenPre0 := cpsBranchWithin_ntakenStripPure2 hpre (by
    intro _ hQt
    obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
    exact absurd ((sepConj_pure_right _).mp h_rest).2 horder)
  have hntakenPre := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x11 endPtr) ** (regIs .x1 raVal) **
      (memIs sp raVal) ** (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr))
    (by pcf_validate_cps) hntakenPre0
  have s1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hpro' hload'
  have s2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s1 hntakenEmpty
  have s3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s2 hntakenPre
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp) s3)

/-- Post-prologue / knot-entry frame produced by `validate_entry_to_knot_cps`. -/
def validateKnotFrame
    (sp raVal cursor endPtr : Word) : Assertion :=
  ((regIs .x2 sp) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
    (regIs .x5 endPtr) ** (regIs .x11 endPtr) **
    (memIs sp raVal) ** (memIs (sp + 8) cursor) **
    (memIs (sp + 16) endPtr))

theorem validate_entry_then_knot_dep
    {α : Type} {nKnot : Nat} {P : Assertion} {post : α → Assertion}
    (sp raVal cursor endPtr x5Old exit_ : Word)
    (hne : cursor ≠ endPtr) (horder : endPtr.ult cursor ≠ true)
    (hP : P.pcFree)
    (hknot : cpsTripleWithin nKnot (validateEntry + 36) exit_ validateCR
      (validateKnotFrame sp raVal cursor endPtr ** P) (cpsDepPost post)) :
    cpsTripleWithin (9 + nKnot) validateEntry exit_ validateCR
      ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
        (regIs .x11 endPtr) ** (regIs .x5 x5Old) **
        memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) ** P)
      (cpsDepPost post) := by
  have hentry0 := validate_entry_to_knot_cps sp raVal cursor endPtr x5Old
    hne horder
  have hentry := cpsTripleWithin_frameR P hP hentry0
  have hentry' : cpsTripleWithin 9 validateEntry (validateEntry + 36) validateCR
      ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
        (regIs .x11 endPtr) ** (regIs .x5 x5Old) **
        memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) ** P)
      (validateKnotFrame sp raVal cursor endPtr ** P) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => by
        simp only [validateKnotFrame]
        xperm_chunked hp) hentry
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hentry' hknot

/-- Same bind with `wholeCode` extending `validateCR` (MachineContract code). -/
theorem validate_entry_then_knot_dep_extend
    {α : Type} {nKnot : Nat} {P : Assertion} {post : α → Assertion}
    {wholeCode : CodeReq}
    (sp raVal cursor endPtr x5Old exit_ : Word)
    (hne : cursor ≠ endPtr) (horder : endPtr.ult cursor ≠ true)
    (hP : P.pcFree)
    (hvalidateSub : ∀ a i, validateCR a = some i → wholeCode a = some i)
    (hknot : cpsTripleWithin nKnot (validateEntry + 36) exit_ wholeCode
      (validateKnotFrame sp raVal cursor endPtr ** P) (cpsDepPost post)) :
    cpsTripleWithin (9 + nKnot) validateEntry exit_ wholeCode
      ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
        (regIs .x11 endPtr) ** (regIs .x5 x5Old) **
        memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) ** P)
      (cpsDepPost post) := by
  have hentry0 := validate_entry_to_knot_cps sp raVal cursor endPtr x5Old
    hne horder
  have hentryU := cpsTripleWithin_extend_code hvalidateSub hentry0
  have hentry := cpsTripleWithin_frameR P hP hentryU
  have hentry' : cpsTripleWithin 9 validateEntry (validateEntry + 36) wholeCode
      ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
        (regIs .x11 endPtr) ** (regIs .x5 x5Old) **
        memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) ** P)
      (validateKnotFrame sp raVal cursor endPtr ** P) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => by
        simp only [validateKnotFrame]
        xperm_chunked hp) hentry
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hentry' hknot

/-- Lift a knot body stated with `validateCyclePost` into the dependent-post
bind (definitional via `validateCyclePost_eq_cpsDepPost`). -/
theorem validate_entry_then_knot_cycle_post
    {nKnot : Nat} {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff endOff : Nat} {P : Assertion}
    {wholeCode : CodeReq}
    (sp raVal cursor endPtr x5Old exit_ : Word)
    (hne : cursor ≠ endPtr) (horder : endPtr.ult cursor ≠ true)
    (hP : P.pcFree)
    (hvalidateSub : ∀ a i, validateCR a = some i → wholeCode a = some i)
    (hknot : cpsTripleWithin nKnot (validateEntry + 36) exit_ wholeCode
      (validateKnotFrame sp raVal cursor endPtr ** P)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P)) :
    cpsTripleWithin (9 + nKnot) validateEntry exit_ wholeCode
      ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
        (regIs .x11 endPtr) ** (regIs .x5 x5Old) **
        memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) ** P)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P) := by
  simpa [validateCyclePost_eq_cpsDepPost] using
    (validate_entry_then_knot_dep_extend (α := ValidateResult)
      (post := fun r =>
        ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) **
          (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
          memOwn (sp + 8) **
          (memIs (sp + 16) (base + BitVec.ofNat 64 endOff)) **
          regOwn .x5 **
          bytesRegion base bytes **
          ⌜ValidateFuel bytes fuel cursorOff endOff⌝ **
          (validateResultPost bytes base floor cursorOff endOff fuel
            (base + BitVec.ofNat 64 endOff) r) ** P))
      sp raVal cursor endPtr x5Old exit_ hne horder hP hvalidateSub
      (by simpa [validateCyclePost_eq_cpsDepPost] using hknot))

/-- Shared-frame cells preserved across validate but not part of validate's
own 32-byte frame (`sp_v = sp_shared - 32`).  Depth + zero + outer spills. -/
def sharedValidateCallerExtras
    (sp outerNext outerStatus outerLen depth : Word) : Assertion :=
  ((regIs .x9 depth) ** (regIs .x0 (0 : Word)) **
    (memIs (sp + 24) outerNext) ** (memIs (sp + 32) outerStatus) **
    (memIs (sp + 40) outerLen))

theorem sharedValidateCallerAmbient_of_extras
    (sp raVal cursor outerNext outerStatus outerLen depth : Word) :
    ∀ hp,
      ((regIs .x1 (RlpWalkNextStrictTie.S + 160)) ** (regIs .x2 sp) **
        (memIs sp raVal) ** (memIs (sp + 8) cursor) **
        sharedValidateCallerExtras sp outerNext outerStatus outerLen depth) hp →
      sharedValidateCallerAmbient sp raVal cursor outerNext outerStatus
        outerLen depth hp := by
  intro hp h
  simp only [sharedValidateCallerAmbient, sharedValidateCallerExtras] at h ⊢
  xperm_chunked h

/-- Frame shared extras through `validate_entry_then_knot_dep` (validateCR). -/
theorem validate_entry_then_knot_dep_frame_extras
    {α : Type} {nKnot : Nat} {P : Assertion} {post : α → Assertion}
    (sp raVal cursor endPtr x5Old exit_ outerNext outerStatus outerLen
      depth : Word)
    (hne : cursor ≠ endPtr) (horder : endPtr.ult cursor ≠ true)
    (hP : P.pcFree)
    (hknot : cpsTripleWithin nKnot (validateEntry + 36) exit_ validateCR
      (validateKnotFrame sp raVal cursor endPtr **
        sharedValidateCallerExtras sp outerNext outerStatus outerLen depth **
        P)
      (cpsDepPost post)) :
    cpsTripleWithin (9 + nKnot) validateEntry exit_ validateCR
      ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
        (regIs .x11 endPtr) ** (regIs .x5 x5Old) **
        memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) **
        sharedValidateCallerExtras sp outerNext outerStatus outerLen depth **
        P)
      (cpsDepPost post) := by
  have hextras :
      (sharedValidateCallerExtras sp outerNext outerStatus outerLen depth).pcFree := by
    simp only [sharedValidateCallerExtras]
    pcf_validate_cps
  have hP' : (sharedValidateCallerExtras sp outerNext outerStatus outerLen depth **
      P).pcFree := pcFree_sepConj hextras hP
  have hknot' :
      cpsTripleWithin nKnot (validateEntry + 36) exit_ validateCR
        (validateKnotFrame sp raVal cursor endPtr **
          (sharedValidateCallerExtras sp outerNext outerStatus outerLen depth **
            P))
        (cpsDepPost post) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => hp) hknot
  exact validate_entry_then_knot_dep sp raVal cursor endPtr x5Old exit_
    hne horder hP' hknot'

/-- From `validateCyclePre` at `validateEntry` through prologue/precheck to
`validateKnotFrame` at `V+36`, preserving the ambient fuel/bytes/`P` frame. -/
theorem validate_cycle_pre_to_knot
    {bytes : List (BitVec 8)} {base : Word} {fuel cursorOff endOff : Nat}
    {P : Assertion}
    (sp raVal : Word)
    (hne : (base + BitVec.ofNat 64 cursorOff) ≠
      (base + BitVec.ofNat 64 endOff))
    (horder : (base + BitVec.ofNat 64 endOff).ult
      (base + BitVec.ofNat 64 cursorOff) ≠ true)
    (hP : P.pcFree) :
    cpsTripleWithin 9 validateEntry (validateEntry + 36) validateCR
      (validateCyclePre bytes base fuel cursorOff endOff sp raVal P)
      (validateKnotFrame sp raVal
        (base + BitVec.ofNat 64 cursorOff)
        (base + BitVec.ofNat 64 endOff) **
        (regIs .x0 (0 : Word)) ** regOwn .x12 **
        bytesRegion base bytes **
        ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P) := by
  let cursor := base + BitVec.ofNat 64 cursorOff
  let endPtr := base + BitVec.ofNat 64 endOff
  let ambient : Assertion :=
    ((regIs .x0 (0 : Word)) ** regOwn .x12 ** bytesRegion base bytes **
      ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P)
  have hambientPc : ambient.pcFree := by
    simp only [ambient]
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_pure
      | exact hP
      | exact bytesRegion_pcFree _ _
  have hforall : ∀ x5Old,
      cpsTripleWithin 9 validateEntry (validateEntry + 36) validateCR
        ((((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) **
          (regIs .x10 cursor) ** (regIs .x11 endPtr) **
          memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) **
          ambient) ** (regIs .x5 x5Old)))
        (validateKnotFrame sp raVal cursor endPtr ** ambient) := by
    intro x5Old
    have hentry0 := validate_entry_to_knot_cps sp raVal cursor endPtr x5Old
      hne horder
    have hentry := cpsTripleWithin_frameR ambient hambientPc hentry0
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => by
        simp only [validateKnotFrame, ambient, cursor, endPtr]
        xperm_chunked hp) hentry
  have hown :=
    cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5) hforall
  have hpre : cpsTripleWithin 9 validateEntry (validateEntry + 36) validateCR
      (validateCyclePre bytes base fuel cursorOff endOff sp raVal P)
      (validateKnotFrame sp raVal cursor endPtr ** ambient) :=
    cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [validateCyclePre, ambient, cursor, endPtr] at hp ⊢
        xperm_chunked hp)
      (fun _ hp => hp) hown
  simpa [ambient, cursor, endPtr] using hpre

/-- Package an entry-level `ValidateMachineContract.proof` from a knot body
on `validateKnotFrame` (the honest `V+36` mid-state). -/
theorem validate_machine_proof_of_knot
    {nKnot : Nat} {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff endOff : Nat} {P : Assertion}
    {wholeCode : CodeReq}
    (sp raVal exit_ : Word)
    (hne : (base + BitVec.ofNat 64 cursorOff) ≠
      (base + BitVec.ofNat 64 endOff))
    (horder : (base + BitVec.ofNat 64 endOff).ult
      (base + BitVec.ofNat 64 cursorOff) ≠ true)
    (hP : P.pcFree)
    (hvalidateSub : ∀ a i, validateCR a = some i → wholeCode a = some i)
    (hknot : cpsTripleWithin nKnot (validateEntry + 36) exit_ wholeCode
      (validateKnotFrame sp raVal
        (base + BitVec.ofNat 64 cursorOff)
        (base + BitVec.ofNat 64 endOff) **
        (regIs .x0 (0 : Word)) ** regOwn .x12 **
        bytesRegion base bytes **
        ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P)) :
    ∃ steps, cpsTripleWithin steps validateEntry exit_ wholeCode
      (validateCyclePre bytes base fuel cursorOff endOff sp raVal P)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P) := by
  let cursor := base + BitVec.ofNat 64 cursorOff
  let endPtr := base + BitVec.ofNat 64 endOff
  have htoKnot0 := validate_cycle_pre_to_knot (bytes := bytes) (base := base)
    (fuel := fuel) (cursorOff := cursorOff) (endOff := endOff) (P := P)
    sp raVal hne horder hP
  have htoKnot := cpsTripleWithin_extend_code hvalidateSub htoKnot0
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) htoKnot hknot
  exact ⟨9 + nKnot, hseq⟩

/-- Discharge `ValidateFromSharedGoal` by packaging: nested alias from the
Shared family, plus a supplied entry-level CPS proof. -/
theorem validateFromSharedGoal_discharge
    (bytes : List (BitVec 8)) (base : Word) (floor fuel : Nat)
    (cursorOff endOff : Nat) (sp raVal exit_ : Word)
    (wholeCode : CodeReq) (P : Assertion) :
    ValidateFromSharedGoal bytes base floor fuel cursorOff endOff
      sp raVal exit_ wholeCode P := by
  intro hexit hP hvalidateSub hbase_aligned hcursor hwindow hover hnowrap
    hvalid hitem hK hsharedFam hproof
  have hdisj :
      (CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
        (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
          (GuestAddrs.rlp_walk_next_nested + 0)))).Disjoint
        RlpWalkNextStrictTie.sharedCode :=
    CodeReq.Disjoint.singleton_ofProg
      (CodeReq.ofProg_none_range_len
        RlpWalkNextStrictTie.S rlpWalkNextShared_prog 52
        (GuestAddrs.rlp_walk_next_nested : Word)
        RlpWalkNextStrictTie.shared_length
        (by
          intro k hk heq
          have hS : RlpWalkNextStrictTie.S.toNat =
              GuestAddrs.rlp_walk_next_shared := by decide
          have hN : (GuestAddrs.rlp_walk_next_nested : Word).toNat =
              GuestAddrs.rlp_walk_next_nested := by decide
          simp only [GuestAddrs.rlp_walk_next_shared] at hS
          have h := congrArg BitVec.toNat heq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h
          rw [hS, hN] at h
          simp only [GuestAddrs.rlp_walk_next_nested] at h
          omega))
  have hnested : ∀ k, k < fuel →
      Nonempty (IndexedCpsContract k
        (GuestAddrs.rlp_walk_next_nested : Word) (validateEntry + 40)
        nestedMachineCode
        ((regIs .x1 (validateEntry + 40)) ** P)
        (cpsDepPost (validateResultDependentPost bytes base floor
          cursorOff endOff fuel))) := by
    intro k hk
    obtain ⟨hshared⟩ := hsharedFam k hk
    simpa [nestedMachineCode] using
      (validate_nested_alias_indexed (fuel := k) hP hdisj hshared)
  exact validate_machine_contract_statement
    hbase_aligned hcursor hwindow hover hnowrap hvalid hexit hP
    hvalidateSub hsharedFam hnested hitem hK hproof

/-! ## Validate entry proof → call-site `hval` (post bridge)

`validateCyclePost` → caller ambient + result + `validateCallerSlack` +
`validatePreservedResources`.  Call-site *pre* → `validateCyclePre` still
open under `SharedListArmsFromValidateGoal`. -/

theorem validateCyclePost_to_callerAmbient
    (bytes : List (BitVec 8)) (base : Word) (floor fuel cursorOff endOff : Nat)
    (sp_v sp raVal cursor outerNext outerStatus outerLen depth : Word)
    (hsp : sp = sp_v + 32)
    (hra : raVal = RlpWalkNextStrictTie.S + 160) :
    ∀ hp,
      validateCyclePost bytes base floor fuel cursorOff endOff sp_v raVal
        (sharedValidateCallerRest sp raVal cursor outerNext outerStatus
          outerLen depth) hp →
      (cpsDepPost (fun r =>
        sharedValidateCallerAmbient sp raVal cursor outerNext outerStatus
          outerLen depth **
          validateResultPost bytes base floor cursorOff endOff fuel
            (base + BitVec.ofNat 64 endOff) r **
          validateCallerSlack sp_v **
          validatePreservedResources bytes base fuel cursorOff endOff)) hp := by
  intro hp h
  subst hsp hra
  simp only [validateCyclePost, cpsDepPost, sharedValidateCallerAmbient,
    sharedValidateCallerRest, validateCallerSlack, validatePreservedResources] at h ⊢
  rcases h with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  -- Group as (ambient shape) ** result ** memIs-slack ** preserved, then memIs→memOwn.
  have e8 : sp_v + 32 + 8 = sp_v + 40 := by bv_omega
  have e24 : sp_v + 32 + 24 = sp_v + 56 := by bv_omega
  have e32 : sp_v + 32 + 32 = sp_v + 64 := by bv_omega
  have e40 : sp_v + 32 + 40 = sp_v + 72 := by bv_omega
  let ambient' : Assertion :=
    ((regIs .x9 depth) ** (regIs .x0 (0 : Word)) **
      (regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
      (regIs .x2 (sp_v + 32)) **
      (memIs (sp_v + 32) (RlpWalkNextStrictTie.S + 160)) **
      (memIs (sp_v + 40) cursor) **
      (memIs (sp_v + 56) outerNext) **
      (memIs (sp_v + 64) outerStatus) **
      (memIs (sp_v + 72) outerLen))
  let slackIs : Assertion :=
    ((memIs sp_v (RlpWalkNextStrictTie.S + 160)) **
      memOwn (sp_v + 8) **
      (memIs (sp_v + 16) (base + BitVec.ofNat 64 endOff)))
  let result' : Assertion :=
    validateResultPost bytes base floor cursorOff endOff fuel
      (base + BitVec.ofNat 64 endOff) r
  let preserved : Assertion :=
    validatePreservedResources bytes base fuel cursorOff endOff
  have hr1 : (ambient' ** result' ** slackIs ** preserved) hp := by
    have hr' := hr
    simp only [e8, e24, e32, e40, ambient', result', slackIs, preserved,
      validatePreservedResources] at hr' ⊢
    xperm_chunked hr'
  rw [e8, e24, e32, e40]
  -- `**` is right-assoc: ambient' ** (result' ** (slackIs ** preserved)).
  have hr2 : (ambient' ** result' ** validateCallerSlack sp_v ** preserved) hp := by
    have hslack :
        ∀ hq, slackIs hq → validateCallerSlack sp_v hq :=
      sepConj_mono memIs_implies_memOwn
        (sepConj_mono (fun _ h => h) memIs_implies_memOwn)
    have hinner :
        ∀ hq, (slackIs ** preserved) hq →
          (validateCallerSlack sp_v ** preserved) hq :=
      sepConj_mono_left hslack
    have hmid :
        ∀ hq, (result' ** slackIs ** preserved) hq →
          (result' ** validateCallerSlack sp_v ** preserved) hq :=
      sepConj_mono_right hinner
    exact sepConj_mono_right hmid hp
      (by simpa [slackIs, validateCallerSlack] using hr1)
  simpa [ambient', result', preserved, validatePreservedResources,
    validateCallerSlack] using hr2

/-- Post-only packaging: same cyclePre, ambient-shaped post (+ validate slack
+ preserved bytes/fuel/`x5`). -/
theorem validate_machine_proof_post_to_ambient
    {n : Nat} {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff endOff : Nat}
    (sp_v sp raVal cursor outerNext outerStatus outerLen depth endPtr : Word)
    (hsp : sp = sp_v + 32)
    (hra : raVal = RlpWalkNextStrictTie.S + 160)
    (hend : endPtr = base + BitVec.ofNat 64 endOff)
    (hproof : cpsTripleWithin n validateEntry
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word)) validateCR
      (validateCyclePre bytes base fuel cursorOff endOff sp_v raVal
        (sharedValidateCallerRest sp raVal cursor outerNext outerStatus
          outerLen depth))
      (validateCyclePost bytes base floor fuel cursorOff endOff sp_v raVal
        (sharedValidateCallerRest sp raVal cursor outerNext outerStatus
          outerLen depth))) :
    cpsTripleWithin n validateEntry
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word)) validateCR
      (validateCyclePre bytes base fuel cursorOff endOff sp_v raVal
        (sharedValidateCallerRest sp raVal cursor outerNext outerStatus
          outerLen depth))
      (cpsDepPost (fun r =>
        sharedValidateCallerAmbient sp raVal cursor outerNext outerStatus
          outerLen depth **
          validateResultPost bytes base floor cursorOff endOff fuel endPtr r **
          validateCallerSlack sp_v **
          validatePreservedResources bytes base fuel cursorOff endOff)) := by
  have hpost := validateCyclePost_to_callerAmbient
    bytes base floor fuel cursorOff endOff sp_v sp raVal cursor outerNext
    outerStatus outerLen depth hsp hra
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hproof
  intro hp h
  have h' := hpost hp h
  simpa [hend] using h'

/-! ## Knot body under smaller Shared (induction edge)

`rlp_validate_payload_nonempty_cps_under_shared` peels `x1` then runs the
nested Shared call.  `validateKnotFrameRest` is the post-prologue frame
without `x1`, so the nonempty pre rearranges to `validateKnotFrame ** ambient`.
The `hcont` family (V+40 → `validateCyclePost`) is the remaining Validate-side
status residual at child fuel. -/

def validateKnotFrameRest
    (sp raVal cursor endPtr : Word) : Assertion :=
  ((regIs .x2 sp) ** (regIs .x10 cursor) **
    (regIs .x5 endPtr) ** (regIs .x11 endPtr) **
    (memIs sp raVal) ** (memIs (sp + 8) cursor) **
    (memIs (sp + 16) endPtr))

theorem validateKnotFrame_of_rest
    (sp raVal cursor endPtr : Word) :
    ∀ hp,
      ((regIs .x1 raVal) ** validateKnotFrameRest sp raVal cursor endPtr) hp →
      validateKnotFrame sp raVal cursor endPtr hp := by
  intro hp h
  simp only [validateKnotFrame, validateKnotFrameRest] at h ⊢
  xperm_chunked h

theorem validate_knot_body_under_shared
    {nShared nCont : Nat} {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff endOff : Nat} {P : Assertion}
    {contCode wholeCode : CodeReq}
    (sp raVal exit_ : Word) (offset : BitVec 21)
    (hoffset : (validateEntry + 36) + signExtend21 offset =
      (GuestAddrs.rlp_walk_next_nested : Word))
    (halign : ((validateEntry + 40) &&& ~~~(1 : Word)) = validateEntry + 40)
    (hP : P.pcFree)
    (hcallCode : (CodeReq.singleton (validateEntry + 36)
      (.JAL .x1 offset)).Disjoint
      ((CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
        (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
          (GuestAddrs.rlp_walk_next_nested + 0)))).union
        RlpWalkNextStrictTie.sharedCode))
    (hsharedDisj : (CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
      (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
        (GuestAddrs.rlp_walk_next_nested + 0)))).Disjoint
      RlpWalkNextStrictTie.sharedCode)
    (houterDisj :
      ((CodeReq.singleton (validateEntry + 36) (.JAL .x1 offset)).union
        ((CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
          (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
            (GuestAddrs.rlp_walk_next_nested + 0)))).union
          RlpWalkNextStrictTie.sharedCode)).Disjoint contCode)
    (hbodySub : ∀ a i,
      (((CodeReq.singleton (validateEntry + 36) (.JAL .x1 offset)).union
        ((CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
          (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
            (GuestAddrs.rlp_walk_next_nested + 0)))).union
          RlpWalkNextStrictTie.sharedCode)).union contCode) a = some i →
      wholeCode a = some i)
    (hshared : cpsTripleWithin nShared
      (GuestAddrs.rlp_walk_next_shared : Word) (validateEntry + 40)
      RlpWalkNextStrictTie.sharedCode
      ((regIs .x1 (validateEntry + 40)) **
        (validateKnotFrameRest sp raVal
          (base + BitVec.ofNat 64 cursorOff)
          (base + BitVec.ofNat 64 endOff) **
          (regIs .x0 (0 : Word)) ** regOwn .x12 **
          bytesRegion base bytes **
          ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P))
      (cpsDepPost (validateResultDependentPost bytes base floor
        cursorOff endOff fuel)))
    (hcont : ∀ r, cpsTripleWithin nCont (validateEntry + 40) exit_ contCode
      (validateResultDependentPost bytes base floor cursorOff endOff fuel r)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P)) :
    cpsTripleWithin (1 + (1 + nShared) + nCont) (validateEntry + 36) exit_ wholeCode
      (validateKnotFrame sp raVal
        (base + BitVec.ofNat 64 cursorOff)
        (base + BitVec.ofNat 64 endOff) **
        (regIs .x0 (0 : Word)) ** regOwn .x12 **
        bytesRegion base bytes **
        ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P) := by
  let cursor := base + BitVec.ofNat 64 cursorOff
  let endPtr := base + BitVec.ofNat 64 endOff
  let ambient : Assertion :=
    ((regIs .x0 (0 : Word)) ** regOwn .x12 ** bytesRegion base bytes **
      ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P)
  let bodyP : Assertion :=
    validateKnotFrameRest sp raVal cursor endPtr ** ambient
  have hbodyP : bodyP.pcFree := by
    simp only [bodyP, validateKnotFrameRest, ambient]
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_pure
      | exact hP
      | exact bytesRegion_pcFree _ _
  have hshared' :
      cpsTripleWithin nShared
        (GuestAddrs.rlp_walk_next_shared : Word) (validateEntry + 40)
        RlpWalkNextStrictTie.sharedCode
        ((regIs .x1 (validateEntry + 40)) ** bodyP)
        (cpsDepPost (validateResultDependentPost bytes base floor
          cursorOff endOff fuel)) := by
    simpa [bodyP, cursor, endPtr, ambient] using hshared
  have hbody0 := rlp_validate_payload_nonempty_cps_under_shared
    (P := bodyP)
    (R := validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P)
    (post := validateResultDependentPost bytes base floor cursorOff endOff fuel)
    (contCode := contCode)
    raVal exit_ offset hoffset halign hbodyP hcallCode hsharedDisj houterDisj
    hshared' hcont
  have hbody := cpsTripleWithin_extend_code hbodySub hbody0
  refine cpsTripleWithin_weaken ?_ (fun _ hp => hp) hbody
  intro hp h
  -- (validateKnotFrame ** ambient) → (x1 ** bodyP)
  simp only [validateKnotFrame, bodyP, validateKnotFrameRest, ambient, cursor,
    endPtr] at h ⊢
  xperm_chunked h

/-- Enriched short-arm call-site resources intended to imply `validateCyclePre`.
Residual: precise-SL `x12` drop into the cycle ABI; named for Goal quotes. -/
def sharedShortValidateCallPre
    (bytes : List (BitVec 8)) (base : Word) (fuel cursorOff endOff : Nat)
    (listBase sp_v sp raVal cursor outerNext outerStatus outerLen depth
      endPtr : Word) : Assertion :=
  ((regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
    (regIs .x5 listBase) ** (regIs .x12 (listBase + 1)) **
    (regIs .x10 (listBase + 1)) ** (regIs .x11 endPtr) **
    (regIs .x2 sp) ** (regIs .x0 (0 : Word)) **
    validateCallerSlack sp_v **
    bytesRegion base bytes **
    ⌜ValidateFuel bytes fuel cursorOff endOff⌝ **
    sharedValidateCallerRest sp raVal cursor outerNext outerStatus
      outerLen depth)

end EvmAsm.Codegen.RlpWalkNextStrictFuel
