/-
  EvmAsm.Codegen.Programs.RlpWalkNextStrictFuel

  Structural checkpoint for #12300.  The strict LIST path is one mutual
  recursion, not three independent calls:

      shared -> validate_payload -> nested -> shared

  The index carried here is twice the number of bytes remaining in the current
  cursor window.  The constructors deliberately expose the three back-edges
  and require a cursor advance before each one.  The semantic postconditions
  are intentionally not in this checkpoint; this file establishes the
  well-founded shape that the eventual machine triple will consume.
-/

import EvmAsm.Codegen.Programs.RlpWalkNextStrictTie

namespace EvmAsm.Codegen.RlpWalkNextStrictFuel

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP

/-- Remaining input bytes in a cursor window.  The end is exclusive. -/
def remainingBytes (cursor endOff : Nat) : Nat := endOff - cursor

/-- The wrapper's two-fuel-per-byte budget for a cursor window. -/
def cycleFuel (cursor endOff : Nat) : Nat := 2 * remainingBytes cursor endOff

/-- Consuming at least one byte strictly decreases the two-fuel budget, even
    when the recursive call keeps the same enclosing end pointer. -/
theorem cycleFuel_strict_of_advance
    {cursor next endOff : Nat}
    (hcursor : cursor < next) (hend : next ≤ endOff) :
    cycleFuel next endOff < cycleFuel cursor endOff := by
  unfold cycleFuel remainingBytes
  omega

/-! The three call contracts are mutually recursive.  They are a structural
    skeleton, not the final machine postcondition: each list/item arm records
    the exact byte-window facts needed by the eventual CPS composition. -/

mutual

  /-- `rlp_walk_next_shared`: a list arm enters payload validation. -/
  inductive SharedFuel (bytes : List Byte) : Nat → Nat → Nat → Prop where
    | nonList {cursor endOff}
        (hwindow : cursor ≤ endOff ∧ endOff ≤ bytes.length) :
        SharedFuel bytes (cycleFuel cursor endOff) cursor endOff
    | list {cursor outerEnd payloadStart payloadEnd}
        (hcursor : cursor < payloadStart)
        (hpayload : payloadStart ≤ payloadEnd)
        (hpayloadEnd : payloadEnd ≤ outerEnd)
        (houter : outerEnd ≤ bytes.length)
        (hvalidate : ValidateFuel bytes (cycleFuel payloadStart payloadEnd)
          payloadStart payloadEnd) :
        SharedFuel bytes (cycleFuel cursor outerEnd) cursor outerEnd

  /-- `rlp_validate_payload`: either the payload is empty or one item is
      decoded and the cursor advances before the next nested call. -/
  inductive ValidateFuel (bytes : List Byte) : Nat → Nat → Nat → Prop where
    | empty {cursor endOff}
        (hwindow : cursor = endOff ∧ endOff ≤ bytes.length) :
        ValidateFuel bytes (cycleFuel cursor endOff) cursor endOff
    | item {cursor next endOff}
        (hcursor : cursor < next)
        (hend : next ≤ endOff)
        (hwindow : endOff ≤ bytes.length)
        (hnested : NestedFuel bytes (cycleFuel next endOff) next endOff) :
        ValidateFuel bytes (cycleFuel cursor endOff) cursor endOff

  /-- `rlp_walk_next_nested`: one nested item returns to the shared walker at
      the advanced cursor. -/
  inductive NestedFuel (bytes : List Byte) : Nat → Nat → Nat → Prop where
    | descend {cursor next endOff}
        (hcursor : cursor < next)
        (hend : next ≤ endOff)
        (hwindow : endOff ≤ bytes.length)
        (hshared : SharedFuel bytes (cycleFuel next endOff) next endOff) :
        NestedFuel bytes (cycleFuel cursor endOff) cursor endOff

end

/-! The three edge lemmas are the checkpoint's key obligation.  The LIST arm
    may also shrink the enclosing end pointer, so retain that stronger form in
    addition to the same-window cursor lemma above. -/

theorem cycleFuel_strict_of_window
    {cursor payloadStart payloadEnd outerEnd : Nat}
    (hcursor : cursor < payloadStart)
    (hpayload : payloadStart ≤ payloadEnd)
    (hpayloadEnd : payloadEnd ≤ outerEnd) :
    cycleFuel payloadStart payloadEnd < cycleFuel cursor outerEnd := by
  unfold cycleFuel remainingBytes
  omega

theorem shared_list_edge_decreases
    {cursor outerEnd payloadStart payloadEnd : Nat}
    (hcursor : cursor < payloadStart)
    (hpayload : payloadStart ≤ payloadEnd)
    (hpayloadEnd : payloadEnd ≤ outerEnd) :
    cycleFuel payloadStart payloadEnd < cycleFuel cursor outerEnd := by
  exact cycleFuel_strict_of_window hcursor hpayload hpayloadEnd

theorem validate_item_edge_decreases
    {cursor next endOff : Nat}
    (hcursor : cursor < next) (hend : next ≤ endOff) :
    cycleFuel next endOff < cycleFuel cursor endOff := by
  exact cycleFuel_strict_of_advance hcursor hend

theorem nested_shared_edge_decreases
    {cursor next endOff : Nat}
    (hcursor : cursor < next) (hend : next ≤ endOff) :
    cycleFuel next endOff < cycleFuel cursor endOff := by
  exact cycleFuel_strict_of_advance hcursor hend

/-! ## Semantic payload post skeleton

`PayloadStrictFuel` is the postcondition shape the eventual machine proof will
produce for `rlp_validate_payload`: every accepted child is a strict item and
the remainder is validated at the advanced cursor.  Its index is the actual
remaining-byte count (not the doubled guest budget), making the relationship
between the semantic post and `cycleFuel` explicit. -/

inductive PayloadStrictFuel (bytes : List (BitVec 8)) (base : Word) (floor : Nat) :
    Nat → Nat → Nat → Prop where
  | empty {cursor endOff : Nat}
      (heq : cursor = endOff)
      (hend : endOff ≤ bytes.length) :
      PayloadStrictFuel bytes base floor (endOff - cursor) cursor endOff
  | item {cursor next endOff : Nat} {len : Word}
      (hcursor : cursor < next)
      (hend : next ≤ endOff)
      (hbytes : endOff ≤ bytes.length)
      (hitem : rlpItemDecodeStrictW bytes base cursor next endOff len (floor + 1))
      (hrest : PayloadStrictFuel bytes base floor (endOff - next) next endOff) :
      PayloadStrictFuel bytes base floor (endOff - cursor) cursor endOff

theorem payloadFuel_step_lt
    {cursor next endOff : Nat}
    (hcursor : cursor < next) (hend : next ≤ endOff) :
    endOff - next < endOff - cursor := by
  omega

theorem payloadFuel_guest_budget_lt
    {cursor next endOff : Nat}
    (hcursor : cursor < next) (hend : next ≤ endOff) :
    cycleFuel next endOff < cycleFuel cursor endOff := by
  exact cycleFuel_strict_of_advance hcursor hend

/-! ## CPS checkpoint: empty-payload cursor/end threading

The first machine composition checkpoint is deliberately the empty-payload arm
of `rlp_validate_payload`.  It closes the frame protocol and the cursor/end
threading before the recursive call is introduced: the validator saves both
input pointers, compares them, and returns status zero with the frame restored.
The nonempty arm will replace the branch's impossible case by the mutual fuel
induction above and is the next semantic step. -/

/-! These edge lemmas are the induction interface: the eventual mutual machine
    proof may recurse through any of the three constructors only after applying
    the corresponding strict inequality above.  Keeping this checkpoint
    separate prevents a semantic postcondition from hiding a non-decreasing
    LIST arm. -/

/-! ## CPS checkpoint (machine-facing, empty payload)

This is the first consumer of the fuel module's cursor contract.  It proves
the actual validator's empty-payload path: both pointers are saved and
reloaded, the equality branch reaches the success epilogue, and the frame is
restored with status zero.  The nonempty branch remains the mutual-induction
step that will consume `PayloadStrictFuel`. -/

abbrev validateEntry : Word := (GuestAddrs.rlp_validate_payload : Word)
abbrev validateCR : CodeReq := CodeReq.ofProg validateEntry rlpValidatePayload_prog

local macro "pcf_validate_cps" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure)

theorem validate_prologue_cps (sp raVal cursor endPtr : Word) :
    cpsTripleWithin 4 validateEntry (validateEntry + 16) validateCR
      ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
       (regIs .x11 endPtr) ** memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16))
      ((regIs .x2 sp) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
       (regIs .x11 endPtr) ** (memIs sp raVal) ** (memIs (sp + 8) cursor) **
       (memIs (sp + 16) endPtr)) := by
  have h0 := addi_spec_gen_same_within .x2 (sp + 32) (-32 : BitVec 12) validateEntry
    (by decide)
  rw [show (sp + 32) + signExtend12 (-32 : BitVec 12) = sp from by
        rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide]
        bv_omega] at h0
  have h1 := sd_spec_gen_own_within .x2 .x1 sp raVal (0 : BitVec 12) (validateEntry + 4)
  have h2 := sd_spec_gen_own_within .x2 .x10 sp cursor (8 : BitVec 12) (validateEntry + 8)
  have h3 := sd_spec_gen_own_within .x2 .x11 sp endPtr (16 : BitVec 12) (validateEntry + 12)
  runBlock h0 h1 h2 h3

theorem validate_loads_cps (sp cursor endPtr x5Old : Word) :
    cpsTripleWithin 3 (validateEntry + 16) (validateEntry + 28) validateCR
      ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x5 x5Old) **
       (regIs .x11 endPtr) ** (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr))
      ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x5 endPtr) **
       (regIs .x11 endPtr) ** (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr)) := by
  have h4 := ld_spec_gen_within .x10 .x2 sp cursor cursor (8 : BitVec 12)
    (validateEntry + 16) (by decide)
  have h4' := cpsTripleWithin_frameR
    ((regIs .x5 x5Old) ** (regIs .x11 endPtr)) (by pcf_validate_cps) h4
  have h5 := ld_spec_gen_within .x5 .x2 sp x5Old endPtr (16 : BitVec 12)
    (validateEntry + 20) (by decide)
  have h5' := cpsTripleWithin_frameR (regIs .x11 endPtr) (by pcf_validate_cps) h5
  have h6 := mv_spec_gen_within .x11 .x5 endPtr endPtr (validateEntry + 24) (by decide)
  runBlock h4' h5' h6

theorem validate_empty_branch_cps (cursor endPtr : Word) :
    cpsBranchWithin 1 (validateEntry + 28) validateCR
      ((regIs .x10 cursor) ** (regIs .x5 endPtr))
      (validateEntry + 60)
        ((regIs .x10 cursor) ** (regIs .x5 endPtr) ** pure (cursor = endPtr))
      (validateEntry + 32)
        ((regIs .x10 cursor) ** (regIs .x5 endPtr) ** pure (cursor ≠ endPtr)) := by
  have h := beq_spec_gen_within .x10 .x5 (32 : BitVec 13) cursor endPtr
    (validateEntry + 28)
  rw [show (validateEntry + 28) + signExtend13 (32 : BitVec 13) = validateEntry + 60 from by
        rw [show signExtend13 (32 : BitVec 13) = (32 : Word) from by decide]
        bv_omega,
      show validateEntry + 28 + 4 = validateEntry + 32 from by bv_omega] at h
  have hmono : ∀ a i,
      CodeReq.singleton (validateEntry + 28) (.BEQ .x10 .x5 (32 : BitVec 13)) a = some i →
        validateCR a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr validateEntry rlpValidatePayload_prog 7
        (validateEntry + 28)
        (by rw [show rlpValidatePayload_prog.length = 23 from rfl]; norm_num)
        (by rw [show rlpValidatePayload_prog.length = 23 from rfl]; norm_num)
        (by bv_omega)
      simpa [rlpValidatePayload_prog] using hm)
  exact cpsBranchWithin_extend_code hmono h

theorem validate_success_tail_cps (sp raVal cursor endPtr : Word) :
    cpsTripleWithin 4 (validateEntry + 60) (raVal &&& ~~~1) validateCR
      ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x1 raVal) **
       (regIs .x5 endPtr) ** (regIs .x11 endPtr) ** (memIs sp raVal) **
       (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr))
      ((regIs .x2 (sp + 32)) ** (regIs .x10 (0 : Word)) ** (regIs .x1 raVal) **
       (regIs .x5 endPtr) ** (regIs .x11 endPtr) ** (memIs sp raVal) **
       (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr)) := by
  have h15 := li_spec_gen_within .x10 cursor (0 : Word) (validateEntry + 60) (by decide)
  have h16 := ld_spec_gen_within .x1 .x2 sp raVal raVal
    (0 : BitVec 12) (validateEntry + 64) (by decide)
  have h17 := addi_spec_gen_same_within .x2 sp (32 : BitVec 12)
    (validateEntry + 68) (by decide)
  have h18 := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (validateEntry + 72)
  runBlock h15 h16 h17 h18

theorem rlp_validate_payload_empty_cursor_cps
    (sp raVal cursor endPtr x5Old : Word) (heq : cursor = endPtr) :
    cpsTripleWithin 12 validateEntry (raVal &&& ~~~1) validateCR
      ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
       (regIs .x11 endPtr) ** (regIs .x5 x5Old) ** memOwn sp ** memOwn (sp + 8) **
       memOwn (sp + 16))
      ((regIs .x2 (sp + 32)) ** (regIs .x10 (0 : Word)) ** (regIs .x1 raVal) **
       (regIs .x5 endPtr) ** (regIs .x11 endPtr) ** (memIs sp raVal) **
       (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr)) := by
  have hpro := validate_prologue_cps sp raVal cursor endPtr
  have hpro' := cpsTripleWithin_frameR (regIs .x5 x5Old) (by pcf_validate_cps) hpro
  have hload := validate_loads_cps sp cursor endPtr x5Old
  have hload' := cpsTripleWithin_frameR
    ((regIs .x1 raVal) ** (memIs sp raVal)) (by pcf_validate_cps) hload
  have hbr := validate_empty_branch_cps cursor endPtr
  have htaken0 := cpsBranchWithin_takenStripPure2 hbr (by
    intro hp hq
    have hleft := (sepConj_assoc hp).mpr hq
    obtain ⟨_, _, _, _, _, hpure⟩ := hleft
    exact hpure.2 heq)
  have htaken := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x11 endPtr) ** (regIs .x1 raVal) **
      (memIs sp raVal) ** (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr))
    (by pcf_validate_cps) htaken0
  have htail := validate_success_tail_cps sp raVal cursor endPtr
  have h1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hpro' hload'
  have h2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1 htaken
  have h3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h2 htail
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) h3)

/-! ## CPS checkpoint: nested nonzero status

The nested call returns at `V + 40`; its status is tested before the payload
cursor is reloaded.  This checkpoint consumes the strict-cycle interface at
that status edge: every nonzero nested result reaches the status-7 return arm,
with the caller frame restored.  The zero-status continuation remains the
mutual recursive step. -/

theorem validate_failure_tail_cps (sp callRa cursor status x5Old raVal : Word) :
    cpsTripleWithin 4 (validateEntry + 76) (raVal &&& ~~~1) validateCR
      ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x1 callRa) **
       (regIs .x5 x5Old) ** (regIs .x11 status) ** (regIs .x0 (0 : Word)) **
       (memIs sp raVal) ** (memIs (sp + 8) cursor) **
       (memIs (sp + 16) status))
      ((regIs .x2 (sp + 32)) ** (regIs .x10 (7 : Word)) ** (regIs .x1 raVal) **
       (regIs .x5 x5Old) ** (regIs .x11 status) ** (regIs .x0 (0 : Word)) **
       (memIs sp raVal) ** (memIs (sp + 8) cursor) **
       (memIs (sp + 16) status)) := by
  have h19 := li_spec_gen_within .x10 cursor (7 : Word) (validateEntry + 76) (by decide)
  rw [show validateEntry + 76 + 4 = validateEntry + 80 from by bv_omega] at h19
  have h20 := ld_spec_gen_within .x1 .x2 sp callRa raVal
    (0 : BitVec 12) (validateEntry + 80) (by decide)
  rw [show sp + signExtend12 (0 : BitVec 12) = sp from by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega] at h20
  rw [show validateEntry + 80 + 4 = validateEntry + 84 from by bv_omega] at h20
  have h21 := addi_spec_gen_same_within .x2 sp (32 : BitVec 12)
    (validateEntry + 84) (by decide)
  have h32 : sp + signExtend12 (32 : BitVec 12) = sp + 32 := by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]
  rw [h32] at h21
  rw [show validateEntry + 84 + 4 = validateEntry + 88 from by bv_omega] at h21
  have h22 := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (validateEntry + 88)
  rw [show raVal + signExtend12 (0 : BitVec 12) = raVal from by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega] at h22
  have payload_prog_length : rlpValidatePayload_prog.length = 23 := rfl
  have h19m : ∀ a i,
      CodeReq.singleton (validateEntry + 76) (.LI .x10 (7 : Word)) a = some i →
        validateCR a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr validateEntry rlpValidatePayload_prog 19
        (validateEntry + 76) (by rw [payload_prog_length]; norm_num)
        (by rw [payload_prog_length]; norm_num) (by bv_omega)
      simpa [rlpValidatePayload_prog] using hm)
  have h20m : ∀ a i,
      CodeReq.singleton (validateEntry + 80) (.LD .x1 .x2 (0 : BitVec 12)) a = some i →
        validateCR a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr validateEntry rlpValidatePayload_prog 20
        (validateEntry + 80) (by rw [payload_prog_length]; norm_num)
        (by rw [payload_prog_length]; norm_num) (by bv_omega)
      simpa [rlpValidatePayload_prog] using hm)
  have h21m : ∀ a i,
      CodeReq.singleton (validateEntry + 84) (.ADDI .x2 .x2 (32 : BitVec 12)) a = some i →
        validateCR a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr validateEntry rlpValidatePayload_prog 21
        (validateEntry + 84) (by rw [payload_prog_length]; norm_num)
        (by rw [payload_prog_length]; norm_num) (by bv_omega)
      simpa [rlpValidatePayload_prog] using hm)
  have h22m : ∀ a i,
      CodeReq.singleton (validateEntry + 88) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i →
        validateCR a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr validateEntry rlpValidatePayload_prog 22
        (validateEntry + 88) (by rw [payload_prog_length]; norm_num)
        (by rw [payload_prog_length]; norm_num) (by bv_omega)
      simpa [rlpValidatePayload_prog] using hm)
  have h19e := cpsTripleWithin_extend_code h19m
    (cpsTripleWithin_frameR
      ((regIs .x2 sp) ** (regIs .x1 callRa) ** (regIs .x5 x5Old) **
       (regIs .x11 status) ** (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
       (memIs (sp + 8) cursor) ** (memIs (sp + 16) status))
      (by pcf_validate_cps) h19)
  have h20e := cpsTripleWithin_extend_code h20m
    (cpsTripleWithin_frameR
      ((regIs .x10 (7 : Word)) ** (regIs .x5 x5Old) ** (regIs .x11 status) **
       (regIs .x0 (0 : Word)) ** (memIs (sp + 8) cursor) ** (memIs (sp + 16) status))
      (by pcf_validate_cps) h20)
  have h21e := cpsTripleWithin_extend_code h21m
    (cpsTripleWithin_frameR
      ((regIs .x10 (7 : Word)) ** (regIs .x1 raVal) ** (regIs .x5 x5Old) **
       (regIs .x11 status) ** (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
       (memIs (sp + 8) cursor) ** (memIs (sp + 16) status))
      (by pcf_validate_cps) h21)
  have h22e := cpsTripleWithin_extend_code h22m
    (cpsTripleWithin_frameR
      ((regIs .x2 (sp + 32)) ** (regIs .x10 (7 : Word)) ** (regIs .x5 x5Old) **
       (regIs .x11 status) ** (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
       (memIs (sp + 8) cursor) ** (memIs (sp + 16) status))
      (by pcf_validate_cps) h22)
  have htail0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h19e h20e
  have htail1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) htail0 h21e
  have htail2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) htail1 h22e
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) htail2

theorem validate_nested_status_branch_cps (status : Word) :
    cpsBranchWithin 1 (validateEntry + 40) validateCR
      ((regIs .x11 status) ** (regIs .x0 (0 : Word)))
      (validateEntry + 76)
        ((regIs .x11 status) ** (regIs .x0 (0 : Word)) ** pure (status ≠ 0))
      (validateEntry + 44)
        ((regIs .x11 status) ** (regIs .x0 (0 : Word)) ** pure (status = 0)) := by
  have h := bne_spec_gen_within .x11 .x0 (36 : BitVec 13) status (0 : Word)
    (validateEntry + 40)
  rw [show (validateEntry + 40) + signExtend13 (36 : BitVec 13) = validateEntry + 76 from by
        rw [show signExtend13 (36 : BitVec 13) = (36 : Word) from by decide]
        bv_omega,
      show validateEntry + 40 + 4 = validateEntry + 44 from by bv_omega] at h
  have hmono : ∀ a i,
      CodeReq.singleton (validateEntry + 40) (.BNE .x11 .x0 (36 : BitVec 13)) a = some i →
        validateCR a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr validateEntry rlpValidatePayload_prog 10
        (validateEntry + 40)
        (by rw [show rlpValidatePayload_prog.length = 23 from rfl]; norm_num)
        (by rw [show rlpValidatePayload_prog.length = 23 from rfl]; norm_num)
        (by bv_omega)
      simpa [rlpValidatePayload_prog] using hm)
  exact cpsBranchWithin_extend_code hmono h

theorem rlp_validate_payload_nested_nonzero_status_cps
    (sp raVal cursor status x5Old : Word) (hstatus : status ≠ 0) :
    cpsTripleWithin 5 (validateEntry + 40) (raVal &&& ~~~1) validateCR
      ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x11 status) **
       (regIs .x0 (0 : Word)) ** (regIs .x1 (validateEntry + 40)) **
       (regIs .x5 x5Old) ** (memIs sp raVal) ** (memIs (sp + 8) cursor) **
       (memIs (sp + 16) status))
      ((regIs .x2 (sp + 32)) ** (regIs .x10 (7 : Word)) ** (regIs .x11 status) **
       (regIs .x0 (0 : Word)) ** (regIs .x1 raVal) ** (regIs .x5 x5Old) **
       (memIs sp raVal) ** (memIs (sp + 8) cursor) ** (memIs (sp + 16) status)) := by
  have hbr := validate_nested_status_branch_cps status
  have htaken := cpsBranchWithin_takenPath hbr (by
    intro hp hq
    have hleft := (sepConj_assoc hp).mpr hq
    obtain ⟨_, _, _, _, _, hpure⟩ := hleft
    exact hstatus hpure.2)
  have htaken' := cpsTripleWithin_weaken (fun _ hp => hp)
    sepConj_strip_pure_end2 htaken
  have hfr := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x1 (validateEntry + 40)) **
      (regIs .x5 x5Old) ** (memIs sp raVal) ** (memIs (sp + 8) cursor) **
      (memIs (sp + 16) status))
    (by pcf_validate_cps) htaken'
  have htail := validate_failure_tail_cps sp (validateEntry + 40) cursor status x5Old raVal
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hfr htail
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hseq)

end EvmAsm.Codegen.RlpWalkNextStrictFuel
