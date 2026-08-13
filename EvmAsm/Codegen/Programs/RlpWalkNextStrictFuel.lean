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

/-! ## Strict-canonicality checkpoint for the recursive payload arm

The recursive payload constructor is not merely a span proof.  Its item
conjunct is the strict wrapper relation, whose list disjunct carries a full
`decodeAux` witness.  This checkpoint consumes that conjunct at the first
non-empty payload position and returns the continuation fuel unchanged.  Thus
the mutual arm now exposes both facts needed by the eventual CPS composition:
the current child is canonically decoded (including nested-list payloads and
canonical length forms), and the remaining cursor window is still available
for the next recursive step.
-/

theorem payloadStrictFuel_nested_canonical_step
    {bytes : List (BitVec 8)} {base : Word} {floor fuel cursor endOff : Nat}
    (hpayload : PayloadStrictFuel bytes base floor fuel cursor endOff)
    (hnonempty : cursor < endOff)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hnowrap : base.toNat + endOff + 9 < 2 ^ 64) :
    ∃ next len item,
      rlpItemDecodeStrictW bytes base cursor next endOff len (floor + 1) ∧
      decodeAux (floor + 1) (bytes.drop cursor) =
        some (item, bytes.drop next) ∧
      PayloadStrictFuel bytes base floor (endOff - next) next endOff := by
  cases hpayload with
  | empty heq hend =>
      omega
  | @item cursor next endOff len hcursor hend hbytes hitem hrest =>
      have hcursor_le : cursor ≤ endOff := le_trans (Nat.le_of_lt hcursor) hend
      obtain ⟨item, hdecode⟩ := rlpItemDecodeStrictW_to_decodeAux
        bytes base cursor next endOff floor len hitem hcursor_le hend hbytes hover hnowrap
      exact ⟨next, len, item, hitem, hdecode, hrest⟩

/-! ## Branch-local machine continuation predicate

`cpsBranchWithin` and `cpsTripleWithin_seq_perm_same_cr` compose fixed
assertions.  The successful nested arm instead has a dependent post: the
decoded item chooses the next cursor, and the recursive continuation carries
the smaller payload-fuel witness at that cursor.  `ValidateK` is the local
machine-facing relation for that post.  Its pointer arguments are the machine
registers tied to the semantic Nat offsets; the saved frame words (`sp` and
`raVal`) remain fixed by the surrounding CPS frame triples.  Keeping this
relation here avoids changing the shared CPS API while making the exact
continuation obligation explicit. -/

def ValidateK (bytes : List (BitVec 8)) (base : Word) (floor : Nat)
    (cursorPtr endPtr : Word) (cursorOff endOff fuel : Nat) : Prop :=
  cursorPtr = base + BitVec.ofNat 64 cursorOff ∧
    endPtr = base + BitVec.ofNat 64 endOff ∧
    PayloadStrictFuel bytes base floor fuel cursorOff endOff

theorem validate_success_continuation
    {bytes : List (BitVec 8)} {base : Word} {floor : Nat}
    {cursorPtr endPtr : Word}
    {cursorOff endOff fuel : Nat}
    (hK : ValidateK bytes base floor cursorPtr endPtr cursorOff endOff fuel)
    (hnonempty : cursorOff < endOff)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hnowrap : base.toNat + endOff + 9 < 2 ^ 64) :
    ∃ next len item,
      rlpItemDecodeStrictW bytes base cursorOff next endOff len (floor + 1) ∧
      decodeAux (floor + 1) (bytes.drop cursorOff) =
        some (item, bytes.drop next) ∧
      ValidateK bytes base floor
        (base + BitVec.ofNat 64 next) endPtr next endOff (endOff - next) := by
  rcases hK with ⟨hcursorPtr, hendPtr, hpayload⟩
  obtain ⟨next, len, item, hitem, hdecode, hrest⟩ :=
    payloadStrictFuel_nested_canonical_step hpayload hnonempty hover hnowrap
  refine ⟨next, len, item, hitem, hdecode, ?_⟩
  exact ⟨rfl, hendPtr, hrest⟩

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
  exact cpsBranchWithin_extend_code hmono
    (cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) h)

theorem validate_precheck_branch_cps (cursor endPtr : Word) :
    cpsBranchWithin 1 (validateEntry + 32) validateCR
      ((regIs .x10 cursor) ** (regIs .x5 endPtr))
      (validateEntry + 76)
        ((regIs .x10 cursor) ** (regIs .x5 endPtr) ** pure (BitVec.ult endPtr cursor))
      (validateEntry + 36)
        ((regIs .x10 cursor) ** (regIs .x5 endPtr) ** pure (¬ BitVec.ult endPtr cursor)) := by
  have h := bltu_spec_gen_within .x5 .x10 (44 : BitVec 13) endPtr cursor
    (validateEntry + 32)
  rw [show (validateEntry + 32) + signExtend13 (44 : BitVec 13) = validateEntry + 76 from by
        rw [show signExtend13 (44 : BitVec 13) = (44 : Word) from by decide]
        bv_omega,
      show validateEntry + 32 + 4 = validateEntry + 36 from by bv_omega] at h
  have hmono : ∀ a i,
      CodeReq.singleton (validateEntry + 32) (.BLTU .x5 .x10 (44 : BitVec 13)) a = some i →
        validateCR a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr validateEntry rlpValidatePayload_prog 8
        (validateEntry + 32)
        (by rw [show rlpValidatePayload_prog.length = 23 from rfl]; norm_num)
        (by rw [show rlpValidatePayload_prog.length = 23 from rfl]; norm_num)
        (by bv_omega)
      simpa [rlpValidatePayload_prog] using hm)
  exact cpsBranchWithin_extend_code hmono
    (cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) h)

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

theorem validate_failure_tail_cps
    (sp callRa cursor status x5Old raVal memEnd : Word) :
    cpsTripleWithin 4 (validateEntry + 76) (raVal &&& ~~~1) validateCR
      ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x1 callRa) **
       (regIs .x5 x5Old) ** (regIs .x11 status) ** (regIs .x0 (0 : Word)) **
       (memIs sp raVal) ** (memIs (sp + 8) cursor) **
       (memIs (sp + 16) memEnd))
      ((regIs .x2 (sp + 32)) ** (regIs .x10 (7 : Word)) ** (regIs .x1 raVal) **
       (regIs .x5 x5Old) ** (regIs .x11 status) ** (regIs .x0 (0 : Word)) **
       (memIs sp raVal) ** (memIs (sp + 8) cursor) **
       (memIs (sp + 16) memEnd)) := by
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
       (memIs (sp + 8) cursor) ** (memIs (sp + 16) memEnd))
      (by pcf_validate_cps) h19)
  have h20e := cpsTripleWithin_extend_code h20m
    (cpsTripleWithin_frameR
      ((regIs .x10 (7 : Word)) ** (regIs .x5 x5Old) ** (regIs .x11 status) **
       (regIs .x0 (0 : Word)) ** (memIs (sp + 8) cursor) ** (memIs (sp + 16) memEnd))
      (by pcf_validate_cps) h20)
  have h21e := cpsTripleWithin_extend_code h21m
    (cpsTripleWithin_frameR
      ((regIs .x10 (7 : Word)) ** (regIs .x1 raVal) ** (regIs .x5 x5Old) **
       (regIs .x11 status) ** (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
       (memIs (sp + 8) cursor) ** (memIs (sp + 16) memEnd))
      (by pcf_validate_cps) h21)
  have h22e := cpsTripleWithin_extend_code h22m
    (cpsTripleWithin_frameR
      ((regIs .x2 (sp + 32)) ** (regIs .x10 (7 : Word)) ** (regIs .x5 x5Old) **
       (regIs .x11 status) ** (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
       (memIs (sp + 8) cursor) ** (memIs (sp + 16) memEnd))
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
  have htail := validate_failure_tail_cps sp (validateEntry + 40) cursor status x5Old raVal status
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hfr htail
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hseq)

/-! ## CPS checkpoint: zero-status loop-back

After the nested call returns status zero, the validator reloads the saved end
pointer, checks that the advanced cursor has not crossed it, stores that
cursor, and jumps to the cursor reload at `V + 16`.  The pure `ValidateK`
frame is carried unchanged through these four instructions; the recursive
validator consumes it at the next iteration. -/

theorem validate_nested_zero_loop_cps
    {bytes : List (BitVec 8)} {base : Word} {floor nextOff endOff fuel : Nat}
    (sp callRa cursorPtr endPtr : Word)
    (hcursor : ¬ BitVec.ult endPtr cursorPtr) :
    cpsTripleWithin 4 (validateEntry + 44) (validateEntry + 16) validateCR
      ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 callRa) **
       (regIs .x5 (0 : Word)) ** (regIs .x11 (0 : Word)) **
       (memIs sp callRa) ** (memIs (sp + 8) cursorPtr) **
       (memIs (sp + 16) endPtr) **
       ⌜ValidateK bytes base floor cursorPtr endPtr nextOff endOff fuel⌝)
      ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 callRa) **
       (regIs .x5 endPtr) ** (regIs .x11 (0 : Word)) **
       (memIs sp callRa) ** (memIs (sp + 8) cursorPtr) **
       (memIs (sp + 16) endPtr) **
       ⌜ValidateK bytes base floor cursorPtr endPtr nextOff endOff fuel⌝) := by
  have hld := ld_spec_gen_within .x5 .x2 sp (0 : Word) endPtr
    (16 : BitVec 12) (validateEntry + 44) (by decide)
  have hld_off : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
  rw [hld_off,
      show validateEntry + 44 + 4 = validateEntry + 48 by bv_omega] at hld
  have hbr := bltu_spec_gen_within .x5 .x10 (28 : BitVec 13) endPtr cursorPtr
    (validateEntry + 48)
  rw [show (validateEntry + 48) + signExtend13 (28 : BitVec 13) =
      validateEntry + 76 from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]
        bv_omega,
      show validateEntry + 48 + 4 = validateEntry + 52 from by bv_omega] at hbr
  have hbr' := cpsBranchWithin_ntakenPath hbr (by
    intro hp hq
    have hleft := (sepConj_assoc hp).mpr hq
    obtain ⟨_, _, _, _, _, hpure⟩ := hleft
    exact hcursor hpure.2)
  have hbr0 := cpsTripleWithin_weaken (fun _ hp => hp)
    sepConj_strip_pure_end2 hbr'
  have hsd := sd_spec_gen_within .x2 .x10 sp cursorPtr cursorPtr
    (8 : BitVec 12) (validateEntry + 52)
  have hsd_off : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
  rw [hsd_off,
      show validateEntry + 52 + 4 = validateEntry + 56 by bv_omega] at hsd
  have hjal := jal_x0_spec_gen_within (-40 : BitVec 21) (validateEntry + 56)
  have hjal_off : signExtend21 (-40 : BitVec 21) = (-40 : Word) := by decide
  rw [hjal_off,
      show validateEntry + 56 + (-40 : Word) = validateEntry + 16 by decide] at hjal
  have payload_prog_length : rlpValidatePayload_prog.length = 23 := rfl
  have hldm : ∀ a i,
      CodeReq.singleton (validateEntry + 44)
        (.LD .x5 .x2 (16 : BitVec 12)) a = some i → validateCR a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr validateEntry rlpValidatePayload_prog 11
        (validateEntry + 44) (by rw [payload_prog_length]; norm_num)
        (by rw [payload_prog_length]; norm_num) (by bv_omega)
      simpa [rlpValidatePayload_prog] using hm)
  have hbrm : ∀ a i,
      CodeReq.singleton (validateEntry + 48)
        (.BLTU .x5 .x10 (28 : BitVec 13)) a = some i → validateCR a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr validateEntry rlpValidatePayload_prog 12
        (validateEntry + 48) (by rw [payload_prog_length]; norm_num)
        (by rw [payload_prog_length]; norm_num) (by bv_omega)
      simpa [rlpValidatePayload_prog] using hm)
  have hsdm : ∀ a i,
      CodeReq.singleton (validateEntry + 52)
        (.SD .x2 .x10 (8 : BitVec 12)) a = some i → validateCR a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr validateEntry rlpValidatePayload_prog 13
        (validateEntry + 52) (by rw [payload_prog_length]; norm_num)
        (by rw [payload_prog_length]; norm_num) (by bv_omega)
      simpa [rlpValidatePayload_prog] using hm)
  have hjalm : ∀ a i,
      CodeReq.singleton (validateEntry + 56)
        (.JAL .x0 (-40 : BitVec 21)) a = some i → validateCR a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr validateEntry rlpValidatePayload_prog 14
        (validateEntry + 56) (by rw [payload_prog_length]; norm_num)
        (by rw [payload_prog_length]; norm_num) (by bv_omega)
      simpa [rlpValidatePayload_prog] using hm)
  have hldE := cpsTripleWithin_extend_code hldm hld
  have hbrE := cpsTripleWithin_extend_code hbrm hbr0
  have hsdE := cpsTripleWithin_extend_code hsdm hsd
  have hjalE := cpsTripleWithin_extend_code hjalm hjal
  have hld' := cpsTripleWithin_frameR
    ((regIs .x10 cursorPtr) ** (regIs .x1 callRa) **
      (regIs .x11 (0 : Word)) ** (memIs sp callRa) **
      (memIs (sp + 8) cursorPtr) **
      ⌜ValidateK bytes base floor cursorPtr endPtr nextOff endOff fuel⌝)
    (by pcf_validate_cps) hldE
  have hbr'' := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x1 callRa) **
      (regIs .x11 (0 : Word)) ** (memIs sp callRa) **
      (memIs (sp + 8) cursorPtr) ** (memIs (sp + 16) endPtr) **
      ⌜ValidateK bytes base floor cursorPtr endPtr nextOff endOff fuel⌝)
    (by pcf_validate_cps) hbrE
  have hsd' := cpsTripleWithin_frameR
    ((regIs .x1 callRa) ** (regIs .x5 endPtr) ** (regIs .x11 (0 : Word)) **
      (memIs sp callRa) ** (memIs (sp + 16) endPtr) **
      ⌜ValidateK bytes base floor cursorPtr endPtr nextOff endOff fuel⌝)
    (by pcf_validate_cps) hsdE
  have hjal' := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 callRa) **
      (regIs .x5 endPtr) ** (regIs .x11 (0 : Word)) ** (memIs sp callRa) **
      (memIs (sp + 8) cursorPtr) ** (memIs (sp + 16) endPtr) **
      ⌜ValidateK bytes base floor cursorPtr endPtr nextOff endOff fuel⌝)
    (by pcf_validate_cps) hjalE
  have hjal'' := cpsTripleWithin_weaken
    (fun h hp => (sepConj_emp_left h).mpr hp)
    (fun h hp => (sepConj_emp_left h).mp hp) hjal'
  have h1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hld' hbr''
  have h2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1 hsd'
  have h3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h2 hjal''
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) h3

theorem validate_nested_cross_failure_cps
    (sp callRa cursor endPtr raVal : Word)
    (hcross : BitVec.ult endPtr cursor) :
    cpsTripleWithin 8 (validateEntry + 44) (raVal &&& ~~~1) validateCR
      ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x1 callRa) **
       (regIs .x5 (0 : Word)) ** (regIs .x11 (0 : Word)) **
       (regIs .x0 (0 : Word)) **
       (memIs sp raVal) ** (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr))
      ((regIs .x2 (sp + 32)) ** (regIs .x10 (7 : Word)) ** (regIs .x1 raVal) **
       (regIs .x5 endPtr) ** (regIs .x11 (0 : Word)) ** (regIs .x0 (0 : Word)) **
       (memIs sp raVal) ** (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr)) := by
  have hld := ld_spec_gen_within .x5 .x2 sp (0 : Word) endPtr
    (16 : BitVec 12) (validateEntry + 44) (by decide)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
      show validateEntry + 44 + 4 = validateEntry + 48 by bv_omega] at hld
  have hbr := bltu_spec_gen_within .x5 .x10 (28 : BitVec 13) endPtr cursor
    (validateEntry + 48)
  rw [show (validateEntry + 48) + signExtend13 (28 : BitVec 13) =
      validateEntry + 76 from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]
        bv_omega,
      show validateEntry + 48 + 4 = validateEntry + 52 by bv_omega] at hbr
  have hbr' := cpsBranchWithin_takenPath hbr (by
    intro hp hq
    have hleft := (sepConj_assoc hp).mpr hq
    obtain ⟨_, _, _, _, _, hpure⟩ := hleft
    simpa [hcross] using hpure.2)
  have hbr0 := cpsTripleWithin_weaken (fun _ hp => hp)
    sepConj_strip_pure_end2 hbr'
  have payload_prog_length : rlpValidatePayload_prog.length = 23 := rfl
  have hldm : ∀ a i,
      CodeReq.singleton (validateEntry + 44)
        (.LD .x5 .x2 (16 : BitVec 12)) a = some i → validateCR a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr validateEntry rlpValidatePayload_prog 11
        (validateEntry + 44) (by rw [payload_prog_length]; norm_num)
        (by rw [payload_prog_length]; norm_num) (by bv_omega)
      simpa [rlpValidatePayload_prog] using hm)
  have hbrm : ∀ a i,
      CodeReq.singleton (validateEntry + 48)
        (.BLTU .x5 .x10 (28 : BitVec 13)) a = some i → validateCR a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr validateEntry rlpValidatePayload_prog 12
        (validateEntry + 48) (by rw [payload_prog_length]; norm_num)
        (by rw [payload_prog_length]; norm_num) (by bv_omega)
      simpa [rlpValidatePayload_prog] using hm)
  have hldE := cpsTripleWithin_extend_code hldm hld
  have hbrE := cpsTripleWithin_extend_code hbrm hbr0
  have hld' := cpsTripleWithin_frameR
    ((regIs .x10 cursor) ** (regIs .x1 callRa) ** (regIs .x11 (0 : Word)) **
      (memIs sp raVal) ** (memIs (sp + 8) cursor))
    (by pcf_validate_cps) hldE
  have hbr' := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x1 callRa) ** (regIs .x11 (0 : Word)) **
      (memIs sp raVal) ** (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr))
    (by pcf_validate_cps) hbrE
  have hmid := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hld' hbr'
  have htail := validate_failure_tail_cps sp callRa cursor (0 : Word)
    endPtr raVal endPtr
  have hmid0 := cpsTripleWithin_frameR (regIs .x0 (0 : Word)) (by pcf_validate_cps) hmid
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hmid0 htail
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp) hseq)

/-! ## Fuel-indexed mutual trace

`ValidateTrace` is the induction bridge between the semantic fuel witness and
the machine edge above.  The item constructor records both the dependent
continuation family returned by `validate_success_continuation` and the
machine loop continuation for the exact advanced cursor.  Its recursive tail
is strictly smaller because it is indexed by `endOff - next`. -/

def ValidateLoopContinuation
    (bytes : List (BitVec 8)) (base : Word) (floor cursorOff endOff fuel : Nat) : Prop :=
  ∀ (sp callRa cursorPtr endPtr : Word),
    ¬ BitVec.ult endPtr cursorPtr →
    cpsTripleWithin 4 (validateEntry + 44) (validateEntry + 16) validateCR
      ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 callRa) **
       (regIs .x5 (0 : Word)) ** (regIs .x11 (0 : Word)) **
       (memIs sp callRa) ** (memIs (sp + 8) cursorPtr) **
       (memIs (sp + 16) endPtr) **
       ⌜ValidateK bytes base floor cursorPtr endPtr cursorOff endOff fuel⌝)
      ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 callRa) **
       (regIs .x5 endPtr) ** (regIs .x11 (0 : Word)) **
       (memIs sp callRa) ** (memIs (sp + 8) cursorPtr) **
       (memIs (sp + 16) endPtr) **
       ⌜ValidateK bytes base floor cursorPtr endPtr cursorOff endOff fuel⌝)

inductive ValidateTrace (bytes : List (BitVec 8)) (base : Word) (floor : Nat) :
    Nat → Nat → Nat → Prop where
  | empty {cursor endOff}
      (heq : cursor = endOff)
      (hend : endOff ≤ bytes.length) :
      ValidateTrace bytes base floor (endOff - cursor) cursor endOff
  | item {cursor next endOff : Nat} {len : Word}
      (hcursor : cursor < next)
      (hend : next ≤ endOff)
      (hwindow : endOff ≤ bytes.length)
      (hitem : rlpItemDecodeStrictW bytes base cursor next endOff len (floor + 1))
      (hdecode : ∃ item,
        decodeAux (floor + 1) (bytes.drop cursor) =
          some (item, bytes.drop next))
      (hcontinuation : ∃ len' item',
        rlpItemDecodeStrictW bytes base cursor next endOff len' (floor + 1) ∧
        decodeAux (floor + 1) (bytes.drop cursor) =
          some (item', bytes.drop next) ∧
        ValidateK bytes base floor
          (base + BitVec.ofNat 64 next)
          (base + BitVec.ofNat 64 endOff) next endOff (endOff - next))
      (hrest : ValidateTrace bytes base floor (endOff - next) next endOff)
      (hloop : ValidateLoopContinuation bytes base floor next endOff (endOff - next)) :
      ValidateTrace bytes base floor (endOff - cursor) cursor endOff

theorem payloadFuel_to_validateTrace
    {bytes : List (BitVec 8)} {base : Word} {floor fuel cursor endOff : Nat}
    (hpayload : PayloadStrictFuel bytes base floor fuel cursor endOff)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hnowrap : base.toNat + endOff + 9 < 2 ^ 64) :
    ValidateTrace bytes base floor fuel cursor endOff := by
  induction hpayload with
  | empty heq hend =>
      exact .empty heq hend
  | @item cursor next endOff len hcursor hend hwindow hitem hrest ih =>
      have hcursor_le : cursor ≤ endOff := le_trans (Nat.le_of_lt hcursor) hend
      have hK : ValidateK bytes base floor
          (base + BitVec.ofNat 64 cursor)
          (base + BitVec.ofNat 64 endOff)
        cursor endOff (endOff - cursor) :=
        ⟨rfl, rfl, .item hcursor hend hwindow hitem hrest⟩
      have hnonempty : cursor < endOff := lt_of_lt_of_le hcursor hend
      obtain ⟨item, hdecode⟩ := rlpItemDecodeStrictW_to_decodeAux
        bytes base cursor next endOff floor len hitem hcursor_le hend hwindow hover hnowrap
      have hKnext : ValidateK bytes base floor
          (base + BitVec.ofNat 64 next)
          (base + BitVec.ofNat 64 endOff) next endOff (endOff - next) :=
        ⟨rfl, rfl, hrest⟩
      have hloop : ValidateLoopContinuation bytes base floor next endOff (endOff - next) :=
        fun sp callRa cursorPtr endPtr hcross =>
          validate_nested_zero_loop_cps (bytes := bytes) (base := base) (floor := floor)
            (nextOff := next) (endOff := endOff) (fuel := (endOff - next))
            sp callRa cursorPtr endPtr hcross
      exact ValidateTrace.item hcursor hend hwindow hitem
        ⟨item, hdecode⟩ ⟨len, item, hitem, hdecode, hKnext⟩ (ih hnowrap) hloop

/-! ## Branch-local CPS family

`ValidateTrace` is now consumed by a machine-facing family rather than being
left as a semantic witness.  The family is intentionally local to this
module: it packages the dependent cursor relation that the four-instruction
zero-status edge preserves, while the eventual whole-routine theorem can
instantiate the recursive nested-call continuation without changing the
shared CPS API.  A fixed `cpsTripleWithin` assertion cannot quantify over the
trace constructor's advanced cursor; this family keeps that index explicit.
-/

def ValidateTraceCpsFamily
    (bytes : List (BitVec 8)) (base : Word) (floor : Nat)
    (fuel cursor endOff : Nat) : Prop :=
    ∃ next : Nat, ∀ (sp callRa cursorPtr endPtr : Word),
      ¬ BitVec.ult endPtr cursorPtr →
      cpsTripleWithin 4 (validateEntry + 44) (validateEntry + 16) validateCR
        ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 callRa) **
         (regIs .x5 (0 : Word)) ** (regIs .x11 (0 : Word)) **
         (memIs sp callRa) ** (memIs (sp + 8) cursorPtr) **
         (memIs (sp + 16) endPtr) **
         ⌜ValidateK bytes base floor cursorPtr endPtr next endOff (endOff - next)⌝ **
         ⌜ValidateTrace bytes base floor fuel cursor endOff⌝)
        ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 callRa) **
         (regIs .x5 endPtr) ** (regIs .x11 (0 : Word)) **
         (memIs sp callRa) ** (memIs (sp + 8) cursorPtr) **
         (memIs (sp + 16) endPtr) **
         ⌜ValidateK bytes base floor cursorPtr endPtr next endOff (endOff - next)⌝ **
         ⌜ValidateTrace bytes base floor fuel cursor endOff⌝)

theorem validateTrace_item_loop_cps
    {bytes : List (BitVec 8)} {base : Word} {floor fuel cursor endOff : Nat}
    (htrace : ValidateTrace bytes base floor fuel cursor endOff)
    (hnonempty : cursor < endOff) :
    ValidateTraceCpsFamily bytes base floor fuel cursor endOff := by
  have htrace' := htrace
  cases htrace' with
  | empty heq hend => omega
  | @item cursor next endOff len hcursor hend hwindow hitem hdecode
      hcontinuation hrest hloop =>
      refine ⟨next, ?_⟩
      intro sp callRa cursorPtr endPtr hcross
      have hloop' := hloop sp callRa cursorPtr endPtr hcross
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hp => by xperm_hyp hp)
        (cpsTripleWithin_frameR (⌜ValidateTrace bytes base floor
          (endOff - cursor) cursor endOff⌝)
          (by pcf_validate_cps) hloop')

theorem payloadFuel_to_validateTraceCpsFamily
    {bytes : List (BitVec 8)} {base : Word} {floor fuel cursor endOff : Nat}
    (hpayload : PayloadStrictFuel bytes base floor fuel cursor endOff)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hnowrap : base.toNat + endOff + 9 < 2 ^ 64)
    (hnonempty : cursor < endOff) :
    ValidateTraceCpsFamily bytes base floor fuel cursor endOff := by
  have htrace := payloadFuel_to_validateTrace hpayload hover hnowrap
  exact validateTrace_item_loop_cps htrace hnonempty

/-! ## Local dependent-post bind

The shared CPS combinators compose fixed assertions.  The nested LIST call has
one additional shape: its successful return chooses the advanced cursor and
length, and the loop continuation is indexed by that choice.  Keep this bind
local to the RLP proof rather than widening the shared API: the code
requirements and exit PC remain fixed, while only the post assertion is
dependent. -/

def cpsDepPost {α : Type} (post : α → Assertion) : Assertion :=
  fun h => ∃ a, post a h

theorem cpsTripleWithin_seq_dep_post
    {α : Type} {nSteps1 nSteps2 : Nat} {entry mid exit_ : Word}
    {cr1 cr2 : CodeReq} {P R : Assertion} {post : α → Assertion}
    (hd : cr1.Disjoint cr2)
    (h1 : cpsTripleWithin nSteps1 entry mid cr1 P (cpsDepPost post))
    (h2 : ∀ a, cpsTripleWithin nSteps2 mid exit_ cr2 (post a) R) :
    cpsTripleWithin (nSteps1 + nSteps2) entry exit_ (cr1.union cr2) P R := by
  intro Frame hFrame s hcr hP hpc
  rw [CodeReq.union_satisfiedBy hd] at hcr
  obtain ⟨hcr1, hcr2⟩ := hcr
  obtain ⟨k1, hk1, s1, hstep1, hpc1, hQR⟩ :=
    h1 Frame hFrame s hcr1 hP hpc
  have hcr2' := CodeReq.SatisfiedBy_preserved hstep1 hcr2
  obtain ⟨hWhole, hCompat, hQ, hFrame', hdisj, hunion, hpost, hR⟩ := hQR
  obtain ⟨a, hpost_a⟩ := hpost
  have hpostFrame : (post a ** Frame).holdsFor s1 :=
    ⟨hWhole, hCompat, hQ, hFrame', hdisj, hunion, hpost_a, hR⟩
  obtain ⟨k2, hk2, s2, hstep2, hpc2, hR2⟩ :=
    h2 a Frame hFrame s1 hcr2' hpostFrame hpc1
  exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2,
    stepN_add_eq hstep1 hstep2, hpc2, hR2⟩

/-! The concrete nested-call boundary is `V+36 → V+40`: the payload's JAL
enters `rlp_walk_next_nested`, and the continuation starts at the instruction
after that call.  This specialization keeps the call code and the
continuation code separate (with one static disjointness proof), while the
success value remains fully indexed by `post`. -/

theorem validate_nested_success_path_dep_bind
    {α : Type} {nCall nCont : Nat} {callCode contCode : CodeReq}
    {P R : Assertion} {post : α → Assertion} (exit_ : Word)
    (hd : callCode.Disjoint contCode)
    (hcall : cpsTripleWithin nCall (validateEntry + 36) (validateEntry + 40)
      callCode P (cpsDepPost post))
    (hcont : ∀ a, cpsTripleWithin nCont (validateEntry + 40) exit_ contCode
      (post a) R) :
    cpsTripleWithin (nCall + nCont) (validateEntry + 36) exit_ (callCode.union contCode)
      P R :=
  cpsTripleWithin_seq_dep_post hd hcall hcont

theorem validate_nested_jal_success_dep_bind
    {nCall nCont : Nat} {calleeEntry : Word} {calleeCode contCode : CodeReq}
    {α : Type} {P R : Assertion} {post : α → Assertion}
    (oldRa : Word) (offset : BitVec 21) (exit_ : Word)
    (hoffset : (validateEntry + 36) + signExtend21 offset = calleeEntry)
    (halign : ((validateEntry + 40) &&& ~~~(1 : Word)) = validateEntry + 40)
    (hP : P.pcFree)
    (hcallCode : (CodeReq.singleton (validateEntry + 36) (.JAL .x1 offset)).Disjoint calleeCode)
    (hcallee : cpsTripleWithin nCall calleeEntry (validateEntry + 40) calleeCode
      ((regIs .x1 (validateEntry + 40)) ** P) (cpsDepPost post))
    (hdisj : (CodeReq.singleton (validateEntry + 36) (.JAL .x1 offset)).union calleeCode |>.Disjoint contCode)
    (hcont : ∀ a, cpsTripleWithin nCont (validateEntry + 40) exit_ contCode (post a) R) :
    cpsTripleWithin (1 + nCall + nCont) (validateEntry + 36) exit_
      ((CodeReq.singleton (validateEntry + 36) (.JAL .x1 offset)).union calleeCode |>.union contCode)
      ((regIs .x1 oldRa) ** P) R := by
  have hcall' := WP.cpsCallWithin (vOld := oldRa) offset hoffset halign hP hcallCode hcallee
  exact cpsTripleWithin_seq_dep_post hdisj hcall' hcont

theorem validate_nested_alias_dep_hcallee
    {nShared : Nat} {α : Type} {P : Assertion} {post : α → Assertion}
    (hP : P.pcFree)
    (hdisj : (CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
      (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
        (GuestAddrs.rlp_walk_next_nested + 0)))).Disjoint
      RlpWalkNextStrictTie.sharedCode)
    (hshared : cpsTripleWithin nShared (GuestAddrs.rlp_walk_next_shared : Word)
      (validateEntry + 40) RlpWalkNextStrictTie.sharedCode
      ((regIs .x1 (validateEntry + 40)) ** P) (cpsDepPost post)) :
    cpsTripleWithin (1 + nShared) (GuestAddrs.rlp_walk_next_nested : Word)
      (validateEntry + 40)
      ((CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
        (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
          (GuestAddrs.rlp_walk_next_nested + 0)))).union
        RlpWalkNextStrictTie.sharedCode)
      ((regIs .x1 (validateEntry + 40)) ** P) (cpsDepPost post) := by
  have hj := jal_x0_spec_gen_within
    (jalOff GuestAddrs.rlp_walk_next_shared
      (GuestAddrs.rlp_walk_next_nested + 0))
    (GuestAddrs.rlp_walk_next_nested : Word)
  rw [show (GuestAddrs.rlp_walk_next_nested : Word) +
      signExtend21 (jalOff GuestAddrs.rlp_walk_next_shared
        (GuestAddrs.rlp_walk_next_nested + 0)) =
      (GuestAddrs.rlp_walk_next_shared : Word) from by decide] at hj
  have hj' := cpsTripleWithin_frameR
    ((regIs .x1 (validateEntry + 40)) ** P)
    (by apply pcFree_sepConj <;> first | exact pcFree_regIs | exact hP) hj
  have hj'' := cpsTripleWithin_weaken
    (fun h hp => (sepConj_emp_left h).mpr hp)
    (fun h hp => (sepConj_emp_left h).mp hp) hj'
  exact cpsTripleWithin_seq hdisj hj'' hshared

/-! First list-parser edge in the shared callee: after the list-prefix class,
`BLTU x6,248` selects the short-list payload-start arm at `S+148` or the
long-list length decoder at `S+88`. -/

theorem shared_list_length_prefix_branch (pfx : Word) :
    cpsBranchWithin 1 (RlpWalkNextStrictTie.S + 84)
      RlpWalkNextStrictTie.sharedCode
      ((regIs .x6 pfx) ** (regIs .x7 (248 : Word)))
      (RlpWalkNextStrictTie.S + 148)
        ((regIs .x6 pfx) ** (regIs .x7 (248 : Word)) ** pure (BitVec.ult pfx (248 : Word)))
      (RlpWalkNextStrictTie.S + 88)
        ((regIs .x6 pfx) ** (regIs .x7 (248 : Word)) ** pure (¬ BitVec.ult pfx (248 : Word))) := by
  have h := bltu_spec_gen_within .x6 .x7 (64 : BitVec 13) pfx (248 : Word)
    (RlpWalkNextStrictTie.S + 84)
  rw [show (RlpWalkNextStrictTie.S + 84) + signExtend13 (64 : BitVec 13) =
      RlpWalkNextStrictTie.S + 148 from by
        rw [show signExtend13 (64 : BitVec 13) = (64 : Word) from by decide]
        bv_omega,
      show RlpWalkNextStrictTie.S + 84 + 4 = RlpWalkNextStrictTie.S + 88 by bv_omega] at h
  exact cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 21 (RlpWalkNextStrictTie.S + 84)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))) h

theorem shared_list_depth_branch (depth : Word) :
    cpsBranchWithin 1 (RlpWalkNextStrictTie.S + 68)
      RlpWalkNextStrictTie.sharedCode
      ((regIs .x9 depth) ** (regIs .x7 (1024 : Word)))
      (RlpWalkNextStrictTie.S + 168)
        ((regIs .x9 depth) ** (regIs .x7 (1024 : Word)) ** pure (¬ BitVec.ult depth (1024 : Word)))
      (RlpWalkNextStrictTie.S + 72)
        ((regIs .x9 depth) ** (regIs .x7 (1024 : Word)) ** pure (BitVec.ult depth (1024 : Word))) := by
  have h := bgeu_spec_gen_within .x9 .x7 (100 : BitVec 13) depth (1024 : Word)
    (RlpWalkNextStrictTie.S + 68)
  rw [show (RlpWalkNextStrictTie.S + 68) + signExtend13 (100 : BitVec 13) =
      RlpWalkNextStrictTie.S + 168 from by
        rw [show signExtend13 (100 : BitVec 13) = (100 : Word) from by decide]
        bv_omega,
      show RlpWalkNextStrictTie.S + 68 + 4 = RlpWalkNextStrictTie.S + 72 by bv_omega] at h
  exact cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 17 (RlpWalkNextStrictTie.S + 68)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))) h

theorem shared_list_depth_increment (depth : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 72)
      (RlpWalkNextStrictTie.S + 76) RlpWalkNextStrictTie.sharedCode
      ((regIs .x9 depth) ** (regIs .x7 (1024 : Word)))
      ((regIs .x9 (depth + 1)) ** (regIs .x7 (1024 : Word))) := by
  have h := addi_spec_gen_same_within .x9 depth (1 : BitVec 12)
    (RlpWalkNextStrictTie.S + 72) (by decide)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    show RlpWalkNextStrictTie.S + 72 + 4 = RlpWalkNextStrictTie.S + 76 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 72)
      (.ADDI .x9 .x9 (1 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 18 (RlpWalkNextStrictTie.S + 72)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  have hframe := cpsTripleWithin_frameR (regIs .x7 (1024 : Word))
    (by exact pcFree_regIs) hcode
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hframe

theorem shared_list_length_limit (endPtr : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 80)
      (RlpWalkNextStrictTie.S + 84) RlpWalkNextStrictTie.sharedCode
      ((regIs .x7 (1024 : Word)) ** (regIs .x11 endPtr))
      ((regIs .x7 (248 : Word)) ** (regIs .x11 endPtr)) := by
  have h := li_spec_gen_within .x7 (1024 : Word) (248 : Word)
    (RlpWalkNextStrictTie.S + 80) (by decide)
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 80)
      (.LI .x7 (248 : Word)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 20 (RlpWalkNextStrictTie.S + 80)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  have hframe := cpsTripleWithin_frameR (regIs .x11 endPtr)
    (by exact pcFree_regIs) hcode
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hframe

theorem shared_long_prefix_branch (remaining : Word) :
    cpsBranchWithin 1 (RlpWalkNextStrictTie.S + 108)
      RlpWalkNextStrictTie.sharedCode
      ((regIs .x28 remaining) ** (regIs .x0 (0 : Word)))
      (RlpWalkNextStrictTie.S + 136)
        ((regIs .x28 remaining) ** (regIs .x0 (0 : Word)) ** pure (remaining = 0))
      (RlpWalkNextStrictTie.S + 112)
        ((regIs .x28 remaining) ** (regIs .x0 (0 : Word)) ** pure (remaining ≠ 0)) := by
  have h := beq_spec_gen_within .x28 .x0 (28 : BitVec 13) remaining (0 : Word)
    (RlpWalkNextStrictTie.S + 108)
  rw [show (RlpWalkNextStrictTie.S + 108) + signExtend13 (28 : BitVec 13) =
      RlpWalkNextStrictTie.S + 136 from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]
        bv_omega,
      show RlpWalkNextStrictTie.S + 108 + 4 = RlpWalkNextStrictTie.S + 112 by bv_omega] at h
  exact cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 27 (RlpWalkNextStrictTie.S + 108)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))) h

theorem shared_validate_result_branch (status : Word) :
    cpsBranchWithin 1 (RlpWalkNextStrictTie.S + 164)
      RlpWalkNextStrictTie.sharedCode
      ((regIs .x10 status) ** (regIs .x0 (0 : Word)))
      (RlpWalkNextStrictTie.S + 184)
        ((regIs .x10 status) ** (regIs .x0 (0 : Word)) ** pure (status = 0))
      (RlpWalkNextStrictTie.S + 168)
        ((regIs .x10 status) ** (regIs .x0 (0 : Word)) ** pure (status ≠ 0)) := by
  have h := beq_spec_gen_within .x10 .x0 (20 : BitVec 13) status (0 : Word)
    (RlpWalkNextStrictTie.S + 164)
  rw [show (RlpWalkNextStrictTie.S + 164) + signExtend13 (20 : BitVec 13) =
      RlpWalkNextStrictTie.S + 184 from by
        rw [show signExtend13 (20 : BitVec 13) = (20 : Word) from by decide]
        bv_omega,
      show RlpWalkNextStrictTie.S + 164 + 4 = RlpWalkNextStrictTie.S + 168 by bv_omega] at h
  exact cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 41 (RlpWalkNextStrictTie.S + 164)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))) h

theorem shared_long_prefix_decrement (remaining cursor : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 128)
      (RlpWalkNextStrictTie.S + 132) RlpWalkNextStrictTie.sharedCode
      ((regIs .x28 remaining) ** (regIs .x29 cursor))
      ((regIs .x28 (remaining - 1)) ** (regIs .x29 cursor)) := by
  have h := addi_spec_gen_same_within .x28 remaining (-1 : BitVec 12)
    (RlpWalkNextStrictTie.S + 128) (by decide)
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide,
    show remaining + (-1 : Word) = remaining - 1 by bv_omega,
    show RlpWalkNextStrictTie.S + 128 + 4 = RlpWalkNextStrictTie.S + 132 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 128)
      (.ADDI .x28 .x28 (-1 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 32 (RlpWalkNextStrictTie.S + 128)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  have hframe := cpsTripleWithin_frameR (regIs .x29 cursor)
    (by exact pcFree_regIs) hcode
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hframe

theorem shared_long_prefix_cursor_increment (cursor remaining : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 124)
      (RlpWalkNextStrictTie.S + 128) RlpWalkNextStrictTie.sharedCode
      ((regIs .x29 cursor) ** (regIs .x28 remaining))
      ((regIs .x29 (cursor + 1)) ** (regIs .x28 remaining)) := by
  have h := addi_spec_gen_same_within .x29 cursor (1 : BitVec 12)
    (RlpWalkNextStrictTie.S + 124) (by decide)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    show RlpWalkNextStrictTie.S + 124 + 4 = RlpWalkNextStrictTie.S + 128 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 124)
      (.ADDI .x29 .x29 (1 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 31 (RlpWalkNextStrictTie.S + 124)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  have hframe := cpsTripleWithin_frameR (regIs .x28 remaining)
    (by exact pcFree_regIs) hcode
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hframe

theorem shared_long_prefix_loop_backedge (cursor remaining : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 132)
      (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
      ((regIs .x0 (0 : Word)) ** (regIs .x29 cursor) ** (regIs .x28 remaining))
      ((regIs .x0 (0 : Word)) ** (regIs .x29 cursor) ** (regIs .x28 remaining)) := by
  have h := jal_x0_spec_gen_within (-24 : BitVec 21)
    (RlpWalkNextStrictTie.S + 132)
  rw [show (RlpWalkNextStrictTie.S + 132) +
      signExtend21 (-24 : BitVec 21) = RlpWalkNextStrictTie.S + 108 from by
        rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]
        bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 132)
      (.JAL .x0 (-24 : BitVec 21)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 33 (RlpWalkNextStrictTie.S + 132)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  have hframe := cpsTripleWithin_frameR
    ((regIs .x0 (0 : Word)) ** (regIs .x29 cursor) ** (regIs .x28 remaining))
    (by apply pcFree_sepConj <;> first | exact pcFree_regIs | apply pcFree_sepConj <;> exact pcFree_regIs)
    hcode
  have hframe' := cpsTripleWithin_weaken
    (fun h hp => (sepConj_emp_left h).mpr hp)
    (fun h hp => (sepConj_emp_left h).mp hp) hframe
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hframe'

end EvmAsm.Codegen.RlpWalkNextStrictFuel
