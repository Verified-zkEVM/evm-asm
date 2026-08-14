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
import EvmAsm.Rv64.RLP.WalkItemDeterminism
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.Tactics.XPermPure
import EvmAsm.Rv64.Tactics.DropPure

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

/-! A shared-post success uses pointer differences, while a trace uses Nat
    offsets.  This local bridge keeps that normalization at the consumer: the
    pointer difference is a reversible `BitVec` subtraction, and deterministic
    item decoding identifies it with the trace's concrete cursor. -/
theorem strictW_pointer_output_matches_index
    {bytes : List (BitVec 8)} {base : Word} {floor cursor next endOff : Nat}
    {a0 endPtr a2 len : Word}
    (hnext : next ≤ endOff) (hend : endOff ≤ bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hendPtr : endPtr = base + BitVec.ofNat 64 endOff)
    (hptr : rlpItemDecodeStrictW bytes base cursor
      (a0 - base).toNat (endPtr - base).toNat a2 floor)
    (htrace : rlpItemDecodeStrictW bytes base cursor next endOff len floor) :
    (a0 - base).toNat = next ∧
      base + BitVec.ofNat 64 ((a0 - base).toNat) = a0 ∧
      (endPtr - base).toNat = endOff ∧ a2 = len := by
  have hendOff : (endPtr - base).toNat = endOff := by
    rw [hendPtr]
    exact sub_base_of_base_add hend hover
  rw [hendOff] at hptr
  obtain ⟨hnextPtr, hlen⟩ := rlpItemDecode_deterministic hptr.1 htrace.1
  have hq : (a0 - base).toNat = next := by
    have hsub := congrArg (fun p : Word => p - base) hnextPtr
    have hqWord : BitVec.ofNat 64 (a0 - base).toNat =
        BitVec.ofNat 64 next := by
      simpa [BitVec.add_comm, BitVec.add_sub_cancel] using hsub
    have hqLt : (a0 - base).toNat < 2 ^ 64 := (a0 - base).isLt
    have hnextLt : next < 2 ^ 64 := by omega
    have hqNat := congrArg BitVec.toNat hqWord
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hqLt, Nat.mod_eq_of_lt hnextLt] at hqNat
    exact hqNat
  have hround : base + BitVec.ofNat 64 ((a0 - base).toNat) = a0 := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  exact ⟨hq, hround, hendOff, hlen⟩

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
    (sp callRa cursorPtr frameCursor endPtr x5Old : Word)
    (hcursor : ¬ BitVec.ult endPtr cursorPtr) :
    cpsTripleWithin 4 (validateEntry + 44) (validateEntry + 16) validateCR
      ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 callRa) **
       (regIs .x5 x5Old) ** (regIs .x11 (0 : Word)) **
       (memIs sp callRa) ** (memIs (sp + 8) frameCursor) **
       (memIs (sp + 16) endPtr) **
       ⌜ValidateK bytes base floor cursorPtr endPtr nextOff endOff fuel⌝)
      ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 callRa) **
       (regIs .x5 endPtr) ** (regIs .x11 (0 : Word)) **
       (memIs sp callRa) ** (memIs (sp + 8) cursorPtr) **
       (memIs (sp + 16) endPtr) **
       ⌜ValidateK bytes base floor cursorPtr endPtr nextOff endOff fuel⌝) := by
  have hld := ld_spec_gen_within .x5 .x2 sp x5Old endPtr
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
  have hsd := sd_spec_gen_within .x2 .x10 sp cursorPtr frameCursor
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
      (memIs (sp + 8) frameCursor) **
      ⌜ValidateK bytes base floor cursorPtr endPtr nextOff endOff fuel⌝)
    (by pcf_validate_cps) hldE
  have hbr'' := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x1 callRa) **
      (regIs .x11 (0 : Word)) ** (memIs sp callRa) **
      (memIs (sp + 8) frameCursor) ** (memIs (sp + 16) endPtr) **
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
    (bytes : List (BitVec 8)) (base : Word) (floor nextOff endOff fuel : Nat) : Prop :=
  ∀ (sp callRa cursorPtr frameCursorPtr endPtr : Word),
    ¬ BitVec.ult endPtr cursorPtr →
    cpsTripleWithin 4 (validateEntry + 44) (validateEntry + 16) validateCR
      ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 callRa) **
       regOwn .x5 ** (regIs .x11 (0 : Word)) **
       (memIs sp callRa) ** (memIs (sp + 8) frameCursorPtr) **
       (memIs (sp + 16) endPtr) **
       ⌜ValidateK bytes base floor cursorPtr endPtr nextOff endOff fuel⌝)
      ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 callRa) **
       (regIs .x5 endPtr) ** (regIs .x11 (0 : Word)) **
       (memIs sp callRa) ** (memIs (sp + 8) cursorPtr) **
       (memIs (sp + 16) endPtr) **
         ⌜ValidateK bytes base floor cursorPtr endPtr nextOff endOff fuel⌝)

/-! The normalized output is now consumable by the trace's concrete loop
    continuation.  This is the first nonempty-cycle composition point: the
    shared result is pointer-indexed, while `ValidateLoopContinuation` is
    indexed by the trace's Nat `next`/`endOff`. -/
theorem validateTrace_item_zero_loop_indexed
    {bytes : List (BitVec 8)} {base : Word} {floor cursor next endOff : Nat}
    {a0 endPtr a2 : Word}
    (hend : next ≤ endOff)
    (hwindow : endOff ≤ bytes.length)
    (hitem : rlpItemDecodeStrictW bytes base cursor next endOff a2 (floor + 1))
    (hKnext : ValidateK bytes base floor
      (base + BitVec.ofNat 64 next)
      (base + BitVec.ofNat 64 endOff) next endOff (endOff - next))
    (hloop : ValidateLoopContinuation bytes base floor next endOff (endOff - next))
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hendPtr : endPtr = base + BitVec.ofNat 64 endOff)
    (hptr : rlpItemDecodeStrictW bytes base cursor
      (a0 - base).toNat (endPtr - base).toNat a2 (floor + 1)) :
    ∀ (sp callRa frameCursorPtr : Word),
      cpsTripleWithin 4 (validateEntry + 44) (validateEntry + 16) validateCR
        ((regIs .x2 sp) ** (regIs .x10 a0) ** (regIs .x1 callRa) **
         regOwn .x5 ** (regIs .x11 (0 : Word)) **
         (memIs sp callRa) ** (memIs (sp + 8) frameCursorPtr) **
         (memIs (sp + 16) endPtr) **
         ⌜ValidateK bytes base floor a0 endPtr next endOff (endOff - next)⌝)
        ((regIs .x2 sp) ** (regIs .x10 a0) ** (regIs .x1 callRa) **
         (regIs .x5 endPtr) ** (regIs .x11 (0 : Word)) **
         (memIs sp callRa) ** (memIs (sp + 8) a0) **
         (memIs (sp + 16) endPtr) **
         ⌜ValidateK bytes base floor a0 endPtr next endOff (endOff - next)⌝) := by
  intro sp callRa frameCursorPtr
  obtain ⟨hq, hround, hendOff, hlen⟩ :=
    strictW_pointer_output_matches_index hend hwindow hover hendPtr hptr hitem
  have ha0 : base + BitVec.ofNat 64 next = a0 := by
    simpa [hq] using hround
  have hcross : ¬ BitVec.ult endPtr a0 := by
    rw [hendPtr, ← ha0]
    rw [ult_base_add_ofNat (base := base) (i := endOff) (j := next)
      hwindow (le_trans hend hwindow) hover]
    omega
  have hK : ValidateK bytes base floor a0 endPtr next endOff (endOff - next) := by
    rw [← ha0, hendPtr]
    exact hKnext
  simpa [hK] using hloop sp callRa a0 frameCursorPtr endPtr hcross

/-! The nonempty mutual step is the status-zero edge followed by the
    normalized cursor loop.  Keeping the status guard explicit here prevents
    the nonzero failure tail from being hidden in a broad postcondition. -/
theorem validate_nested_success_zero_loop_indexed
    {bytes : List (BitVec 8)} {base : Word} {floor cursor next endOff : Nat}
    {a0 endPtr a2 status : Word}
    (hend : next ≤ endOff)
    (hwindow : endOff ≤ bytes.length)
    (hitem : rlpItemDecodeStrictW bytes base cursor next endOff a2 (floor + 1))
    (hKnext : ValidateK bytes base floor
      (base + BitVec.ofNat 64 next)
      (base + BitVec.ofNat 64 endOff) next endOff (endOff - next))
    (hloop : ValidateLoopContinuation bytes base floor next endOff (endOff - next))
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hendPtr : endPtr = base + BitVec.ofNat 64 endOff)
    (hptr : rlpItemDecodeStrictW bytes base cursor
      (a0 - base).toNat (endPtr - base).toNat a2 (floor + 1))
    (hstatus : status = 0)
    (sp callRa frameCursorPtr : Word) :
    cpsTripleWithin 5 (validateEntry + 40) (validateEntry + 16) validateCR
      ((regIs .x2 sp) ** (regIs .x10 a0) ** (regIs .x11 status) **
       (regIs .x0 (0 : Word)) ** (regIs .x1 callRa) ** regOwn .x5 **
       (memIs sp callRa) ** (memIs (sp + 8) frameCursorPtr) **
       (memIs (sp + 16) endPtr) **
       ⌜ValidateK bytes base floor a0 endPtr next endOff (endOff - next)⌝)
      ((regIs .x2 sp) ** (regIs .x10 a0) ** (regIs .x11 (0 : Word)) **
       (regIs .x0 (0 : Word)) ** (regIs .x1 callRa) ** (regIs .x5 endPtr) **
       (memIs sp callRa) ** (memIs (sp + 8) a0) **
       (memIs (sp + 16) endPtr) **
       ⌜ValidateK bytes base floor a0 endPtr next endOff (endOff - next)⌝) := by
  subst status
  have hbr := validate_nested_status_branch_cps (0 : Word)
  have hbr' := cpsBranchWithin_ntakenPath hbr (by
    intro hp hq
    have hleft := (sepConj_assoc hp).mpr hq
    obtain ⟨_, _, _, _, _, hpure⟩ := hleft
    exact by simpa using hpure.2)
  have hbr0 := cpsTripleWithin_weaken (fun _ hp => hp)
    sepConj_strip_pure_end2 hbr'
  have hzero := validateTrace_item_zero_loop_indexed
    (bytes := bytes) (base := base) (floor := floor) (cursor := cursor)
    (next := next) (endOff := endOff) (a0 := a0) (endPtr := endPtr)
    (a2 := a2) hend hwindow hitem hKnext hloop hover hendPtr hptr
    sp callRa frameCursorPtr
  have hzero' := cpsTripleWithin_frameR (regIs .x0 (0 : Word))
    (by pcf_validate_cps) hzero
  have hbrFull := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x10 a0) ** (regIs .x1 callRa) **
      regOwn .x5 ** (memIs sp callRa) **
      (memIs (sp + 8) frameCursorPtr) ** (memIs (sp + 16) endPtr) **
      ⌜ValidateK bytes base floor a0 endPtr next endOff (endOff - next)⌝)
    (by pcf_validate_cps) hbr0
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hbrFull hzero'
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp) hseq)

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
        fun sp callRa cursorPtr frameCursorPtr endPtr hcross => by
          have hown : cpsTripleWithin 4 (validateEntry + 44) (validateEntry + 16)
              validateCR
              (((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 callRa) **
                (regIs .x11 (0 : Word)) ** (memIs sp callRa) **
                (memIs (sp + 8) frameCursorPtr) ** (memIs (sp + 16) endPtr) **
                ⌜ValidateK bytes base floor cursorPtr endPtr next endOff (endOff - next)⌝) **
               regOwn .x5)
              ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 callRa) **
               (regIs .x5 endPtr) ** (regIs .x11 (0 : Word)) **
               (memIs sp callRa) ** (memIs (sp + 8) cursorPtr) **
               (memIs (sp + 16) endPtr) **
               ⌜ValidateK bytes base floor cursorPtr endPtr next endOff (endOff - next)⌝) := by
            apply cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
            intro x5Old
            exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
              (fun _ hp => by xperm_hyp hp)
              (validate_nested_zero_loop_cps (bytes := bytes) (base := base)
                (floor := floor) (nextOff := next) (endOff := endOff)
                (fuel := (endOff - next)) sp callRa cursorPtr frameCursorPtr endPtr x5Old hcross)
          exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
            (fun _ hp => by xperm_hyp hp) hown
      exact ValidateTrace.item hcursor hend hwindow hitem
        ⟨item, hdecode⟩ ⟨len, item, hitem, hdecode, hKnext⟩ (ih hnowrap) hloop

/-! ## Strict LIST result bridge

`ValidateTrace` is the machine-facing witness for a successful payload walk.
The validator's result must also be consumable by the EL list decoder: every
strict child contributes one `decodeAux` link, and the links compose to one
`decodeItems` result with no leftover bytes.  This is the missing bridge between
the CPS trace and the outer `decodeAux` list arm; it is deliberately pure and
does not change the CPS API or introduce another fuel convention. -/

theorem validateTrace_to_decodeChainFrom
    {bytes : List (BitVec 8)} {base : Word} {floor fuel cursor endOff : Nat}
    (htrace : ValidateTrace bytes base floor fuel cursor endOff) :
    ∃ items : List RLPItem,
      DecodeChainFrom bytes (floor + 1) cursor items endOff := by
  induction htrace with
  | empty heq hend =>
      exact ⟨[], heq⟩
  | @item cursor next endOff len hcursor hend hwindow hitem hdecode
      hcontinuation hrest hloop ih =>
      obtain ⟨item, hitem⟩ := hdecode
      obtain ⟨items, hitems⟩ := ih
      exact ⟨item :: items, next, hitem, hitems⟩

theorem validateTrace_to_decodeItems
    {bytes : List (BitVec 8)} {base : Word} {floor fuel cursor endOff : Nat}
    (htrace : ValidateTrace bytes base floor fuel cursor endOff)
    (hend : bytes.drop endOff = []) :
    ∃ items : List RLPItem,
      decodeItems (floor + items.length + 1) (bytes.drop cursor) =
        some (items, []) := by
  obtain ⟨items, hchain⟩ := validateTrace_to_decodeChainFrom htrace
  refine ⟨items, ?_⟩
  exact decodeItems_of_chainFrom bytes (floor + 1) items cursor endOff
    hchain hend floor (by omega)

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
    ∃ next : Nat, ∀ (sp callRa cursorPtr frameCursorPtr endPtr : Word),
      ¬ BitVec.ult endPtr cursorPtr →
      cpsTripleWithin 4 (validateEntry + 44) (validateEntry + 16) validateCR
        ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 callRa) **
         regOwn .x5 ** (regIs .x11 (0 : Word)) **
         (memIs sp callRa) ** (memIs (sp + 8) frameCursorPtr) **
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
      intro sp callRa cursorPtr frameCursorPtr endPtr hcross
      have hloop' := hloop sp callRa cursorPtr frameCursorPtr endPtr hcross
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

/-! A validator return is indexed by the cursor and item length it chose.
The status-zero branch carries the complete machine-level witness; a
nonzero status deliberately carries no fabricated cursor/length fact. -/
structure ValidateResult where
  next : Nat
  cursor : Word
  status : Word
  len : Word

def validateResultFacts
    (bytes : List (BitVec 8)) (base : Word) (floor : Nat)
    (cursorOff endOff fuel : Nat) (endPtr : Word)
    (r : ValidateResult) : Prop :=
  (r.status = 0 ∧
    ValidateK bytes base floor r.cursor endPtr r.next endOff fuel ∧
    rlpItemDecodeStrictW bytes base cursorOff
      (r.cursor - base).toNat (endPtr - base).toNat r.len (floor + 1)) ∨
  r.status ≠ 0

def validateResultPost
    (bytes : List (BitVec 8)) (base : Word) (floor : Nat)
    (cursorOff endOff fuel : Nat) (endPtr : Word)
    (r : ValidateResult) : Assertion :=
  ((regIs .x10 r.status) ** (regIs .x11 r.cursor) **
    (regIs .x12 r.len) **
    ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)

/-! The validator's nonzero status arm is intentionally not made symmetric with
the success tail.  It reloads the caller cursor, materialises status 7/length
zero, and jumps directly to `S + 196`; the outer spill slots therefore still
contain the core result.  Keeping that layout explicit prevents a dependent
post from silently claiming that the skipped tail stores ran. -/
theorem shared_validate_status_failure_tail
    (sp raVal cursor outerNext outerStatus outerLen : Word)
    (r : ValidateResult) :
    cpsTripleWithin 7 (RlpWalkNextStrictTie.S + 168)
      (raVal &&& ~~~1) RlpWalkNextStrictTie.sharedCode
      ((regIs .x2 sp) ** (regIs .x10 r.status) ** (regIs .x11 r.cursor) **
       (regIs .x12 r.len) **
       (regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
       (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
       (memIs (sp + 8) cursor) ** (memIs (sp + 24) outerNext) **
       (memIs (sp + 32) outerStatus) ** (memIs (sp + 40) outerLen) **
       ⌜r.status ≠ 0⌝)
      ((regIs .x2 (sp + 64)) ** (regIs .x10 cursor) **
       (regIs .x11 (7 : Word)) ** (regIs .x12 (0 : Word)) **
       (regIs .x1 raVal) ** (regIs .x0 (0 : Word)) **
       (memIs sp raVal) ** (memIs (sp + 8) cursor) **
       (memIs (sp + 24) outerNext) ** (memIs (sp + 32) outerStatus) **
       (memIs (sp + 40) outerLen) ** ⌜r.status ≠ 0⌝) := by
  have h42 := ld_spec_gen_within .x10 .x2 sp r.status cursor
    (8 : BitVec 12) (RlpWalkNextStrictTie.S + 168) (by decide)
  rw [show sp + signExtend12 (8 : BitVec 12) = sp + 8 from by
        rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]] at h42
  rw [show RlpWalkNextStrictTie.S + 168 + 4 = RlpWalkNextStrictTie.S + 172
      from by bv_omega] at h42
  have h43 := li_spec_gen_within .x11 r.cursor (7 : Word)
    (RlpWalkNextStrictTie.S + 172) (by decide)
  rw [show RlpWalkNextStrictTie.S + 172 + 4 = RlpWalkNextStrictTie.S + 176
      from by bv_omega] at h43
  have h44 := li_spec_gen_within .x12 r.len (0 : Word)
    (RlpWalkNextStrictTie.S + 176) (by decide)
  rw [show RlpWalkNextStrictTie.S + 176 + 4 = RlpWalkNextStrictTie.S + 180
      from by bv_omega] at h44
  have h45 := jal_x0_spec_gen_within (16 : BitVec 21)
    (RlpWalkNextStrictTie.S + 180)
  rw [show RlpWalkNextStrictTie.S + 180 + signExtend21 (16 : BitVec 21) =
      RlpWalkNextStrictTie.S + 196 from by
        rw [show signExtend21 (16 : BitVec 21) = (16 : Word) from by decide]
        bv_omega] at h45
  have h49 := ld_spec_gen_within .x1 .x2 sp
    (RlpWalkNextStrictTie.S + 160) raVal (0 : BitVec 12)
    (RlpWalkNextStrictTie.S + 196) (by decide)
  rw [show sp + signExtend12 (0 : BitVec 12) = sp from by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega] at h49
  rw [show RlpWalkNextStrictTie.S + 196 + 4 = RlpWalkNextStrictTie.S + 200
      from by bv_omega] at h49
  have h50 := addi_spec_gen_same_within .x2 sp (64 : BitVec 12)
    (RlpWalkNextStrictTie.S + 200) (by decide)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide] at h50
  rw [show RlpWalkNextStrictTie.S + 200 + 4 = RlpWalkNextStrictTie.S + 204
      from by bv_omega] at h50
  have h51 := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12)
    (RlpWalkNextStrictTie.S + 204)
  rw [show raVal + signExtend12 (0 : BitVec 12) = raVal from by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega] at h51
  have shared_prog_length : rlpWalkNextShared_prog.length = 52 :=
    RlpWalkNextStrictTie.shared_length
  have h42m : ∀ a i,
      CodeReq.singleton (RlpWalkNextStrictTie.S + 168)
        (.LD .x10 .x2 (8 : BitVec 12)) a = some i →
        RlpWalkNextStrictTie.sharedCode a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
        rlpWalkNextShared_prog 42 (RlpWalkNextStrictTie.S + 168)
        (by rw [shared_prog_length]; norm_num)
        (by rw [shared_prog_length]; norm_num) (by bv_omega)
      simpa [rlpWalkNextShared_prog] using hm)
  have h43m : ∀ a i,
      CodeReq.singleton (RlpWalkNextStrictTie.S + 172)
        (.LI .x11 (7 : Word)) a = some i →
        RlpWalkNextStrictTie.sharedCode a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
        rlpWalkNextShared_prog 43 (RlpWalkNextStrictTie.S + 172)
        (by rw [shared_prog_length]; norm_num)
        (by rw [shared_prog_length]; norm_num) (by bv_omega)
      simpa [rlpWalkNextShared_prog] using hm)
  have h44m : ∀ a i,
      CodeReq.singleton (RlpWalkNextStrictTie.S + 176)
        (.LI .x12 (0 : Word)) a = some i →
        RlpWalkNextStrictTie.sharedCode a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
        rlpWalkNextShared_prog 44 (RlpWalkNextStrictTie.S + 176)
        (by rw [shared_prog_length]; norm_num)
        (by rw [shared_prog_length]; norm_num) (by bv_omega)
      simpa [rlpWalkNextShared_prog] using hm)
  have h45m : ∀ a i,
      CodeReq.singleton (RlpWalkNextStrictTie.S + 180)
        (.JAL .x0 (16 : BitVec 21)) a = some i →
        RlpWalkNextStrictTie.sharedCode a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
        rlpWalkNextShared_prog 45 (RlpWalkNextStrictTie.S + 180)
        (by rw [shared_prog_length]; norm_num)
        (by rw [shared_prog_length]; norm_num) (by bv_omega)
      simpa [rlpWalkNextShared_prog] using hm)
  have h49m : ∀ a i,
      CodeReq.singleton (RlpWalkNextStrictTie.S + 196)
        (.LD .x1 .x2 (0 : BitVec 12)) a = some i →
        RlpWalkNextStrictTie.sharedCode a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
        rlpWalkNextShared_prog 49 (RlpWalkNextStrictTie.S + 196)
        (by rw [shared_prog_length]; norm_num)
        (by rw [shared_prog_length]; norm_num) (by bv_omega)
      simpa [rlpWalkNextShared_prog] using hm)
  have h50m : ∀ a i,
      CodeReq.singleton (RlpWalkNextStrictTie.S + 200)
        (.ADDI .x2 .x2 (64 : BitVec 12)) a = some i →
        RlpWalkNextStrictTie.sharedCode a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
        rlpWalkNextShared_prog 50 (RlpWalkNextStrictTie.S + 200)
        (by rw [shared_prog_length]; norm_num)
        (by rw [shared_prog_length]; norm_num) (by bv_omega)
      simpa [rlpWalkNextShared_prog] using hm)
  have h51m : ∀ a i,
      CodeReq.singleton (RlpWalkNextStrictTie.S + 204)
        (.JALR .x0 .x1 (0 : BitVec 12)) a = some i →
        RlpWalkNextStrictTie.sharedCode a = some i :=
    CodeReq.singleton_mono (by
      have hm := CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
        rlpWalkNextShared_prog 51 (RlpWalkNextStrictTie.S + 204)
        (by rw [shared_prog_length]; norm_num)
        (by rw [shared_prog_length]; norm_num) (by bv_omega)
      simpa [rlpWalkNextShared_prog] using hm)
  have h42e := cpsTripleWithin_extend_code h42m
    (cpsTripleWithin_frameR
      ((regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
       (regIs .x11 r.cursor) ** (regIs .x12 r.len) **
       (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
       (memIs (sp + 24) outerNext) ** (memIs (sp + 32) outerStatus) **
       (memIs (sp + 40) outerLen) ** ⌜r.status ≠ 0⌝)
      (by pcf_validate_cps) h42)
  have h43e := cpsTripleWithin_extend_code h43m
    (cpsTripleWithin_frameR
      ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x12 r.len) **
       (regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
       (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
       (memIs (sp + 8) cursor) ** (memIs (sp + 24) outerNext) **
       (memIs (sp + 32) outerStatus) ** (memIs (sp + 40) outerLen) **
       ⌜r.status ≠ 0⌝)
      (by pcf_validate_cps) h43)
  have h44e := cpsTripleWithin_extend_code h44m
    (cpsTripleWithin_frameR
      ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x11 (7 : Word)) **
       (regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
       (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
       (memIs (sp + 8) cursor) ** (memIs (sp + 24) outerNext) **
       (memIs (sp + 32) outerStatus) ** (memIs (sp + 40) outerLen) **
       ⌜r.status ≠ 0⌝)
      (by pcf_validate_cps) h44)
  have h45e := cpsTripleWithin_extend_code h45m
    (cpsTripleWithin_frameR
      ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x11 (7 : Word)) **
       (regIs .x12 (0 : Word)) ** (regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
       (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
       (memIs (sp + 8) cursor) ** (memIs (sp + 24) outerNext) **
       (memIs (sp + 32) outerStatus) ** (memIs (sp + 40) outerLen) **
       ⌜r.status ≠ 0⌝)
      (by pcf_validate_cps) h45)
  have h49e := cpsTripleWithin_extend_code h49m
    (cpsTripleWithin_frameR
      ((regIs .x10 cursor) **
       (regIs .x11 (7 : Word)) ** (regIs .x12 (0 : Word)) **
       (regIs .x0 (0 : Word)) **
       (memIs (sp + 8) cursor) **
       (memIs (sp + 24) outerNext) ** (memIs (sp + 32) outerStatus) **
       (memIs (sp + 40) outerLen) ** ⌜r.status ≠ 0⌝)
      (by pcf_validate_cps) h49)
  have h50e := cpsTripleWithin_extend_code h50m
    (cpsTripleWithin_frameR
      ((regIs .x1 raVal) ** (regIs .x10 cursor) **
       (regIs .x11 (7 : Word)) ** (regIs .x12 (0 : Word)) **
       (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
       (memIs (sp + 8) cursor) ** (memIs (sp + 24) outerNext) **
       (memIs (sp + 32) outerStatus) ** (memIs (sp + 40) outerLen) **
       ⌜r.status ≠ 0⌝)
      (by pcf_validate_cps) h50)
  have h51e := cpsTripleWithin_extend_code h51m
    (cpsTripleWithin_frameR
      ((regIs .x2 (sp + 64)) ** (regIs .x10 cursor) **
       (regIs .x11 (7 : Word)) ** (regIs .x12 (0 : Word)) **
       (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
       (memIs (sp + 8) cursor) ** (memIs (sp + 24) outerNext) **
       (memIs (sp + 32) outerStatus) ** (memIs (sp + 40) outerLen) **
       ⌜r.status ≠ 0⌝)
      (by pcf_validate_cps) h51)
  have h45e' := h45e
  rw [sepConj_emp_left'] at h45e'
  have h49e' := h49e
  have hsetup0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h42e h43e
  have hsetup1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsetup0 h44e
  have hsetup2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsetup1 h45e'
  have hreturn0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h49e' h50e
  have hreturn1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hreturn0 h51e
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hsetup2 hreturn1
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hall

theorem shared_validate_status_success_tail
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    (endPtr : Word) (sp raVal outerNext outerStatus outerLen : Word)
    (r : ValidateResult) :
    cpsTripleWithin 6 (RlpWalkNextStrictTie.S + 184)
      (raVal &&& ~~~1) RlpWalkNextStrictTie.sharedCode
      ((regIs .x2 sp) ** (regIs .x10 r.status) ** (regIs .x11 r.cursor) **
       (regIs .x12 r.len) **
       (regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
       (memIs (sp + 24) outerNext) ** (memIs (sp + 32) outerStatus) **
       (memIs (sp + 40) outerLen) ** (memIs sp raVal) **
       ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)
      ((regIs .x2 (sp + 64)) ** (regIs .x10 outerNext) **
       (regIs .x11 outerStatus) ** (regIs .x12 outerLen) **
       (regIs .x1 raVal) ** (memIs (sp + 24) outerNext) **
       (memIs (sp + 32) outerStatus) ** (memIs (sp + 40) outerLen) **
       (memIs sp raVal) **
       ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝) := by
  have htail := RlpWalkNextStrictTie.tail_block sp raVal
    (RlpWalkNextStrictTie.S + 160) r.status r.cursor r.len
    outerNext outerStatus outerLen
  have hfr := cpsTripleWithin_frameR
    (⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)
    (by pcf_validate_cps) htail
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hfr

def sharedValidateStatusFrame
    (sp raVal cursor outerNext outerStatus outerLen : Word)
    (r : ValidateResult) : Assertion :=
  ((regIs .x11 r.cursor) ** (regIs .x12 r.len) **
    (regIs .x1 (RlpWalkNextStrictTie.S + 160)) ** (regIs .x2 sp) **
    (memIs sp raVal) ** (memIs (sp + 8) cursor) **
    (memIs (sp + 24) outerNext) ** (memIs (sp + 32) outerStatus) **
    (memIs (sp + 40) outerLen))

def sharedValidateStatusSuccessPost
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    (endPtr sp raVal cursor outerNext outerStatus outerLen : Word)
    (r : ValidateResult) : Assertion :=
  ((regIs .x2 (sp + 64)) ** (regIs .x10 outerNext) **
    (regIs .x11 outerStatus) ** (regIs .x12 outerLen) **
    (regIs .x1 raVal) ** (regIs .x0 (0 : Word)) **
    (memIs sp raVal) ** (memIs (sp + 8) cursor) **
    (memIs (sp + 24) outerNext) ** (memIs (sp + 32) outerStatus) **
    (memIs (sp + 40) outerLen) **
    ⌜r.status = 0⌝ **
    ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)

def sharedValidateStatusFailurePost
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    (endPtr sp raVal cursor outerNext outerStatus outerLen : Word)
    (r : ValidateResult) : Assertion :=
  ((regIs .x2 (sp + 64)) ** (regIs .x10 cursor) **
    (regIs .x11 (7 : Word)) ** (regIs .x12 (0 : Word)) **
    (regIs .x1 raVal) ** (regIs .x0 (0 : Word)) **
    (memIs sp raVal) ** (memIs (sp + 8) cursor) **
    (memIs (sp + 24) outerNext) ** (memIs (sp + 32) outerStatus) **
    (memIs (sp + 40) outerLen) **
    ⌜r.status ≠ 0⌝ **
    ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)

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

/-! The first half of the mutual knot.  This is the complete non-empty
    validator arm, parameterised by the shared LIST-arm contract.  The
    premise is intentionally the S-entry-to-V+40 dependent contract rather
    than `shared_validate_status_dep`: the nested tail returns at V+40, while
    the latter theorem starts after the shared validator return at S+164. -/
theorem rlp_validate_payload_nonempty_cps_under_shared
    {nShared nCont : Nat} {α : Type}
    {P R : Assertion} {post : α → Assertion}
    {contCode : CodeReq}
    (oldRa exit_ : Word) (offset : BitVec 21)
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
    (hshared : cpsTripleWithin nShared
      (GuestAddrs.rlp_walk_next_shared : Word) (validateEntry + 40)
      RlpWalkNextStrictTie.sharedCode
      ((regIs .x1 (validateEntry + 40)) ** P) (cpsDepPost post))
    (hcont : ∀ a, cpsTripleWithin nCont (validateEntry + 40) exit_
      contCode (post a) R) :
    cpsTripleWithin (1 + (1 + nShared) + nCont) (validateEntry + 36) exit_
      ((CodeReq.singleton (validateEntry + 36) (.JAL .x1 offset)).union
        ((CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
          (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
            (GuestAddrs.rlp_walk_next_nested + 0)))).union
          RlpWalkNextStrictTie.sharedCode) |>.union contCode)
      ((regIs .x1 oldRa) ** P) R := by
  have hcallee := validate_nested_alias_dep_hcallee hP hsharedDisj hshared
  exact validate_nested_jal_success_dep_bind (nCall := 1 + nShared)
    (nCont := nCont) (calleeEntry := GuestAddrs.rlp_walk_next_nested)
    (calleeCode := (CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
      (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
        (GuestAddrs.rlp_walk_next_nested + 0)))).union
      RlpWalkNextStrictTie.sharedCode)
    oldRa offset exit_ hoffset halign hP hcallCode hcallee houterDisj hcont

def rlp_validate_payload_success_post
    (sp raVal cursor endPtr : Word) (P : Assertion) : Assertion :=
  (((regIs .x2 (sp + 32)) ** (regIs .x10 (0 : Word)) **
      (regIs .x1 raVal) ** (regIs .x5 endPtr) ** (regIs .x11 endPtr) **
      (memIs sp raVal) ** (memIs (sp + 8) cursor) **
      (memIs (sp + 16) endPtr)) ** (regIs .x0 (0 : Word))) ** P

def rlp_validate_payload_success_pre
    (sp raVal cursor endPtr : Word) (P : Assertion) : Assertion :=
  (((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x1 raVal) **
      (regIs .x5 endPtr) ** (regIs .x11 endPtr) ** (memIs sp raVal) **
      (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr)) **
      (regIs .x0 (0 : Word))) ** P

def rlp_validate_payload_failure_post
    (sp raVal cursor endPtr : Word) (P : Assertion) : Assertion :=
  (((regIs .x2 (sp + 32)) ** (regIs .x10 (7 : Word)) **
      (regIs .x1 raVal) ** (regIs .x5 endPtr) ** (regIs .x11 endPtr) **
      (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
      (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr)) ** P)

def rlp_validate_payload_precheck_post
    (sp raVal cursor endPtr : Word) (P : Assertion) : Assertion :=
  ((regIs .x10 cursor) ** (regIs .x5 endPtr)) ** (regIs .x2 sp) **
    (regIs .x1 raVal) ** (regIs .x11 endPtr) ** (regIs .x0 (0 : Word)) **
    (memIs sp raVal) ** (memIs (sp + 8) cursor) **
    (memIs (sp + 16) endPtr) ** P

/-! The prefix and terminal arms are composable without closing the mutual
    LIST knot.  This theorem carries the shared-arm contract as a premise and
    leaves only the continuation at `V+40` abstract.  Thus it states the whole
    validator entry contract (empty, precheck failure, nested failure, and the
    result continuation), while the eventual fuel induction can discharge the
    continuation premise separately.  The `post` family is where the decoded
    cursor/length witness is preserved. -/
theorem rlp_validate_payload_cps_under_shared
    {nShared nCont : Nat} {α : Type}
    {P R : Assertion} {post : α → Assertion}
    {contCode wholeCode : CodeReq}
    (sp raVal cursor endPtr x5Old exit_ : Word) (offset : BitVec 21)
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
    (hvalidateSub : ∀ a i, validateCR a = some i → wholeCode a = some i)
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
        ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x11 endPtr) **
          (regIs .x5 endPtr) ** (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
          (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr) ** P))
      (cpsDepPost post))
    (hcont : ∀ a, cpsTripleWithin nCont (validateEntry + 40) exit_
      contCode (post a) R)
    (hexit : exit_ = raVal &&& ~~~(1 : Word))
    (hsuccessPost : ∀ h,
      rlp_validate_payload_success_post sp raVal cursor endPtr P h → R h)
    (hfailPost : ∀ h,
      rlp_validate_payload_failure_post sp raVal cursor endPtr P h → R h) :
    cpsTripleWithin
      (9 + max 4 (max 4 (1 + (1 + nShared) + nCont))) validateEntry exit_ wholeCode
      ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) **
       (regIs .x10 cursor) ** (regIs .x11 endPtr) ** (regIs .x5 x5Old) **
       (regIs .x0 (0 : Word)) ** memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) ** P) R := by
  let bodyP : Assertion :=
    ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x11 endPtr) **
      (regIs .x5 endPtr) ** (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
      (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr) **
      P)
  have hbodyP : bodyP.pcFree := by
    simp only [bodyP]
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_pure
      | exact hP
  have hbody := rlp_validate_payload_nonempty_cps_under_shared
    (P := bodyP) (R := R) (post := post) (contCode := contCode)
    raVal exit_ offset hoffset halign hbodyP hcallCode hsharedDisj houterDisj
    (by simpa [bodyP] using hshared) hcont
  have hfail := validate_failure_tail_cps sp raVal cursor endPtr endPtr raVal endPtr
  have hfail' := cpsTripleWithin_frameR P hP hfail
  have hfailExit := hfail'
  rw [← hexit] at hfailExit
  have hfailCode := cpsTripleWithin_extend_code hvalidateSub hfailExit
  have hsuccess := validate_success_tail_cps sp raVal cursor endPtr
  have hsuccess' := cpsTripleWithin_frameR P hP
    (cpsTripleWithin_frameR (regIs .x0 (0 : Word)) (by exact pcFree_regIs) hsuccess)
  have hsuccessExit := hsuccess'
  rw [← hexit] at hsuccessExit
  have hsuccessCode := cpsTripleWithin_extend_code hvalidateSub hsuccessExit
  have hpre := validate_precheck_branch_cps cursor endPtr
  have hpre0 := cpsBranchWithin_frameR
    (((regIs .x2 sp) ** (regIs .x1 raVal) ** (regIs .x11 endPtr) **
      (regIs .x0 (0 : Word)) **
      (memIs sp raVal) ** (memIs (sp + 8) cursor) **
      (memIs (sp + 16) endPtr) ** P))
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact hP)
    hpre
  have hpre' : cpsBranchWithin 1 (validateEntry + 32) wholeCode
      (((regIs .x10 cursor) ** (regIs .x5 endPtr)) **
        ((regIs .x2 sp) ** (regIs .x1 raVal) ** (regIs .x11 endPtr) **
          (regIs .x0 (0 : Word)) **
          (memIs sp raVal) ** (memIs (sp + 8) cursor) **
          (memIs (sp + 16) endPtr) ** P))
      (validateEntry + 76)
      (((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x1 raVal) **
        (regIs .x5 endPtr) ** (regIs .x11 endPtr) ** (regIs .x0 (0 : Word)) **
        (memIs sp raVal) ** (memIs (sp + 8) cursor) **
        (memIs (sp + 16) endPtr) ** P))
      (validateEntry + 36) ((regIs .x1 raVal) ** bodyP) := by
    apply cpsBranchWithin_extend_code hvalidateSub
    refine cpsBranchWithin_weaken (fun _ hp => hp)
      (fun _ hp => by xperm_pure hp)
      (fun _ hp => by xperm_pure hp) hpre0
  have hbody' := cpsTripleWithin_extend_code hbodySub hbody
  have hpreBody := cpsBranchWithin_merge_same_cr hpre'
    (cpsTripleWithin_mono_nSteps (Nat.le_max_left
      4 (1 + (1 + nShared) + nCont))
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) hfailPost hfailCode))
      (cpsTripleWithin_mono_nSteps (Nat.le_max_right
      4 (1 + (1 + nShared) + nCont)) hbody')
  have hpreBody' : cpsTripleWithin
      (1 + max 4 (1 + (1 + nShared) + nCont)) (validateEntry + 32) exit_ wholeCode
      (rlp_validate_payload_precheck_post sp raVal cursor endPtr P) R := by
    exact hpreBody
  have hpreBodyMax : cpsTripleWithin
      (max 4 (1 + max 4 (1 + (1 + nShared) + nCont)))
      (validateEntry + 32) exit_ wholeCode
      (rlp_validate_payload_precheck_post sp raVal cursor endPtr P) R :=
    cpsTripleWithin_mono_nSteps (Nat.le_max_right
      4 (1 + max 4 (1 + (1 + nShared) + nCont))) hpreBody'
  have hempty := validate_empty_branch_cps cursor endPtr
  have hempty' := cpsBranchWithin_frameR
    (((regIs .x2 sp) ** (regIs .x1 raVal) ** (regIs .x11 endPtr) **
      (regIs .x0 (0 : Word)) **
      (memIs sp raVal) ** (memIs (sp + 8) cursor) **
      (memIs (sp + 16) endPtr) ** P))
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact hP)
    hempty
  have hemptyNoPure : cpsBranchWithin 1 (validateEntry + 28) validateCR
      (((regIs .x10 cursor) ** (regIs .x5 endPtr)) **
        ((regIs .x2 sp) ** (regIs .x1 raVal) ** (regIs .x11 endPtr) **
          (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
          (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr) ** P))
      (validateEntry + 60)
      (rlp_validate_payload_success_pre sp raVal cursor endPtr P)
      (validateEntry + 32)
      (rlp_validate_payload_precheck_post sp raVal cursor endPtr P) := by
    refine cpsBranchWithin_weaken (fun _ hp => hp) (fun _ hp => by
      drop_pure hp
      unfold rlp_validate_payload_success_pre
      xperm_chunked hp) (fun _ hp => by
      drop_pure hp
      unfold rlp_validate_payload_precheck_post
      xperm_chunked hp) hempty'
  have hemptyCode := cpsBranchWithin_extend_code hvalidateSub hemptyNoPure
  have hemptyAll := cpsBranchWithin_merge_same_cr hemptyCode
    (cpsTripleWithin_mono_nSteps (Nat.le_max_left
      4 (1 + max 4 (1 + (1 + nShared) + nCont)))
      (cpsTripleWithin_weaken (fun _ hp => by
        unfold rlp_validate_payload_success_pre at hp
        xperm_hyp hp) hsuccessPost hsuccessCode))
      hpreBodyMax
  have hload := validate_loads_cps sp cursor endPtr x5Old
  have hload' := cpsTripleWithin_frameR P hP
    (cpsTripleWithin_frameR
      (regIs .x1 raVal ** memIs sp raVal ** regIs .x0 (0 : Word))
      (by repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) hload)
  have hloadCode := cpsTripleWithin_extend_code hvalidateSub hload'
  have hpro := validate_prologue_cps sp raVal cursor endPtr
  have hpro' := cpsTripleWithin_frameR
    (regIs .x5 x5Old ** regIs .x0 (0 : Word) ** P)
    (by repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact hP) hpro
  have hproCode := cpsTripleWithin_extend_code hvalidateSub hpro'
  have h1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hloadCode hemptyAll
  have h2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hproCode h1
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => hp) h2)

/-! ## Shared-to-validator call boundary

The LIST arm reaches the validator at `S+156` with a real `JAL .x1` and
returns at `S+160`.  This theorem is the code/frame mapping for that call,
kept dependent in the same way as the nested validator call above: the
successful validator result chooses the continuation witness.  It deliberately
stops at the call boundary; the empty and failure tails, and the nonempty
mutual continuation, are separate consumers of this contract. -/

theorem validate_call_dep_hcallee
    {n : Nat} {α : Type} {P : Assertion} {post : α → Assertion}
    (oldRa : Word) (hP : P.pcFree)
    (hcallee : cpsTripleWithin n (GuestAddrs.rlp_validate_payload : Word)
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word)) validateCR
      ((.x1 ↦ᵣ (RlpWalkNextStrictTie.S + 160)) ** P) (cpsDepPost post)) :
    cpsTripleWithin (1 + n) (RlpWalkNextStrictTie.S + 156)
      (RlpWalkNextStrictTie.S + 160)
      ((CodeReq.singleton (RlpWalkNextStrictTie.S + 156)
        (.JAL .x1 (jalOff GuestAddrs.rlp_validate_payload
          (GuestAddrs.rlp_walk_next_shared + 156)))).union validateCR)
      ((.x1 ↦ᵣ oldRa) ** P) (cpsDepPost post) := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := RlpWalkNextStrictTie.S + 156)
    (calleeEntry := (GuestAddrs.rlp_validate_payload : Word)) (vOld := oldRa)
    (calleeCode := validateCR) (Prest := P) (Q := cpsDepPost post)
    (jalOff GuestAddrs.rlp_validate_payload
      (GuestAddrs.rlp_walk_next_shared + 156))
    (by decide) (by decide) hP
    (CodeReq.Disjoint.singleton_ofProg
      (CodeReq.ofProg_none_range_len
        (GuestAddrs.rlp_validate_payload : Word) rlpValidatePayload_prog 23
        (RlpWalkNextStrictTie.S + 156) (by rfl) (by
        intro k hk heq
        have hS : (RlpWalkNextStrictTie.S + 156).toNat = 2147504872 := by decide
        have hV : (GuestAddrs.rlp_validate_payload : Word).toNat = 2147504924 := by decide
        have h := congrArg BitVec.toNat heq
        rw [hS] at h
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hV] at h
        omega))) hcallee
  exact hcall

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

/-! Full status integration.  The two exits are kept separate: success passes
through the six-instruction epilogue at `S+184`, while failure executes its
four setup instructions and returns from `S+196`, with the core spill values
still intact. -/
theorem shared_validate_status_dep
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    (endPtr sp raVal cursor outerNext outerStatus outerLen : Word)
    (r : ValidateResult) :
    cpsNBranchWithin 14 (RlpWalkNextStrictTie.S + 164)
      RlpWalkNextStrictTie.sharedCode
      (((regIs .x10 r.status) ** (regIs .x0 (0 : Word))) **
       ((sharedValidateStatusFrame sp raVal cursor outerNext outerStatus outerLen r) **
        ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝))
      [(raVal &&& ~~~1,
        sharedValidateStatusSuccessPost (bytes := bytes) (base := base) (floor := floor)
          (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
          endPtr sp raVal cursor outerNext outerStatus outerLen r),
       (raVal &&& ~~~1,
        sharedValidateStatusFailurePost (bytes := bytes) (base := base) (floor := floor)
          (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
          endPtr sp raVal cursor outerNext outerStatus outerLen r)] := by
  have hbr0 := shared_validate_result_branch r.status
  have hbr := cpsBranchWithin_frameR
    ((sharedValidateStatusFrame sp raVal cursor outerNext outerStatus outerLen r) **
      ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)
    (by pcf_validate_cps) hbr0
  have hsucc0 := shared_validate_status_success_tail
    (bytes := bytes) (base := base) (floor := floor)
    (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
    endPtr sp raVal outerNext outerStatus outerLen r
  have hsuccCursor := cpsTripleWithin_frameR (memIs (sp + 8) cursor)
    (by pcf_validate_cps) hsucc0
  have hsucc := cpsTripleWithin_frameR (regIs .x0 (0 : Word))
    (by pcf_validate_cps) hsuccCursor
  have hsuccFacts := cpsTripleWithin_frameR (⌜r.status = 0⌝)
    (by pcf_validate_cps) hsucc
  have hfail0 := shared_validate_status_failure_tail
    sp raVal cursor outerNext outerStatus outerLen r
  have hfail := cpsTripleWithin_frameR
    (⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)
    (by pcf_validate_cps) hfail0
  have hfail' : cpsTripleWithin 7 (RlpWalkNextStrictTie.S + 168)
      (raVal &&& ~~~1) RlpWalkNextStrictTie.sharedCode
      (((regIs .x10 r.status) ** (regIs .x0 (0 : Word)) **
        ⌜r.status ≠ 0⌝) **
          (sharedValidateStatusFrame sp raVal cursor outerNext outerStatus outerLen r) **
          ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)
      (sharedValidateStatusFailurePost (bytes := bytes) (base := base)
        (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
        (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus outerLen r) := by
    simp only [RlpWalkNextStrictTie.S] at hfail
    simp only [sharedValidateStatusFrame, RlpWalkNextStrictTie.S]
    simp only [sharedValidateStatusFailurePost]
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => by xperm_chunked hp) hfail
  have hfailN := cpsTripleWithin_as_cpsNBranchWithin hfail'
  have hbranch := cpsBranchWithin_cons_cpsNBranchWithin_same_cr hbr hfailN
  have hsucc' : cpsTripleWithin 6 (RlpWalkNextStrictTie.S + 184)
      (raVal &&& ~~~1) RlpWalkNextStrictTie.sharedCode
      (((regIs .x10 r.status) ** (regIs .x0 (0 : Word)) **
        ⌜r.status = 0⌝) **
          (sharedValidateStatusFrame sp raVal cursor outerNext outerStatus outerLen r) **
          ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)
      (sharedValidateStatusSuccessPost (bytes := bytes) (base := base)
        (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
        (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus outerLen r) := by
    simp only [RlpWalkNextStrictTie.S] at hsuccFacts
    simp only [sharedValidateStatusFrame, RlpWalkNextStrictTie.S]
    simp only [sharedValidateStatusSuccessPost]
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => by xperm_chunked hp) hsuccFacts
  have hsuccN := cpsTripleWithin_as_cpsNBranchWithin hsucc'
  have hall := cpsNBranchWithin_extend_head_nbranch hbranch hsuccN
  exact hall


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

theorem shared_long_prefix_payload_base (cursor pfx oldOut : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 136)
      (RlpWalkNextStrictTie.S + 140) RlpWalkNextStrictTie.sharedCode
      ((regIs .x12 oldOut) ** (regIs .x5 cursor) ** (regIs .x13 pfx))
      ((regIs .x12 (cursor + pfx)) ** (regIs .x5 cursor) ** (regIs .x13 pfx)) := by
  have h := add_spec_gen_within .x12 .x5 .x13 cursor pfx oldOut
    (RlpWalkNextStrictTie.S + 136) (by decide)
  rw [show RlpWalkNextStrictTie.S + 136 + 4 = RlpWalkNextStrictTie.S + 140 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 136)
      (.ADD .x12 .x5 .x13) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 34 (RlpWalkNextStrictTie.S + 136)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hcode

theorem shared_long_prefix_payload_start (cursor pfx : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 140)
      (RlpWalkNextStrictTie.S + 144) RlpWalkNextStrictTie.sharedCode
      ((regIs .x12 (cursor + pfx)) ** (regIs .x5 cursor) ** (regIs .x13 pfx))
      ((regIs .x12 (cursor + pfx + 1)) ** (regIs .x5 cursor) ** (regIs .x13 pfx)) := by
  have h := addi_spec_gen_same_within .x12 (cursor + pfx) (1 : BitVec 12)
    (RlpWalkNextStrictTie.S + 140) (by decide)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    show (cursor + pfx) + (1 : Word) = cursor + pfx + 1 by bv_omega,
    show RlpWalkNextStrictTie.S + 140 + 4 = RlpWalkNextStrictTie.S + 144 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 140)
      (.ADDI .x12 .x12 (1 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 35 (RlpWalkNextStrictTie.S + 140)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  have hframe := cpsTripleWithin_frameR
    ((regIs .x5 cursor) ** (regIs .x13 pfx))
    (by apply pcFree_sepConj <;> exact pcFree_regIs) hcode
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hframe

theorem shared_long_prefix_to_validator (payload : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 144)
      (RlpWalkNextStrictTie.S + 152) RlpWalkNextStrictTie.sharedCode
      (regIs .x12 payload) (regIs .x12 payload) := by
  have h := jal_x0_spec_gen_within (8 : BitVec 21)
    (RlpWalkNextStrictTie.S + 144)
  rw [show (RlpWalkNextStrictTie.S + 144) +
      signExtend21 (8 : BitVec 21) = RlpWalkNextStrictTie.S + 152 from by
        rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]
        bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 144)
      (.JAL .x0 (8 : BitVec 21)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 36 (RlpWalkNextStrictTie.S + 144)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  have hframe := cpsTripleWithin_frameR (regIs .x12 payload)
    (by exact pcFree_regIs) hcode
  have hframe' := cpsTripleWithin_weaken
    (fun h hp => (sepConj_emp_left h).mpr hp)
    (fun h hp => (sepConj_emp_left h).mp hp) hframe
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hframe'

theorem shared_long_prefix_shift (acc : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 112)
      (RlpWalkNextStrictTie.S + 116) RlpWalkNextStrictTie.sharedCode
      (regIs .x30 acc) (regIs .x30 (acc <<< 8)) := by
  have h := slli_spec_gen_same_within .x30 acc (8 : BitVec 6)
    (RlpWalkNextStrictTie.S + 112) (by decide)
  rw [show RlpWalkNextStrictTie.S + 112 + 4 = RlpWalkNextStrictTie.S + 116 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 112)
      (.SLLI .x30 .x30 (8 : BitVec 6)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 28 (RlpWalkNextStrictTie.S + 112)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hcode

theorem shared_long_prefix_load_byte
    (cursor oldByte dwordAddr wordVal : Word)
    (halign : alignToDword cursor = dwordAddr)
    (hvalid : isValidByteAccess cursor = true) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 116)
      (RlpWalkNextStrictTie.S + 120) RlpWalkNextStrictTie.sharedCode
      ((regIs .x29 cursor) ** (regIs .x31 oldByte) ** (dwordAddr ↦ₘ wordVal))
      ((regIs .x29 cursor) **
        (regIs .x31 ((extractByte wordVal (byteOffset cursor)).zeroExtend 64)) **
        (dwordAddr ↦ₘ wordVal)) := by
  have h := lbu_spec_gen_within .x31 .x29 cursor oldByte
    (0 : BitVec 12) (RlpWalkNextStrictTie.S + 116)
    dwordAddr wordVal (by decide) (by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
        show cursor + (0 : Word) = cursor by bv_omega]
      exact halign) (by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
        show cursor + (0 : Word) = cursor by bv_omega]
      exact hvalid)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show cursor + (0 : Word) = cursor by bv_omega,
    show RlpWalkNextStrictTie.S + 116 + 4 = RlpWalkNextStrictTie.S + 120 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 116)
      (.LBU .x31 .x29 (0 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 29 (RlpWalkNextStrictTie.S + 116)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hcode

theorem shared_long_prefix_accumulate_byte (acc byte : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 120)
      (RlpWalkNextStrictTie.S + 124) RlpWalkNextStrictTie.sharedCode
      ((regIs .x30 acc) ** (regIs .x31 byte))
      ((regIs .x30 (acc ||| byte)) ** (regIs .x31 byte)) := by
  have h := or_spec_gen_rd_eq_rs1_within .x30 .x31 acc byte
    (RlpWalkNextStrictTie.S + 120) (by decide)
  rw [show RlpWalkNextStrictTie.S + 120 + 4 = RlpWalkNextStrictTie.S + 124 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 120)
      (.OR .x30 .x30 .x31) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 30 (RlpWalkNextStrictTie.S + 120)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hcode

theorem shared_long_prefix_init_acc (oldAcc : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 104)
      (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
      (regIs .x30 oldAcc) (regIs .x30 (0 : Word)) := by
  have h := li_spec_gen_within .x30 oldAcc (0 : Word)
    (RlpWalkNextStrictTie.S + 104) (by decide)
  rw [show RlpWalkNextStrictTie.S + 104 + 4 = RlpWalkNextStrictTie.S + 108 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 104)
      (.LI .x30 (0 : Word)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 26 (RlpWalkNextStrictTie.S + 104)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hcode

theorem shared_list_load_end (sp endPtr oldEnd : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 76)
      (RlpWalkNextStrictTie.S + 80) RlpWalkNextStrictTie.sharedCode
      ((regIs .x2 sp) ** (regIs .x11 oldEnd) ** ((sp + 24) ↦ₘ endPtr))
      ((regIs .x2 sp) ** (regIs .x11 endPtr) ** ((sp + 24) ↦ₘ endPtr)) := by
  have h := ld_spec_gen_within .x11 .x2 sp oldEnd endPtr
    (24 : BitVec 12) (RlpWalkNextStrictTie.S + 76) (by decide)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
    show RlpWalkNextStrictTie.S + 76 + 4 = RlpWalkNextStrictTie.S + 80 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 76)
      (.LD .x11 .x2 (24 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 19 (RlpWalkNextStrictTie.S + 76)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  exact cpsTripleWithin_extend_code hmono h

theorem shared_list_load_cursor (sp cursor oldCursor : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 48)
      (RlpWalkNextStrictTie.S + 52) RlpWalkNextStrictTie.sharedCode
      ((regIs .x2 sp) ** (regIs .x5 oldCursor) ** ((sp + 8) ↦ₘ cursor))
      ((regIs .x2 sp) ** (regIs .x5 cursor) ** ((sp + 8) ↦ₘ cursor)) := by
  have h := ld_spec_gen_within .x5 .x2 sp oldCursor cursor
    (8 : BitVec 12) (RlpWalkNextStrictTie.S + 48) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show RlpWalkNextStrictTie.S + 48 + 4 = RlpWalkNextStrictTie.S + 52 by decide] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 48)
      (.LD .x5 .x2 (8 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 12 (RlpWalkNextStrictTie.S + 48)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by decide))
  exact cpsTripleWithin_extend_code hmono h

theorem shared_list_length_prefix_load (sp cursor oldByte : Word)
    (halign : alignToDword cursor = cursor &&& ~~~(7 : Word))
    (hvalid : isValidByteAccess cursor = true) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 52)
      (RlpWalkNextStrictTie.S + 56) RlpWalkNextStrictTie.sharedCode
      ((regIs .x5 cursor) ** (regIs .x6 oldByte) **
        ((cursor &&& ~~~(7 : Word)) ↦ₘ sp))
      ((regIs .x5 cursor) **
        (regIs .x6 ((extractByte sp (byteOffset cursor)).zeroExtend 64)) **
        ((cursor &&& ~~~(7 : Word)) ↦ₘ sp)) := by
  have h := lbu_spec_gen_within .x6 .x5 cursor oldByte
    (0 : BitVec 12) (RlpWalkNextStrictTie.S + 52)
    (cursor &&& ~~~(7 : Word)) sp (by decide) (by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
        show cursor + (0 : Word) = cursor by bv_omega]
      exact halign) (by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
        show cursor + (0 : Word) = cursor by bv_omega]
      exact hvalid)
  rw [show RlpWalkNextStrictTie.S + 52 + 4 = RlpWalkNextStrictTie.S + 56 by decide,
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show cursor + (0 : Word) = cursor by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 52)
      (.LBU .x6 .x5 (0 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 13 (RlpWalkNextStrictTie.S + 52)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by decide))
  exact cpsTripleWithin_extend_code hmono h

theorem shared_short_list_payload_start (cursor oldPayload : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 148)
      (RlpWalkNextStrictTie.S + 152) RlpWalkNextStrictTie.sharedCode
      ((regIs .x5 cursor) ** (regIs .x12 oldPayload))
      ((regIs .x5 cursor) ** (regIs .x12 (cursor + 1))) := by
  have h := addi_spec_gen_within .x12 .x5 oldPayload cursor (1 : BitVec 12)
    (RlpWalkNextStrictTie.S + 148) (by decide)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    show RlpWalkNextStrictTie.S + 148 + 4 = RlpWalkNextStrictTie.S + 152 by decide] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 148)
      (.ADDI .x12 .x5 (1 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 37 (RlpWalkNextStrictTie.S + 148)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by decide))
  have hcode := cpsTripleWithin_extend_code hmono h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hcode

theorem shared_payload_handoff (payload oldPayload : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 152)
      (RlpWalkNextStrictTie.S + 156) RlpWalkNextStrictTie.sharedCode
      ((regIs .x10 oldPayload) ** (regIs .x12 payload))
      ((regIs .x10 payload) ** (regIs .x12 payload)) := by
  have h := mv_spec_gen_within .x10 .x12 payload oldPayload
    (RlpWalkNextStrictTie.S + 152) (by decide)
  rw [show RlpWalkNextStrictTie.S + 152 + 4 = RlpWalkNextStrictTie.S + 156 by decide] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 152)
      (.MV .x10 .x12) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 38 (RlpWalkNextStrictTie.S + 152)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by decide))
  have hcode := cpsTripleWithin_extend_code hmono h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hcode

theorem shared_depth_decrement (depth : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 160)
      (RlpWalkNextStrictTie.S + 164) RlpWalkNextStrictTie.sharedCode
      (regIs .x9 depth) (regIs .x9 (depth - 1)) := by
  have h := addi_spec_gen_same_within .x9 depth (-1 : BitVec 12)
    (RlpWalkNextStrictTie.S + 160) (by decide)
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide,
    show depth + (-1 : Word) = depth - 1 by bv_omega,
    show RlpWalkNextStrictTie.S + 160 + 4 = RlpWalkNextStrictTie.S + 164 by decide] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 160)
      (.ADDI .x9 .x9 (-1 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 40 (RlpWalkNextStrictTie.S + 160)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by decide))
  exact cpsTripleWithin_extend_code hmono h

end EvmAsm.Codegen.RlpWalkNextStrictFuel
