/-
  EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelContracts

  Foundational machine-level CPS contracts for #12300.  The structural fuel
  model for the strict LIST recursion lives in the sibling
  `RlpWalkNextStrictFuelModel` module; this file contains the validator-side
  contracts consumed by the shared-machine continuation module.
-/

import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelModel
import EvmAsm.Codegen.Programs.RlpWalkNextStrictTie
import EvmAsm.Rv64.RLP.WalkItemDeterminism
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.Tactics.XPermPure
import EvmAsm.Rv64.Tactics.DropPure

namespace EvmAsm.Codegen.RlpWalkNextStrictFuel

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP


/-! A CPS contract has two independent measures.  `index` is the structural
`cycleFuel` used by the mutual induction; `steps` is only the machine-step
bound consumed by `cpsTripleWithin`.  Keeping them in separate fields prevents
the tempting (and unsound) use of a `max` of CPS bounds as a termination
measure. -/
structure IndexedCpsContract
    (index : Nat) (entry exit_ : Word) (code : CodeReq)
    (pre post : Assertion) : Type where
  steps : Nat
  proof : cpsTripleWithin steps entry exit_ code pre post

/-! The named adapter is the exact entry-point bridge still needed by the full
mutual proof.  Its validator witness is at the child `cycleFuel`; the two
functions return arm contracts at the parent index, with their CPS bounds free
to differ.  Any missing setup/status fact therefore appears as an explicit
field rather than disappearing inside induction. -/
structure SharedListValidatorAdapter
    (parentFuel childFuel : Nat) (Validator : Prop)
    (pfx exit_ : Word) (P R : Assertion) : Type where
  decrease : childFuel < parentFuel
  validator : Validator
  short : Validator → IndexedCpsContract parentFuel
    (RlpWalkNextStrictTie.S + 148) exit_
    RlpWalkNextStrictTie.sharedCode
    (((regIs .x6 pfx) ** (regIs .x7 (248 : Word)) **
      pure (BitVec.ult pfx (248 : Word))) ** P) R
  long : Validator → IndexedCpsContract parentFuel
    (RlpWalkNextStrictTie.S + 88) exit_
    RlpWalkNextStrictTie.sharedCode
    (((regIs .x6 pfx) ** (regIs .x7 (248 : Word)) **
      pure (¬ BitVec.ult pfx (248 : Word))) ** P) R

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

macro "pcf_validate_cps" : tactic =>
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

theorem validate_loads_cps (sp cursor endPtr x5Old x11Old : Word) :
    cpsTripleWithin 3 (validateEntry + 16) (validateEntry + 28) validateCR
      ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x5 x5Old) **
       (regIs .x11 x11Old) ** (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr))
      ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x5 endPtr) **
       (regIs .x11 endPtr) ** (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr)) := by
  have h4 := ld_spec_gen_within .x10 .x2 sp cursor cursor (8 : BitVec 12)
    (validateEntry + 16) (by decide)
  have h4' := cpsTripleWithin_frameR
    ((regIs .x5 x5Old) ** (regIs .x11 x11Old)) (by pcf_validate_cps) h4
  have h5 := ld_spec_gen_within .x5 .x2 sp x5Old endPtr (16 : BitVec 12)
    (validateEntry + 20) (by decide)
  have h5' := cpsTripleWithin_frameR (regIs .x11 x11Old) (by pcf_validate_cps) h5
  have h6 := mv_spec_gen_within .x11 .x5 endPtr x11Old (validateEntry + 24) (by decide)
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

/-- Success epilogue at `V+60`.  `x1Old` is the live return-address register
before the stack reload: on the entry/empty path it equals `raVal`, but on the
Cont zero-loop path it is `V+40` while `memIs sp` still holds the outer
`raVal` (#12419). -/
theorem validate_success_tail_cps (sp x1Old raVal cursor endPtr : Word) :
    cpsTripleWithin 4 (validateEntry + 60) (raVal &&& ~~~1) validateCR
      ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x1 x1Old) **
       (regIs .x5 endPtr) ** (regIs .x11 endPtr) ** (memIs sp raVal) **
       (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr))
      ((regIs .x2 (sp + 32)) ** (regIs .x10 (0 : Word)) ** (regIs .x1 raVal) **
       (regIs .x5 endPtr) ** (regIs .x11 endPtr) ** (memIs sp raVal) **
       (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr)) := by
  have h15 := li_spec_gen_within .x10 cursor (0 : Word) (validateEntry + 60) (by decide)
  have h16 := ld_spec_gen_within .x1 .x2 sp x1Old raVal
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
  have hload := validate_loads_cps sp cursor endPtr x5Old endPtr
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
  have htail := validate_success_tail_cps sp raVal raVal cursor endPtr
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
    (sp callRa x10Val status x5Old raVal memCursor memEnd : Word) :
    cpsTripleWithin 4 (validateEntry + 76) (raVal &&& ~~~1) validateCR
      ((regIs .x2 sp) ** (regIs .x10 x10Val) ** (regIs .x1 callRa) **
       (regIs .x5 x5Old) ** (regIs .x11 status) ** (regIs .x0 (0 : Word)) **
       (memIs sp raVal) ** (memIs (sp + 8) memCursor) **
       (memIs (sp + 16) memEnd))
      ((regIs .x2 (sp + 32)) ** (regIs .x10 (7 : Word)) ** (regIs .x1 raVal) **
       (regIs .x5 x5Old) ** (regIs .x11 status) ** (regIs .x0 (0 : Word)) **
       (memIs sp raVal) ** (memIs (sp + 8) memCursor) **
       (memIs (sp + 16) memEnd)) := by
  have h19 := li_spec_gen_within .x10 x10Val (7 : Word) (validateEntry + 76) (by decide)
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
       (memIs (sp + 8) memCursor) ** (memIs (sp + 16) memEnd))
      (by pcf_validate_cps) h19)
  have h20e := cpsTripleWithin_extend_code h20m
    (cpsTripleWithin_frameR
      ((regIs .x10 (7 : Word)) ** (regIs .x5 x5Old) ** (regIs .x11 status) **
       (regIs .x0 (0 : Word)) ** (memIs (sp + 8) memCursor) ** (memIs (sp + 16) memEnd))
      (by pcf_validate_cps) h20)
  have h21e := cpsTripleWithin_extend_code h21m
    (cpsTripleWithin_frameR
      ((regIs .x10 (7 : Word)) ** (regIs .x1 raVal) ** (regIs .x5 x5Old) **
       (regIs .x11 status) ** (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
       (memIs (sp + 8) memCursor) ** (memIs (sp + 16) memEnd))
      (by pcf_validate_cps) h21)
  have h22e := cpsTripleWithin_extend_code h22m
    (cpsTripleWithin_frameR
      ((regIs .x2 (sp + 32)) ** (regIs .x10 (7 : Word)) ** (regIs .x5 x5Old) **
       (regIs .x11 status) ** (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
       (memIs (sp + 8) memCursor) ** (memIs (sp + 16) memEnd))
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
    (sp raVal cursor status endPtr frameCursor x5Old : Word)
    (hstatus : status ≠ 0) :
    cpsTripleWithin 5 (validateEntry + 40) (raVal &&& ~~~1) validateCR
      ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x11 status) **
       (regIs .x0 (0 : Word)) ** (regIs .x1 (validateEntry + 40)) **
       (regIs .x5 x5Old) ** (memIs sp raVal) ** (memIs (sp + 8) frameCursor) **
       (memIs (sp + 16) endPtr))
      ((regIs .x2 (sp + 32)) ** (regIs .x10 (7 : Word)) ** (regIs .x11 status) **
       (regIs .x0 (0 : Word)) ** (regIs .x1 raVal) ** (regIs .x5 x5Old) **
       (memIs sp raVal) ** (memIs (sp + 8) frameCursor) **
       (memIs (sp + 16) endPtr)) := by
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
      (regIs .x5 x5Old) ** (memIs sp raVal) ** (memIs (sp + 8) frameCursor) **
      (memIs (sp + 16) endPtr))
    (by pcf_validate_cps) htaken'
  have htail := validate_failure_tail_cps sp (validateEntry + 40) cursor status x5Old
    raVal frameCursor endPtr
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
    (sp x1Val spVal cursorPtr frameCursor endPtr x5Old : Word)
    (hcursor : ¬ BitVec.ult endPtr cursorPtr) :
    cpsTripleWithin 4 (validateEntry + 44) (validateEntry + 16) validateCR
      ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 x1Val) **
       (regIs .x5 x5Old) ** (regIs .x11 (0 : Word)) **
       (memIs sp spVal) ** (memIs (sp + 8) frameCursor) **
       (memIs (sp + 16) endPtr) **
       ⌜ValidateK bytes base floor cursorPtr endPtr nextOff endOff fuel⌝)
      ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 x1Val) **
       (regIs .x5 endPtr) ** (regIs .x11 (0 : Word)) **
       (memIs sp spVal) ** (memIs (sp + 8) cursorPtr) **
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
    ((regIs .x10 cursorPtr) ** (regIs .x1 x1Val) **
      (regIs .x11 (0 : Word)) ** (memIs sp spVal) **
      (memIs (sp + 8) frameCursor) **
      ⌜ValidateK bytes base floor cursorPtr endPtr nextOff endOff fuel⌝)
    (by pcf_validate_cps) hldE
  have hbr'' := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x1 x1Val) **
      (regIs .x11 (0 : Word)) ** (memIs sp spVal) **
      (memIs (sp + 8) frameCursor) ** (memIs (sp + 16) endPtr) **
      ⌜ValidateK bytes base floor cursorPtr endPtr nextOff endOff fuel⌝)
    (by pcf_validate_cps) hbrE
  have hsd' := cpsTripleWithin_frameR
    ((regIs .x1 x1Val) ** (regIs .x5 endPtr) ** (regIs .x11 (0 : Word)) **
      (memIs sp spVal) ** (memIs (sp + 16) endPtr) **
      ⌜ValidateK bytes base floor cursorPtr endPtr nextOff endOff fuel⌝)
    (by pcf_validate_cps) hsdE
  have hjal' := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 x1Val) **
      (regIs .x5 endPtr) ** (regIs .x11 (0 : Word)) ** (memIs sp spVal) **
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
    endPtr raVal cursor endPtr
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
  ∀ (sp x1Val spVal cursorPtr frameCursorPtr endPtr : Word),
    ¬ BitVec.ult endPtr cursorPtr →
    cpsTripleWithin 4 (validateEntry + 44) (validateEntry + 16) validateCR
      ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 x1Val) **
       regOwn .x5 ** (regIs .x11 (0 : Word)) **
       (memIs sp spVal) ** (memIs (sp + 8) frameCursorPtr) **
       (memIs (sp + 16) endPtr) **
       ⌜ValidateK bytes base floor cursorPtr endPtr nextOff endOff fuel⌝)
      ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 x1Val) **
       (regIs .x5 endPtr) ** (regIs .x11 (0 : Word)) **
       (memIs sp spVal) ** (memIs (sp + 8) cursorPtr) **
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
    ∀ (sp x1Val spVal frameCursorPtr : Word),
      cpsTripleWithin 4 (validateEntry + 44) (validateEntry + 16) validateCR
        ((regIs .x2 sp) ** (regIs .x10 a0) ** (regIs .x1 x1Val) **
         regOwn .x5 ** (regIs .x11 (0 : Word)) **
         (memIs sp spVal) ** (memIs (sp + 8) frameCursorPtr) **
         (memIs (sp + 16) endPtr) **
         ⌜ValidateK bytes base floor a0 endPtr next endOff (endOff - next)⌝)
        ((regIs .x2 sp) ** (regIs .x10 a0) ** (regIs .x1 x1Val) **
         (regIs .x5 endPtr) ** (regIs .x11 (0 : Word)) **
         (memIs sp spVal) ** (memIs (sp + 8) a0) **
         (memIs (sp + 16) endPtr) **
         ⌜ValidateK bytes base floor a0 endPtr next endOff (endOff - next)⌝) := by
  intro sp x1Val spVal frameCursorPtr
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
  simpa [hK] using hloop sp x1Val spVal a0 frameCursorPtr endPtr hcross

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
    (sp x1Val spVal frameCursorPtr : Word) :
    cpsTripleWithin 5 (validateEntry + 40) (validateEntry + 16) validateCR
      ((regIs .x2 sp) ** (regIs .x10 a0) ** (regIs .x11 status) **
       (regIs .x0 (0 : Word)) ** (regIs .x1 x1Val) ** regOwn .x5 **
       (memIs sp spVal) ** (memIs (sp + 8) frameCursorPtr) **
       (memIs (sp + 16) endPtr) **
       ⌜ValidateK bytes base floor a0 endPtr next endOff (endOff - next)⌝)
      ((regIs .x2 sp) ** (regIs .x10 a0) ** (regIs .x11 (0 : Word)) **
       (regIs .x0 (0 : Word)) ** (regIs .x1 x1Val) ** (regIs .x5 endPtr) **
       (memIs sp spVal) ** (memIs (sp + 8) a0) **
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
    sp x1Val spVal frameCursorPtr
  have hzero' := cpsTripleWithin_frameR (regIs .x0 (0 : Word))
    (by pcf_validate_cps) hzero
  have hbrFull := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x10 a0) ** (regIs .x1 x1Val) **
      regOwn .x5 ** (memIs sp spVal) **
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
        fun sp x1Val spVal cursorPtr frameCursorPtr endPtr hcross => by
          have hown : cpsTripleWithin 4 (validateEntry + 44) (validateEntry + 16)
              validateCR
              (((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 x1Val) **
                (regIs .x11 (0 : Word)) ** (memIs sp spVal) **
                (memIs (sp + 8) frameCursorPtr) ** (memIs (sp + 16) endPtr) **
                ⌜ValidateK bytes base floor cursorPtr endPtr next endOff (endOff - next)⌝) **
               regOwn .x5)
              ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 x1Val) **
               (regIs .x5 endPtr) ** (regIs .x11 (0 : Word)) **
               (memIs sp spVal) ** (memIs (sp + 8) cursorPtr) **
               (memIs (sp + 16) endPtr) **
               ⌜ValidateK bytes base floor cursorPtr endPtr next endOff (endOff - next)⌝) := by
            apply cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
            intro x5Old
            exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
              (fun _ hp => by xperm_hyp hp)
              (validate_nested_zero_loop_cps (bytes := bytes) (base := base)
                (floor := floor) (nextOff := next) (endOff := endOff)
                (fuel := (endOff - next)) sp x1Val spVal cursorPtr frameCursorPtr endPtr x5Old hcross)
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
      have hloop' := hloop sp callRa callRa cursorPtr frameCursorPtr endPtr hcross
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
    (cursorOff endOff : Nat) (_fuel : Nat) (endPtr : Word)
    (r : ValidateResult) : Prop :=
  (r.status = 0 ∧
    -- Continuation fuel is the REMAINING window (`endOff - r.next`), not the
    -- outer `_fuel` (`endOff - cursorOff`).  Coupling them made Cont's zero arm
    -- uninhabitable on any advancing item (#12419).  `_fuel` is retained in the
    -- signature for callers that thread the outer window beside these facts.
    --
    -- The head facts (tail `ValidateK`, first-item decode) reference the
    -- SEMANTIC first-item boundary `r.next`, NOT the register value `r.cursor`
    -- (#12419).  Previously `ValidateK`'s cursorPtr was `r.cursor`, forcing
    -- `r.cursor = base + r.next` — which tied the exit register to the first
    -- item's end and made `regIs x11 r.cursor` UNSATISFIABLE on any multi-item
    -- window (the machine leaves `x11 = endPtr` via `mv x11,x5`).  Decoupling
    -- lets success freely choose `r.cursor := endPtr` (the true exit value)
    -- while these pures still pin the first-item/tail structure at `r.next`.
    ValidateK bytes base floor (base + BitVec.ofNat 64 r.next) endPtr
      r.next endOff (endOff - r.next) ∧
    rlpItemDecodeStrictW bytes base cursorOff
      r.next (endPtr - base).toNat r.len (floor + 1)) ∨
  r.status ≠ 0

def validateResultPost
    (bytes : List (BitVec 8)) (base : Word) (floor : Nat)
    (cursorOff endOff fuel : Nat) (endPtr : Word)
    (r : ValidateResult) : Assertion :=
  -- `x11 = r.cursor` is the per-outcome TRUE exit value (endPtr on success via
  -- the existential, the failing status on the nonzero arm).  `x12` is held as
  -- `regOwn`: no instruction in `rlpValidatePayload_prog` writes it, so at the
  -- aggregate success exit it holds the LAST child's len (nested-call residue),
  -- outcome-dependent and unobservable (in-degree 1, SP restored) — pinning a
  -- value would be false on multi-item.  `r.len` survives only as the
  -- first-item length inside the decode pure (#12419).
  ((regIs .x10 r.status) ** (regIs .x11 r.cursor) **
    regOwn .x12 **
    ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)

/-! The validator's nonzero status arm is intentionally not made symmetric with
the success tail.  It reloads the caller cursor, materialises status 7/length
zero, and jumps directly to `S + 196`; the outer spill slots therefore still
contain the core result.  Keeping that layout explicit prevents a dependent
post from silently claiming that the skipped tail stores ran. -/
theorem shared_validate_status_failure_tail
    (sp raVal cursor outerNext outerStatus outerLen x12Old : Word)
    (r : ValidateResult) :
    cpsTripleWithin 7 (RlpWalkNextStrictTie.S + 168)
      (raVal &&& ~~~1) RlpWalkNextStrictTie.sharedCode
      ((regIs .x2 sp) ** (regIs .x10 r.status) ** (regIs .x11 r.cursor) **
       (regIs .x12 x12Old) **
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
  have h44 := li_spec_gen_within .x12 x12Old (0 : Word)
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
       (regIs .x11 r.cursor) ** (regIs .x12 x12Old) **
       (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
       (memIs (sp + 24) outerNext) ** (memIs (sp + 32) outerStatus) **
       (memIs (sp + 40) outerLen) ** ⌜r.status ≠ 0⌝)
      (by pcf_validate_cps) h42)
  have h43e := cpsTripleWithin_extend_code h43m
    (cpsTripleWithin_frameR
      ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x12 x12Old) **
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
    (endPtr : Word) (sp raVal outerNext outerStatus outerLen x12Old : Word)
    (r : ValidateResult) :
    cpsTripleWithin 6 (RlpWalkNextStrictTie.S + 184)
      (raVal &&& ~~~1) RlpWalkNextStrictTie.sharedCode
      ((regIs .x2 sp) ** (regIs .x10 r.status) ** (regIs .x11 r.cursor) **
       (regIs .x12 x12Old) **
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
    (RlpWalkNextStrictTie.S + 160) r.status r.cursor x12Old
    outerNext outerStatus outerLen
  have hfr := cpsTripleWithin_frameR
    (⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)
    (by pcf_validate_cps) htail
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hfr

def sharedValidateStatusFrame
    (sp raVal cursor outerNext outerStatus outerLen : Word)
    (r : ValidateResult) : Assertion :=
  -- `x12` held as `regOwn` (not `regIs .x12 r.len`): the nested validate call
  -- returns `regOwn .x12` (its exit value is the LAST child's len, outcome
  -- dependent and unobservable — #12419), and the shared status handler
  -- OVERWRITES `x12` anyway (`li x12,0` on failure, `ld x12,40(sp)=outerLen`
  -- on success), so the incoming value is dead here.
  ((regIs .x11 r.cursor) ** regOwn .x12 **
    (regIs .x1 (RlpWalkNextStrictTie.S + 160)) ** (regIs .x2 sp) **
    (memIs sp raVal) ** (memIs (sp + 8) cursor) **
    (memIs (sp + 24) outerNext) ** (memIs (sp + 32) outerStatus) **
    (memIs (sp + 40) outerLen))

/-- `sharedValidateStatusFrame` with `x12` pinned to a concrete `x12v` (the
value-parameterized family member: the status handler reloads `x12`, so the
incoming value is arbitrary — see `sharedValidateStatusFrame`, #12419). -/
def sharedValidateStatusFrameAt
    (sp raVal cursor outerNext outerStatus outerLen x12v : Word)
    (r : ValidateResult) : Assertion :=
  ((regIs .x11 r.cursor) ** (regIs .x12 x12v) **
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


end EvmAsm.Codegen.RlpWalkNextStrictFuel
