/-
  EvmAsm.Codegen.Programs.ValidateHeaderWhole

  Whole-routine composition shell for `validate_header` (#12346).

  The machine route between H+56 and H+352 is supplied as an explicit
  `validateHeaderCoreExits` contract. This file does not turn that premise
  into a proof by naming it: the premise is the remaining composition work
  (the six checker/callee seams and their fall-through branches). What is
  discharged here is the ABI composition around that route, including the
  SpecRef status relation, the 56-byte prologue, and the common epilogue.
  Status 12 is a guest-side rejection outside the result space of
  `SpecRef.validate_header`: it is K67's status-4 (init/walk failure) remapped
  by the caller's `status12_tail`.  Its post therefore carries the concrete
  `k67GuardFail` predicate rather than inventing a SpecRef error.  A free
  proposition asserting that K67 returned a value in 0..3 would be an
  assumption about a machine result, not an input-domain restriction; this
  module does not use that added-premise trap.
-/

import EvmAsm.Codegen.Programs.ValidateHeaderCompose
import EvmAsm.Codegen.Programs.HeaderValidatePostMergeFinal
import EvmAsm.Stateless.SpecRef.SeamShell

namespace EvmAsm.Codegen.ValidateHeaderWhole

open EvmAsm EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.ValidateHeaderCorrespondence
open EvmAsm.Codegen.ValidateHeaderCompose
open EvmAsm.Codegen.ValidateHeaderInlineArms
open EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec

abbrev H : Word := ValidateHeaderCorrespondence.H
abbrev callerCode : CodeReq := ValidateHeaderCorrespondence.callerCode

/-! ## Total machine-result description

For inputs on which the K67 post-merge guard holds, statuses 0--11 carry the
corresponding `SpecRef.validate_header` result.  When that guard fails, the
guest instead rejects with status 12 and the post records the concrete
`k67GuardFail` predicate.  Thus this is a total description of the guest's
thirteen exits, not a claim that every guest rejection is a result in the
`SpecRef.validate_header` result space. -/

def validateHeaderStatusResult
    (parent header : EvmAsm.Stateless.SpecRef.Header) (status headerPtr : Word)
    (rawBytes : List (BitVec 8)) : Prop :=
  (status = 0 ∧
      EvmAsm.Stateless.SpecRef.validate_header parent header = .ok ()) ∨
  (status = 1 ∧
      EvmAsm.Stateless.SpecRef.validate_header parent header =
        .error (.invalidBlock "block number < 1")) ∨
  (status = 2 ∧
      EvmAsm.Stateless.SpecRef.validate_header parent header =
        .error (.invalidBlock "excess blob gas mismatch")) ∨
  (status = 3 ∧
      EvmAsm.Stateless.SpecRef.validate_header parent header =
        .error (.invalidBlock "gas used exceeds limit")) ∨
  (status = 4 ∧ ∃ why : String,
      (why = "gas limit out of bounds" ∨ why = "base fee mismatch") ∧
      EvmAsm.Stateless.SpecRef.validate_header parent header =
        .error (.invalidBlock why)) ∨
  (status = 5 ∧
      EvmAsm.Stateless.SpecRef.validate_header parent header =
        .error (.invalidBlock "timestamp not after parent")) ∨
  (status = 6 ∧
      EvmAsm.Stateless.SpecRef.validate_header parent header =
        .error (.invalidBlock "block number not parent + 1")) ∨
  (status = 7 ∧
      EvmAsm.Stateless.SpecRef.validate_header parent header =
        .error (.invalidBlock "extra data too long")) ∨
  (status = 8 ∧
      EvmAsm.Stateless.SpecRef.validate_header parent header =
        .error (.invalidBlock "difficulty nonzero")) ∨
  (status = 9 ∧
      EvmAsm.Stateless.SpecRef.validate_header parent header =
        .error (.invalidBlock "nonce nonzero")) ∨
  (status = 10 ∧
      EvmAsm.Stateless.SpecRef.validate_header parent header =
        .error (.invalidBlock "ommers hash not empty")) ∨
  (status = 11 ∧
      EvmAsm.Stateless.SpecRef.validate_header parent header =
        .error (.invalidBlock "parent hash mismatch")) ∨
  (status = 12 ∧
    ∃ hoff : 0 < rawBytes.length, k67GuardFail headerPtr rawBytes hoff)

/-! `decode_header_inv` is the port's existing raw-to-model interface.  The
status 7--10 arms are the four paths that read fields which are not stored in
the 144-byte core record (`extraData`, `difficulty`, `nonce`, and `ommersHash`).
Keep the decoder inversion as a *projection* of that existing theorem: this
is not a second raw-to-header relation.  The arity and index inequalities are
included so the projection is valid for both the 23-field current-fork arm
and the 21-field previous-fork arm. -/

def validateHeaderStatusDecodeFacts
    (status : Word) (rawBytes : List (BitVec 8))
    (headerSpec : EvmAsm.Stateless.SpecRef.Header) : Prop :=
  (status = 7 ∨ status = 8 ∨ status = 9 ∨ status = 10) →
    ∃ (items : List EvmAsm.EL.RLP.RLPItem)
      (bs : List EvmAsm.Stateless.SpecRef.Bytes),
      EvmAsm.EL.RLP.decodeFully rawBytes = some (EvmAsm.EL.RLP.RLPItem.list items) ∧
      bs.length = items.length ∧
      (bs.length = 23 ∨ bs.length = 21) ∧
      1 < bs.length ∧ 7 < bs.length ∧ 12 < bs.length ∧ 14 < bs.length ∧
      headerSpec.extraData = bs.getD 12 [] ∧
      headerSpec.difficulty = EvmAsm.Stateless.SpecRef.bytesBEtoNat (bs.getD 7 []) ∧
      headerSpec.nonce = bs.getD 14 [] ∧
      headerSpec.ommersHash = bs.getD 1 []

open EvmAsm.Stateless.SpecRef in
/-- Project the existing successful-decoder inversion to the four status-arm
fields.  In particular, no 23-field-only indexing is assumed: `mkHeaderFields`
uses positions 1/7/12/14 in both accepted arities, and the bounds below are
derived from the disjunction supplied by `decode_header_inv`. -/
theorem validateHeaderStatusDecodeFacts_of_decode
    {status : Word} {rawBytes : Bytes} {headerSpec : Header}
    (hdec : _decode_header rawBytes = .ok headerSpec) :
    validateHeaderStatusDecodeFacts status rawBytes headerSpec := by
  intro _
  obtain ⟨items, bs, hfull, hlen, harity, -, hfields, -, -⟩ := decode_header_inv hdec
  have h1 : 1 < bs.length := by
    rcases harity with h23 | h21 <;> omega
  have h7 : 7 < bs.length := by
    rcases harity with h23 | h21 <;> omega
  have h12 : 12 < bs.length := by
    rcases harity with h23 | h21 <;> omega
  have h14 : 14 < bs.length := by
    rcases harity with h23 | h21 <;> omega
  refine ⟨items, bs, hfull, hlen, harity, h1, h7, h12, h14, ?_, ?_, ?_, ?_⟩
  · rw [hfields]
    rfl
  · rw [hfields]
    rfl
  · rw [hfields]
    rfl
  · rw [hfields]
    rfl

/-- Concrete inhabitant for the guest-only status-12 predicate.  A one-byte
    window whose first byte is not an RLP list prefix takes the init-failure
    arm, so this is a genuine machine-visible K67 failure rather than a
    syntactic proposition that happens to be satisfiable. -/
theorem k67GuardFail_constructive_witness :
    k67GuardFail (0 : Word) ([0] : List (BitVec 8)) (by decide) := by
  unfold k67GuardFail k67InitFailedPure
  exact Or.inr (Or.inr (Or.inl (by decide)))

/-- A non-degenerate companion: `0xc1` declares a one-byte short list in a
    one-byte window, so the init content-end check fails. -/
theorem k67GuardFail_nonzero_constructive_witness :
    k67GuardFail (0 : Word) ([0xc1] : List (BitVec 8)) (by decide) := by
  unfold k67GuardFail k67InitFailedPure
  exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))

/-! The decoder writes a fixed 144-byte header record: the six 8-byte scalar
    fields are little-endian, while the 32-byte U256 base-fee field is
    big-endian.  The core contract owns those decoded records rather than
    treating the memory behind `x18`/`x19` as an unconstrained implementation
    detail.  The raw-byte relation deliberately uses the existing SpecRef
    decoder result, rather than authoring a second encoder/decoder tie; callers
    can consume `decode_header_inv` to obtain the canonical field facts. -/

def headerCoreStructBytes
    (h : EvmAsm.Stateless.SpecRef.Header) : List (BitVec 8) :=
  h.parentHash ++ h.stateRoot ++
    EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.number ++
    EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.timestamp ++
    EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasLimit ++
    EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasUsed ++
    EvmAsm.Stateless.SpecRef.natToBytesBE 32 h.baseFeePerGas ++
    EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.blobGasUsed ++
    EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.excessBlobGas

def headerCoreStructRelation
    (structBytes : List (BitVec 8))
    (h : EvmAsm.Stateless.SpecRef.Header) : Prop :=
  structBytes.length = 144 ∧ structBytes = headerCoreStructBytes h

/-- The byte-level header resource is tied to the successful SpecRef decoder
    result represented by the machine record.  This is the existing
    `decode_header_inv` interface; it exposes the arity, item bytes, canonical
    numeric fields and fixed-width fields needed by the status arms without
    introducing a parallel raw-to-model theorem. -/

def validateHeaderCoreFrame
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (headerPtr parentRlpPtr headerLen parentRlpLen : Word)
    (rawBytes parentRawBytes : List (BitVec 8))
    (thisStruct parentStructPtr : Word)
    (headerStruct parentStruct : List (BitVec 8)) : Assertion :=
  bytesRegion headerPtr rawBytes ** bytesRegion parentRlpPtr parentRawBytes **
  bytesRegion thisStruct headerStruct ** bytesRegion parentStructPtr parentStruct **
  ⌜rawBytes.length = headerLen ∧ parentRawBytes.length = parentRlpLen ∧
    EvmAsm.Stateless.SpecRef._decode_header rawBytes = .ok headerSpec ∧
    EvmAsm.Stateless.SpecRef._decode_header parentRawBytes = .ok parentSpec ∧
    headerCoreStructRelation headerStruct headerSpec ∧
    headerCoreStructRelation parentStruct parentSpec⌝

def validateHeaderCorePre
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (spC raIn header headerLen : Word)
    (rawBytes parentRawBytes : List (BitVec 8))
    (thisStruct parentStructPtr parentRlpPtr parentRlpLen : Word)
    (headerStruct parentStruct : List (BitVec 8))
    (o8 o9 o18 o19 o20 o21 : Word) (G : Assertion) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ header) ** (.x9 ↦ᵣ headerLen) **
  (.x18 ↦ᵣ thisStruct) ** (.x19 ↦ᵣ parentStructPtr) **
  (.x20 ↦ᵣ parentRlpPtr) ** (.x21 ↦ᵣ parentRlpLen) **
  (.x10 ↦ᵣ header) ** (.x11 ↦ᵣ headerLen) **
  (.x12 ↦ᵣ thisStruct) ** (.x13 ↦ᵣ parentStructPtr) **
  (.x14 ↦ᵣ parentRlpPtr) ** (.x15 ↦ᵣ parentRlpLen) **
  (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ o8) ** ((spC + 16) ↦ₘ o9) **
  ((spC + 24) ↦ₘ o18) ** ((spC + 32) ↦ₘ o19) **
  ((spC + 40) ↦ₘ o20) ** ((spC + 48) ↦ₘ o21) **
  validateHeaderCoreFrame parentSpec headerSpec header parentRlpPtr headerLen parentRlpLen
    rawBytes parentRawBytes thisStruct parentStructPtr headerStruct parentStruct ** G

def validateHeaderCorePost
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header) (status : Word)
    (spC raIn headerPtr headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen : Word)
    (rawBytes parentRawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (o1 o8 o9 o18 o19 o20 o21 : Word) (G : Assertion) : Assertion :=
  (.x10 ↦ᵣ status) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
  (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) **
  (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
  (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ o8) ** ((spC + 16) ↦ₘ o9) **
  ((spC + 24) ↦ₘ o18) ** ((spC + 32) ↦ₘ o19) **
  ((spC + 40) ↦ₘ o20) ** ((spC + 48) ↦ₘ o21) **
  validateHeaderCoreFrame parentSpec headerSpec headerPtr parentRlpPtr headerLen parentRlpLen
    rawBytes parentRawBytes thisStruct parentStructPtr headerStruct parentStruct **
  ⌜validateHeaderStatusResult parentSpec headerSpec status headerPtr rawBytes⌝ ** G

def validateHeaderFinalPost
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (sp0 spC raIn headerPtr headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen : Word)
    (rawBytes parentRawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (o8 o9 o18 o19 o20 o21 : Word)
    (G : Assertion) : Assertion := fun s =>
  ∃ status : Word,
    (((.x10 ↦ᵣ status) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
      (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) **
      (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ o8) ** ((spC + 16) ↦ₘ o9) **
      ((spC + 24) ↦ₘ o18) ** ((spC + 32) ↦ₘ o19) **
      ((spC + 40) ↦ₘ o20) ** ((spC + 48) ↦ₘ o21) **
      validateHeaderCoreFrame parentSpec headerSpec headerPtr parentRlpPtr headerLen parentRlpLen
        rawBytes parentRawBytes thisStruct parentStructPtr headerStruct parentStruct **
      ⌜validateHeaderStatusResult parentSpec headerSpec status headerPtr rawBytes⌝ ** G) **
      ⌜validateHeaderStatusDecodeFacts status rawBytes headerSpec⌝) s

def validateHeaderCoreExits
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (spC raIn headerPtr headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen : Word)
    (rawBytes parentRawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (o1 o8 o9 o18 o19 o20 o21 : Word)
    (G : Assertion) : List (Word × Assertion) :=
  [ (H + 352, validateHeaderCorePost parentSpec headerSpec 0 spC raIn
        headerPtr headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 1 spC raIn
        headerPtr headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 2 spC raIn
        headerPtr headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 3 spC raIn
        headerPtr headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 4 spC raIn
        headerPtr headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 5 spC raIn
        headerPtr headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 6 spC raIn
        headerPtr headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 7 spC raIn
        headerPtr headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 8 spC raIn
        headerPtr headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 9 spC raIn
        headerPtr headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 10 spC raIn
        headerPtr headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 11 spC raIn
        headerPtr headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 12 spC raIn
        headerPtr headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G) ]

/-! This is deliberately a named remaining premise rather than an axiom-like
 theorem. It is the route that must consume all thirteen status exits.  The
 status-12 exit is not hidden behind a range assumption: its post carries the
 K67 arm-4 `k67GuardFail` predicate. -/
abbrev validateHeaderCoreContract
    (nCore : Nat) (cr : CodeReq)
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen : Word)
    (rawBytes parentRawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (o1 o8 o9 o18 o19 o20 o21 : Word) (G : Assertion) : Prop :=
  cpsNBranchWithin nCore (H + 56) cr
    (validateHeaderCorePre parentSpec headerSpec spC raIn header headerLen
      rawBytes parentRawBytes thisStruct parentStructPtr parentRlpPtr parentRlpLen
      headerStruct parentStruct
      o8 o9 o18 o19 o20 o21 G)
    (validateHeaderCoreExits parentSpec headerSpec spC raIn header headerLen thisStruct
      parentStructPtr parentRlpPtr parentRlpLen rawBytes parentRawBytes headerStruct parentStruct
      o1 o8 o9 o18 o19 o20 o21 G)

theorem validateHeader_epilogue_for_status
    {cr : CodeReq} (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (sp0 spC raIn headerPtr headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen : Word)
    (rawBytes parentRawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (o1 o8 o9 o18 o19 o20 o21 status : Word)
    (G : Assertion) (hG : G.pcFree)
    (hdecode : EvmAsm.Stateless.SpecRef._decode_header rawBytes = .ok headerSpec)
    (hcaller : ∀ a i, callerCode a = some i → cr a = some i)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 9 (H + 352) raIn cr
      (validateHeaderCorePost parentSpec headerSpec status spC raIn headerPtr headerLen
        thisStruct parentStructPtr parentRlpPtr parentRlpLen rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G)
      (validateHeaderFinalPost parentSpec headerSpec sp0 spC raIn headerPtr headerLen
        thisStruct parentStructPtr parentRlpPtr parentRlpLen rawBytes parentRawBytes headerStruct parentStruct
        o8 o9 o18 o19 o20 o21 G) := by
  have hepi := vhEpi sp0 spC raIn o8 o9 o18 o19 o20 o21
    o1 o8 o9 o18 o19 o20 o21 hspC hret
  have hepiC := cpsTripleWithin_extend_code hcaller hepi
  have hdecodeFacts := validateHeaderStatusDecodeFacts_of_decode (status := status) hdecode
  have hframe : ((.x10 ↦ᵣ status) **
      validateHeaderCoreFrame parentSpec headerSpec headerPtr parentRlpPtr headerLen parentRlpLen
        rawBytes parentRawBytes thisStruct parentStructPtr headerStruct parentStruct **
      ⌜validateHeaderStatusResult parentSpec headerSpec status headerPtr rawBytes⌝ ** G).pcFree := by
    repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_pure |
      exact bytesRegion_pcFree _ _ | exact hG
  have hfr := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ status) **
      validateHeaderCoreFrame parentSpec headerSpec headerPtr parentRlpPtr headerLen parentRlpLen
        rawBytes parentRawBytes thisStruct parentStructPtr headerStruct parentStruct **
      ⌜validateHeaderStatusResult parentSpec headerSpec status headerPtr rawBytes⌝ ** G)
    hframe hepiC
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      unfold validateHeaderCorePost at hp
      unfold validateHeaderCoreFrame at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      unfold validateHeaderFinalPost
      refine ⟨status, ?_⟩
      unfold validateHeaderCoreFrame at hq ⊢
      have hq' := (sepConj_pure_right _).2 ⟨hq, hdecodeFacts⟩
      xperm_hyp hq')
    hfr

set_option maxRecDepth 8000 in
/-- Compose the prologue, all thirteen core exits, and the common epilogue.

The first twelve exits correspond to `SpecRef.validate_header` results.  The
thirteenth is the guest-only K67 guard-failure rejection (status 12), whose
input predicate is retained in `validateHeaderStatusResult`; it is not a
false-reject claim about the reference, whose result type has no status 12.
-/
theorem validate_header_cps_compose
    {cr : CodeReq} {nCore : Nat}
    (sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen : Word)
    (o1 o8 o9 o18 o19 o20 o21 : Word)
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (rawBytes parentRawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (G : Assertion) (hG : G.pcFree)
    (hdecode : EvmAsm.Stateless.SpecRef._decode_header rawBytes = .ok headerSpec)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hcaller : ∀ a i, callerCode a = some i → cr a = some i)
    (hcore : cpsNBranchWithin nCore (H + 56) cr
      (validateHeaderCorePre parentSpec headerSpec spC raIn header headerLen
        rawBytes parentRawBytes thisStruct parentStructPtr parentRlpPtr parentRlpLen
        headerStruct parentStruct
        o8 o9 o18 o19 o20 o21 G)
      (validateHeaderCoreExits parentSpec headerSpec spC raIn header headerLen thisStruct
        parentStructPtr parentRlpPtr parentRlpLen rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G)) :
    cpsTripleWithin (14 + nCore + 9) H raIn cr
      ((regIs .x1 raIn) ** (regIs .x2 sp0) **
        (regIs .x8 o8) ** (regIs .x9 o9) ** (regIs .x18 o18) **
        (regIs .x19 o19) ** (regIs .x20 o20) ** (regIs .x21 o21) **
        (regIs .x10 header) ** (regIs .x11 headerLen) **
        (regIs .x12 thisStruct) ** (regIs .x13 parentStructPtr) **
        (regIs .x14 parentRlpPtr) ** (regIs .x15 parentRlpLen) **
        memOwn spC ** memOwn (spC + 8) ** memOwn (spC + 16) **
        memOwn (spC + 24) ** memOwn (spC + 32) ** memOwn (spC + 40) **
        memOwn (spC + 48) **
        validateHeaderCoreFrame parentSpec headerSpec header parentRlpPtr headerLen parentRlpLen
          rawBytes parentRawBytes thisStruct parentStructPtr headerStruct parentStruct ** G)
      (validateHeaderFinalPost parentSpec headerSpec sp0 spC raIn header headerLen
        thisStruct parentStructPtr parentRlpPtr parentRlpLen rawBytes parentRawBytes headerStruct parentStruct
        o8 o9 o18 o19 o20 o21 G) := by
  have hcoreFrame_pcFree :
      (validateHeaderCoreFrame parentSpec headerSpec header parentRlpPtr headerLen parentRlpLen
        rawBytes parentRawBytes thisStruct parentStructPtr headerStruct parentStruct).pcFree := by
    unfold validateHeaderCoreFrame
    repeat' first | apply pcFree_sepConj | exact bytesRegion_pcFree _ _ |
      exact pcFree_pure
  have hGFrame :
      (validateHeaderCoreFrame parentSpec headerSpec header parentRlpPtr headerLen parentRlpLen
        rawBytes parentRawBytes thisStruct parentStructPtr headerStruct parentStruct ** G).pcFree :=
    pcFree_sepConj hcoreFrame_pcFree hG
  have hpro := validateHeader_prologue_spec sp0 spC raIn
    header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen o8 o9 o18 o19 o20 o21
    (validateHeaderCoreFrame parentSpec headerSpec header parentRlpPtr headerLen parentRlpLen
      rawBytes parentRawBytes thisStruct parentStructPtr headerStruct parentStruct ** G) hGFrame hspC
  have hproC := cpsTripleWithin_extend_code hcaller hpro
  have hcore' := cpsNBranchWithin_merge hcore (by
    intro exit hmem
    have hex : exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 0 spC raIn header
          headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
          rawBytes parentRawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 1 spC raIn header
          headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
          rawBytes parentRawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 2 spC raIn header
          headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
          rawBytes parentRawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 3 spC raIn header
          headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
          rawBytes parentRawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 4 spC raIn header
          headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
          rawBytes parentRawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 5 spC raIn header
          headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
          rawBytes parentRawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 6 spC raIn header
          headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
          rawBytes parentRawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 7 spC raIn header
          headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
          rawBytes parentRawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 8 spC raIn header
          headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
          rawBytes parentRawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 9 spC raIn header
          headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
          rawBytes parentRawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 10 spC raIn header
          headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
          rawBytes parentRawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 11 spC raIn header
          headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
          rawBytes parentRawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 12 spC raIn header
          headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
          rawBytes parentRawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) := by
      simpa [validateHeaderCoreExits] using hmem
    rcases hex with h0 | hrest
    · rw [h0]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 0 G hG hdecode hcaller hspC hret
    rcases hrest with h1 | hrest
    · rw [h1]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 1 G hG hdecode hcaller hspC hret
    rcases hrest with h2 | hrest
    · rw [h2]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 2 G hG hdecode hcaller hspC hret
    rcases hrest with h3 | hrest
    · rw [h3]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 3 G hG hdecode hcaller hspC hret
    rcases hrest with h4 | hrest
    · rw [h4]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 4 G hG hdecode hcaller hspC hret
    rcases hrest with h5 | hrest
    · rw [h5]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 5 G hG hdecode hcaller hspC hret
    rcases hrest with h6 | hrest
    · rw [h6]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 6 G hG hdecode hcaller hspC hret
    rcases hrest with h7 | hrest
    · rw [h7]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 7 G hG hdecode hcaller hspC hret
    rcases hrest with h8 | hrest
    · rw [h8]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 8 G hG hdecode hcaller hspC hret
    rcases hrest with h9 | hrest
    · rw [h9]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 9 G hG hdecode hcaller hspC hret
    rcases hrest with h10 | hrest
    · rw [h10]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 10 G hG hdecode hcaller hspC hret
    rcases hrest with h11 | h12
    · rw [h11]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 11 G hG hdecode hcaller hspC hret
    · rw [h12]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
        rawBytes parentRawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 12 G hG hdecode hcaller hspC hret
  )
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      unfold validateHeaderCorePre
      xperm_hyp hp)
    hproC hcore'
  simpa [Nat.add_assoc] using hseq

end EvmAsm.Codegen.ValidateHeaderWhole
