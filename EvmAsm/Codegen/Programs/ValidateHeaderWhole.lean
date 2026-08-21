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

/-! The decoder writes a fixed 144-byte little-endian header record.  The
    core contract owns those decoded records rather than treating the memory
    behind `x18`/`x19` as an unconstrained implementation detail.  The
    relation is deliberately explicit: the bytes are one physical resource,
    and the pure fact ties that resource to the corresponding SpecRef value. -/

def headerCoreStructBytes
    (h : EvmAsm.Stateless.SpecRef.Header) : List (BitVec 8) :=
  h.parentHash ++ h.stateRoot ++
    EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.number ++
    EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.timestamp ++
    EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasLimit ++
    EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.gasUsed ++
    EvmAsm.Stateless.SpecRef.natToBytesLE 32 h.baseFeePerGas ++
    EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.blobGasUsed ++
    EvmAsm.Stateless.SpecRef.natToBytesLE 8 h.excessBlobGas

def headerCoreStructRelation
    (structBytes : List (BitVec 8))
    (h : EvmAsm.Stateless.SpecRef.Header) : Prop :=
  structBytes.length = 144 ∧ structBytes = headerCoreStructBytes h

def validateHeaderCoreFrame
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (thisStruct parentStructPtr : Word)
    (headerStruct parentStruct : List (BitVec 8)) : Assertion :=
  bytesRegion thisStruct headerStruct ** bytesRegion parentStructPtr parentStruct **
  ⌜headerCoreStructRelation headerStruct headerSpec ∧
    headerCoreStructRelation parentStruct parentSpec⌝

def validateHeaderCorePre
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen : Word)
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
  validateHeaderCoreFrame parentSpec headerSpec thisStruct parentStructPtr
    headerStruct parentStruct ** G

def validateHeaderCorePost
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header) (status : Word)
    (spC raIn headerPtr thisStruct parentStructPtr : Word)
    (rawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (o1 o8 o9 o18 o19 o20 o21 : Word) (G : Assertion) : Assertion :=
  (.x10 ↦ᵣ status) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
  (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) **
  (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
  (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ o8) ** ((spC + 16) ↦ₘ o9) **
  ((spC + 24) ↦ₘ o18) ** ((spC + 32) ↦ₘ o19) **
  ((spC + 40) ↦ₘ o20) ** ((spC + 48) ↦ₘ o21) **
  validateHeaderCoreFrame parentSpec headerSpec thisStruct parentStructPtr
    headerStruct parentStruct **
  ⌜validateHeaderStatusResult parentSpec headerSpec status headerPtr rawBytes⌝ ** G

def validateHeaderFinalPost
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (sp0 spC raIn headerPtr thisStruct parentStructPtr : Word)
    (rawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (o8 o9 o18 o19 o20 o21 : Word)
    (G : Assertion) : Assertion := fun s =>
  ∃ status : Word,
    ((.x10 ↦ᵣ status) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
      (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) **
      (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ o8) ** ((spC + 16) ↦ₘ o9) **
      ((spC + 24) ↦ₘ o18) ** ((spC + 32) ↦ₘ o19) **
      ((spC + 40) ↦ₘ o20) ** ((spC + 48) ↦ₘ o21) **
      validateHeaderCoreFrame parentSpec headerSpec thisStruct parentStructPtr
        headerStruct parentStruct **
      ⌜validateHeaderStatusResult parentSpec headerSpec status headerPtr rawBytes⌝ ** G) s

def validateHeaderCoreExits
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (spC raIn headerPtr thisStruct parentStructPtr : Word)
    (rawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (o1 o8 o9 o18 o19 o20 o21 : Word)
    (G : Assertion) : List (Word × Assertion) :=
  [ (H + 352, validateHeaderCorePost parentSpec headerSpec 0 spC raIn
        headerPtr thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 1 spC raIn
        headerPtr thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 2 spC raIn
        headerPtr thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 3 spC raIn
        headerPtr thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 4 spC raIn
        headerPtr thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 5 spC raIn
        headerPtr thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 6 spC raIn
        headerPtr thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 7 spC raIn
        headerPtr thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 8 spC raIn
        headerPtr thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 9 spC raIn
        headerPtr thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 10 spC raIn
        headerPtr thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 11 spC raIn
        headerPtr thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 12 spC raIn
        headerPtr thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 G) ]

/-! This is deliberately a named remaining premise rather than an axiom-like
 theorem. It is the route that must consume all thirteen status exits.  The
 status-12 exit is not hidden behind a range assumption: its post carries the
 K67 arm-4 `k67GuardFail` predicate. -/
abbrev validateHeaderCoreContract
    (nCore : Nat) (cr : CodeReq)
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen : Word)
    (rawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (o1 o8 o9 o18 o19 o20 o21 : Word) (G : Assertion) : Prop :=
  cpsNBranchWithin nCore (H + 56) cr
    (validateHeaderCorePre parentSpec headerSpec spC raIn header headerLen
      thisStruct parentStructPtr parentRlpPtr parentRlpLen headerStruct parentStruct
      o8 o9 o18 o19 o20 o21 G)
    (validateHeaderCoreExits parentSpec headerSpec spC raIn header thisStruct parentStructPtr
      rawBytes headerStruct parentStruct o1 o8 o9 o18 o19 o20 o21 G)

theorem validateHeader_epilogue_for_status
    {cr : CodeReq} (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (sp0 spC raIn headerPtr thisStruct parentStructPtr : Word)
    (rawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (o1 o8 o9 o18 o19 o20 o21 status : Word)
    (G : Assertion) (hG : G.pcFree)
    (hcaller : ∀ a i, callerCode a = some i → cr a = some i)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 9 (H + 352) raIn cr
      (validateHeaderCorePost parentSpec headerSpec status spC raIn headerPtr thisStruct parentStructPtr
        rawBytes headerStruct parentStruct o1 o8 o9 o18 o19 o20 o21 G)
      (validateHeaderFinalPost parentSpec headerSpec sp0 spC raIn headerPtr thisStruct parentStructPtr
        rawBytes headerStruct parentStruct o8 o9 o18 o19 o20 o21 G) := by
  have hepi := vhEpi sp0 spC raIn o8 o9 o18 o19 o20 o21
    o1 o8 o9 o18 o19 o20 o21 hspC hret
  have hepiC := cpsTripleWithin_extend_code hcaller hepi
  have hframe : ((.x10 ↦ᵣ status) **
      validateHeaderCoreFrame parentSpec headerSpec thisStruct parentStructPtr
        headerStruct parentStruct **
      ⌜validateHeaderStatusResult parentSpec headerSpec status headerPtr rawBytes⌝ ** G).pcFree := by
    repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_pure |
      exact bytesRegion_pcFree _ _ | exact hG
  have hfr := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ status) **
      validateHeaderCoreFrame parentSpec headerSpec thisStruct parentStructPtr
        headerStruct parentStruct **
      ⌜validateHeaderStatusResult parentSpec headerSpec status headerPtr rawBytes⌝ ** G)
    hframe hepiC
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      unfold validateHeaderCorePost at hp
      xperm_hyp hp)
    (fun _ hq => by
      unfold validateHeaderFinalPost
      refine ⟨status, ?_⟩
      xperm_hyp hq)
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
    (rawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hcaller : ∀ a i, callerCode a = some i → cr a = some i)
    (hcore : cpsNBranchWithin nCore (H + 56) cr
      (validateHeaderCorePre parentSpec headerSpec spC raIn header headerLen
        thisStruct parentStructPtr parentRlpPtr parentRlpLen headerStruct parentStruct
        o8 o9 o18 o19 o20 o21 G)
      (validateHeaderCoreExits parentSpec headerSpec spC raIn header thisStruct parentStructPtr
        rawBytes headerStruct parentStruct o1 o8 o9 o18 o19 o20 o21 G)) :
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
        validateHeaderCoreFrame parentSpec headerSpec thisStruct parentStructPtr
          headerStruct parentStruct ** G)
      (validateHeaderFinalPost parentSpec headerSpec sp0 spC raIn header thisStruct parentStructPtr
        rawBytes headerStruct parentStruct o8 o9 o18 o19 o20 o21 G) := by
  have hcoreFrame_pcFree :
      (validateHeaderCoreFrame parentSpec headerSpec thisStruct parentStructPtr
        headerStruct parentStruct).pcFree := by
    unfold validateHeaderCoreFrame
    repeat' first | apply pcFree_sepConj | exact bytesRegion_pcFree _ _ |
      exact pcFree_pure
  have hGFrame :
      (validateHeaderCoreFrame parentSpec headerSpec thisStruct parentStructPtr
        headerStruct parentStruct ** G).pcFree :=
    pcFree_sepConj hcoreFrame_pcFree hG
  have hpro := validateHeader_prologue_spec sp0 spC raIn
    header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen o8 o9 o18 o19 o20 o21
    (validateHeaderCoreFrame parentSpec headerSpec thisStruct parentStructPtr
      headerStruct parentStruct ** G) hGFrame hspC
  have hproC := cpsTripleWithin_extend_code hcaller hpro
  have hcore' := cpsNBranchWithin_merge hcore (by
    intro exit hmem
    have hex : exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 0 spC raIn header thisStruct parentStructPtr
          rawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 1 spC raIn header thisStruct parentStructPtr
          rawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 2 spC raIn header thisStruct parentStructPtr
          rawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 3 spC raIn header thisStruct parentStructPtr
          rawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 4 spC raIn header thisStruct parentStructPtr
          rawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 5 spC raIn header thisStruct parentStructPtr
          rawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 6 spC raIn header thisStruct parentStructPtr
          rawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 7 spC raIn header thisStruct parentStructPtr
          rawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 8 spC raIn header thisStruct parentStructPtr
          rawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 9 spC raIn header thisStruct parentStructPtr
          rawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 10 spC raIn header thisStruct parentStructPtr
          rawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 11 spC raIn header thisStruct parentStructPtr
          rawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 12 spC raIn header thisStruct parentStructPtr
          rawBytes headerStruct parentStruct
          o1 o8 o9 o18 o19 o20 o21 G) := by
      simpa [validateHeaderCoreExits] using hmem
    rcases hex with h0 | hrest
    · rw [h0]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 0 G hG hcaller hspC hret
    rcases hrest with h1 | hrest
    · rw [h1]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 1 G hG hcaller hspC hret
    rcases hrest with h2 | hrest
    · rw [h2]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 2 G hG hcaller hspC hret
    rcases hrest with h3 | hrest
    · rw [h3]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 3 G hG hcaller hspC hret
    rcases hrest with h4 | hrest
    · rw [h4]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 4 G hG hcaller hspC hret
    rcases hrest with h5 | hrest
    · rw [h5]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 5 G hG hcaller hspC hret
    rcases hrest with h6 | hrest
    · rw [h6]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 6 G hG hcaller hspC hret
    rcases hrest with h7 | hrest
    · rw [h7]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 7 G hG hcaller hspC hret
    rcases hrest with h8 | hrest
    · rw [h8]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 8 G hG hcaller hspC hret
    rcases hrest with h9 | hrest
    · rw [h9]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 9 G hG hcaller hspC hret
    rcases hrest with h10 | hrest
    · rw [h10]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 10 G hG hcaller hspC hret
    rcases hrest with h11 | h12
    · rw [h11]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 11 G hG hcaller hspC hret
    · rw [h12]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn header thisStruct parentStructPtr rawBytes headerStruct parentStruct
        o1 o8 o9 o18 o19 o20 o21 12 G hG hcaller hspC hret
  )
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      unfold validateHeaderCorePre
      xperm_hyp hp)
    hproC hcore'
  simpa [Nat.add_assoc] using hseq

end EvmAsm.Codegen.ValidateHeaderWhole
