/-
  EvmAsm.Codegen.Programs.ValidateHeaderWhole

  Whole-routine composition shell for `validate_header` (#12346).

  The machine route between H+56 and H+352 is supplied as an explicit
  `validateHeaderCoreExits` contract. This file does not turn that premise
  into a proof by naming it: the premise is the remaining composition work
  (the six checker/callee seams and their fall-through branches). What is
  discharged here is the ABI composition around that route, including the
  SpecRef status relation, the 56-byte prologue, and the common epilogue.
  Status 12 is intentionally uncovered here: it is the auxiliary parse/other
  arm, whereas `SpecRef.validate_header` has no status-12 result.  No
  whole-route theorem is claimed until that arm has either a named premise
  gate or a real postcondition.
-/

import EvmAsm.Codegen.Programs.ValidateHeaderCompose
import EvmAsm.Stateless.SpecRef.SeamShell

namespace EvmAsm.Codegen.ValidateHeaderWhole

open EvmAsm EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.ValidateHeaderCorrespondence
open EvmAsm.Codegen.ValidateHeaderCompose
open EvmAsm.Codegen.ValidateHeaderInlineArms

abbrev H : Word := ValidateHeaderCorrespondence.H
abbrev callerCode : CodeReq := ValidateHeaderCorrespondence.callerCode

/-! ## SpecRef status relation -/

def validateHeaderStatusResult
    (parent header : EvmAsm.Stateless.SpecRef.Header) (status : Word) : Prop :=
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
        .error (.invalidBlock "parent hash mismatch"))

def validateHeaderCorePre
    (spC raIn header headerLen parent parentLen s4 s5 : Word)
    (o8 o9 o18 o19 o20 o21 : Word) (G : Assertion) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ header) ** (.x9 ↦ᵣ headerLen) **
  (.x18 ↦ᵣ parent) ** (.x19 ↦ᵣ parentLen) **
  (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
  (.x10 ↦ᵣ header) ** (.x11 ↦ᵣ headerLen) **
  (.x12 ↦ᵣ parent) ** (.x13 ↦ᵣ parentLen) **
  (.x14 ↦ᵣ s4) ** (.x15 ↦ᵣ s5) **
  (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ o8) ** ((spC + 16) ↦ₘ o9) **
  ((spC + 24) ↦ₘ o18) ** ((spC + 32) ↦ₘ o19) **
  ((spC + 40) ↦ₘ o20) ** ((spC + 48) ↦ₘ o21) ** G

def validateHeaderCorePost
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header) (status : Word)
    (spC raIn : Word) (o1 o8 o9 o18 o19 o20 o21 : Word) (G : Assertion) : Assertion :=
  (.x10 ↦ᵣ status) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
  (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) **
  (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
  (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ o8) ** ((spC + 16) ↦ₘ o9) **
  ((spC + 24) ↦ₘ o18) ** ((spC + 32) ↦ₘ o19) **
  ((spC + 40) ↦ₘ o20) ** ((spC + 48) ↦ₘ o21) **
  ⌜validateHeaderStatusResult parentSpec headerSpec status⌝ ** G

def validateHeaderFinalPost
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (sp0 spC raIn : Word) (o8 o9 o18 o19 o20 o21 : Word)
    (G : Assertion) : Assertion := fun s =>
  ∃ status : Word,
    ((.x10 ↦ᵣ status) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
      (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) **
      (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ o8) ** ((spC + 16) ↦ₘ o9) **
      ((spC + 24) ↦ₘ o18) ** ((spC + 32) ↦ₘ o19) **
      ((spC + 40) ↦ₘ o20) ** ((spC + 48) ↦ₘ o21) **
      ⌜validateHeaderStatusResult parentSpec headerSpec status⌝ ** G) s

def validateHeaderCoreExits
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (spC raIn : Word) (o1 o8 o9 o18 o19 o20 o21 : Word)
    (G : Assertion) : List (Word × Assertion) :=
  [ (H + 352, validateHeaderCorePost parentSpec headerSpec 0 spC raIn
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 1 spC raIn
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 2 spC raIn
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 3 spC raIn
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 4 spC raIn
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 5 spC raIn
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 6 spC raIn
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 7 spC raIn
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 8 spC raIn
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 9 spC raIn
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 10 spC raIn
        o1 o8 o9 o18 o19 o20 o21 G),
    (H + 352, validateHeaderCorePost parentSpec headerSpec 11 spC raIn
        o1 o8 o9 o18 o19 o20 o21 G) ]

/-! This is deliberately a named remaining premise rather than an axiom-like
 theorem. It is the route that must consume the twelve currently modelled
 status exits.  Status 12 is an admitted uncovered exit until its K67 range
 premise or semantic post is supplied. -/
abbrev validateHeaderCoreContract
    (nCore : Nat) (cr : CodeReq)
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (spC raIn header headerLen parent parentLen s4 s5 : Word)
    (o1 o8 o9 o18 o19 o20 o21 : Word) (G : Assertion) : Prop :=
  cpsNBranchWithin nCore (H + 56) cr
    (validateHeaderCorePre spC raIn header headerLen parent parentLen s4 s5
      o8 o9 o18 o19 o20 o21 G)
    (validateHeaderCoreExits parentSpec headerSpec spC raIn
      o1 o8 o9 o18 o19 o20 o21 G)

theorem validateHeader_epilogue_for_status
    {cr : CodeReq} (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (sp0 spC raIn : Word) (o1 o8 o9 o18 o19 o20 o21 status : Word)
    (G : Assertion) (hG : G.pcFree)
    (hcaller : ∀ a i, callerCode a = some i → cr a = some i)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 9 (H + 352) raIn cr
      (validateHeaderCorePost parentSpec headerSpec status spC raIn
        o1 o8 o9 o18 o19 o20 o21 G)
      (validateHeaderFinalPost parentSpec headerSpec sp0 spC raIn
        o8 o9 o18 o19 o20 o21 G) := by
  have hepi := vhEpi sp0 spC raIn o8 o9 o18 o19 o20 o21
    o1 o8 o9 o18 o19 o20 o21 hspC hret
  have hepiC := cpsTripleWithin_extend_code hcaller hepi
  have hframe : ((.x10 ↦ᵣ status) **
      ⌜validateHeaderStatusResult parentSpec headerSpec status⌝ ** G).pcFree := by
    repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_pure | exact hG
  have hfr := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ status) ** ⌜validateHeaderStatusResult parentSpec headerSpec status⌝ ** G)
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
theorem validate_header_cps_compose
    {cr : CodeReq} {nCore : Nat}
    (sp0 spC raIn header headerLen parent parentLen s4 s5 : Word)
    (o1 o8 o9 o18 o19 o20 o21 : Word)
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hcaller : ∀ a i, callerCode a = some i → cr a = some i)
    (hcore : cpsNBranchWithin nCore (H + 56) cr
      (validateHeaderCorePre spC raIn header headerLen parent parentLen s4 s5
        o8 o9 o18 o19 o20 o21 G)
      (validateHeaderCoreExits parentSpec headerSpec spC raIn
        o1 o8 o9 o18 o19 o20 o21 G)) :
    cpsTripleWithin (14 + nCore + 9) H raIn cr
      ((regIs .x1 raIn) ** (regIs .x2 sp0) **
        (regIs .x8 o8) ** (regIs .x9 o9) ** (regIs .x18 o18) **
        (regIs .x19 o19) ** (regIs .x20 o20) ** (regIs .x21 o21) **
        (regIs .x10 header) ** (regIs .x11 headerLen) **
        (regIs .x12 parent) ** (regIs .x13 parentLen) **
        (regIs .x14 s4) ** (regIs .x15 s5) **
        memOwn spC ** memOwn (spC + 8) ** memOwn (spC + 16) **
        memOwn (spC + 24) ** memOwn (spC + 32) ** memOwn (spC + 40) **
        memOwn (spC + 48) ** G)
      (validateHeaderFinalPost parentSpec headerSpec sp0 spC raIn
        o8 o9 o18 o19 o20 o21 G) := by
  have hpro := validateHeader_prologue_spec sp0 spC raIn
    header headerLen parent parentLen s4 s5 o8 o9 o18 o19 o20 o21 G
    hG hspC
  have hproC := cpsTripleWithin_extend_code hcaller hpro
  have hcore' := cpsNBranchWithin_merge hcore (by
    intro exit hmem
    have hex : exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 0 spC raIn
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 1 spC raIn
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 2 spC raIn
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 3 spC raIn
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 4 spC raIn
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 5 spC raIn
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 6 spC raIn
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 7 spC raIn
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 8 spC raIn
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 9 spC raIn
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 10 spC raIn
          o1 o8 o9 o18 o19 o20 o21 G) ∨
      exit = (H + 352,
        validateHeaderCorePost parentSpec headerSpec 11 spC raIn
          o1 o8 o9 o18 o19 o20 o21 G) := by
      simpa [validateHeaderCoreExits] using hmem
    rcases hex with h0 | hrest
    · rw [h0]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn o1 o8 o9 o18 o19 o20 o21 0 G hG hcaller hspC hret
    rcases hrest with h1 | hrest
    · rw [h1]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn o1 o8 o9 o18 o19 o20 o21 1 G hG hcaller hspC hret
    rcases hrest with h2 | hrest
    · rw [h2]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn o1 o8 o9 o18 o19 o20 o21 2 G hG hcaller hspC hret
    rcases hrest with h3 | hrest
    · rw [h3]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn o1 o8 o9 o18 o19 o20 o21 3 G hG hcaller hspC hret
    rcases hrest with h4 | hrest
    · rw [h4]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn o1 o8 o9 o18 o19 o20 o21 4 G hG hcaller hspC hret
    rcases hrest with h5 | hrest
    · rw [h5]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn o1 o8 o9 o18 o19 o20 o21 5 G hG hcaller hspC hret
    rcases hrest with h6 | hrest
    · rw [h6]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn o1 o8 o9 o18 o19 o20 o21 6 G hG hcaller hspC hret
    rcases hrest with h7 | hrest
    · rw [h7]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn o1 o8 o9 o18 o19 o20 o21 7 G hG hcaller hspC hret
    rcases hrest with h8 | hrest
    · rw [h8]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn o1 o8 o9 o18 o19 o20 o21 8 G hG hcaller hspC hret
    rcases hrest with h9 | hrest
    · rw [h9]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn o1 o8 o9 o18 o19 o20 o21 9 G hG hcaller hspC hret
    rcases hrest with h10 | hrest
    · rw [h10]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn o1 o8 o9 o18 o19 o20 o21 10 G hG hcaller hspC hret
    · rw [hrest]
      exact validateHeader_epilogue_for_status parentSpec headerSpec
        sp0 spC raIn o1 o8 o9 o18 o19 o20 o21 11 G hG hcaller hspC hret
  )
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      unfold validateHeaderCorePre
      xperm_hyp hp)
    hproC hcore'
  simpa [Nat.add_assoc] using hseq

end EvmAsm.Codegen.ValidateHeaderWhole
