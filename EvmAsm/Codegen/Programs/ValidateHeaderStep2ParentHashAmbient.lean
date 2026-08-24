/-
  EvmAsm.Codegen.Programs.ValidateHeaderStep2ParentHashAmbient

  Step-2 caller plumbing for the unified parent-hash route (#12346 item 9).

  The parent-hash continuation resources are available at the whole-verdict
  entry, but x20 is not: validate_header's prologue installs x20 from the
  a4 parent-RLP argument.  This module gives that distinction a named
  assertion, carries it through the prologue, and records the status-0
  handoff obligation without pretending that the current all-exit core
  contract already supplies it.
-/

import EvmAsm.Codegen.Programs.ValidateHeaderWhole
import EvmAsm.Codegen.Programs.HeaderValidateParentHashUnifiedCover
import EvmAsm.Codegen.Programs.ValidateHeaderParentHashUnifiedRoute
import EvmAsm.Codegen.Programs.ValidateHeaderWholeWitness
import EvmAsm.Codegen.Programs.ValidateHeaderWholeStatus0Witness

namespace EvmAsm.Codegen.ValidateHeaderStep2ParentHashAmbient

open EvmAsm EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.ValidateHeaderCorrespondence
open EvmAsm.Codegen.ValidateHeaderCompose
open EvmAsm.Codegen.ValidateHeaderWhole
open EvmAsm.Codegen.HeaderValidateParentHashSpec
open EvmAsm.Codegen.Proofs

/- Reuse the concrete core-pre heap only for the joint non-vacuity check
   below.  Opening these private names does not turn the witness into a core
   execution proof. -/
open private hcoreWitnessHeap hcoreWitnessSat hcoreWitnessAssertion
  hcoreWitnessRegHeapFold
  from EvmAsm.Codegen.Programs.ValidateHeaderWholeWitness

noncomputable section

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _
      | exact pcFree_stackFree _ _
      | exact pcFree_regOwns _)

/-- The stack cells reserved for the keccak child are below the prologue
    frame.  At entry `sp0` is live; after the prologue `spC = sp0 - 56`, so
    this is `spC - 32`, the child frame base used by the parent-hash route. -/
abbrev step2ParentHashChildSp (sp0 : Word) : Word :=
  sp0 + signExtend12 (-88 : BitVec 12)

/-- Resources which the all-exit core may safely carry.

    This is intentionally *not* the complete route carrier.  x14/x15 are
    caller-saved scratch registers (the extra-data callee uses a4/x14), and
    the child stack is consumed by the route's own frame.  Neither is put in
    the generic all-thirteen-exit `G`, so the core precondition cannot be
    made unsatisfiable by overlapping its x14/x15 `regIs` atoms.  The
    status-0 handoff below adds those route-local resources explicitly. -/
def step2ParentHashAmbient
    (_sp0 : Word) (C0 os out0 : List (BitVec 8)) (F : Assertion) : Assertion :=
  claimedOwn C0 **
  regOwns [.x16, .x17] **
  bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
  bytesRegion Computed out0 ** F

/-! The core precondition's existing witness does not own x16/x17.  The
    following small syntactic lemmas make that fact explicit rather than
    relying on the private shape of `ValidateHeaderWholeWitness`: every
    register atom in `validateHeaderCorePre` is one of x1..x15, while its
    memory and pure atoms carry no registers. -/

private def step2NoReg (r : Reg) (P : Assertion) : Prop :=
  ∀ h, P h → h.regs r = none

private theorem step2NoReg_sep {r : Reg} {P Q : Assertion}
    (hP : step2NoReg r P) (hQ : step2NoReg r Q) :
    step2NoReg r (P ** Q) := by
  intro h hh
  rcases hh with ⟨h1, h2, hd, hu, hp, hq⟩
  rw [← hu]
  simp only [PartialState.union]
  rw [hP h1 hp, hQ h2 hq]

private theorem step2NoReg_regIs {r r' : Reg} {v : Word} (hne : r ≠ r') :
    step2NoReg r (regIs r' v) := by
  intro h hh
  rw [regIs] at hh
  subst h
  simp [PartialState.singletonReg, hne]

private theorem step2NoReg_memIs {r : Reg} {a v : Word} :
    step2NoReg r (memIs a v) := by
  intro h hh
  rw [memIs] at hh
  rcases hh with ⟨rfl, _⟩
  rfl

private theorem step2NoReg_pure {r : Reg} {P : Prop} :
    step2NoReg r (pure P) := by
  intro h hh
  exact hh.1 ▸ rfl

private theorem step2NoReg_bytesAux {r : Reg} :
    ∀ (base : Word) (n : Nat) (bs : List (BitVec 8)),
      step2NoReg r (bytesRegionAux base n bs) := by
  intro base n
  induction n generalizing base with
  | zero =>
      intro bs
      simp [bytesRegionAux, step2NoReg, empAssertion, PartialState.empty]
  | succ n ih =>
      intro bs h hh
      rcases hh with ⟨h1, h2, hd, hu, hp, hq⟩
      rw [← hu]
      simp only [PartialState.union]
      have h1r : h1.regs r = none := by
        rw [memIs] at hp
        rcases hp with ⟨rfl, _⟩
        rfl
      have h2r := ih (base + 8) (bs.drop 8) h2 hq
      rw [h1r, h2r]

private theorem step2NoReg_bytesRegion {r : Reg} {base : Word}
    {bs : List (BitVec 8)} :
    step2NoReg r (bytesRegion base bs) := by
  unfold bytesRegion
  exact step2NoReg_bytesAux base _ bs

private theorem step2NoReg_coreFrame
    {r : Reg} {parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header}
    {headerPtr parentRlpPtr headerLen parentRlpLen : Word}
    {rawBytes parentRawBytes : List (BitVec 8)}
    {thisStruct parentStructPtr : Word}
    {headerStruct parentStruct : List (BitVec 8)} :
    step2NoReg r (validateHeaderCoreFrame parentSpec headerSpec headerPtr parentRlpPtr
      headerLen parentRlpLen rawBytes parentRawBytes thisStruct parentStructPtr
      headerStruct parentStruct) := by
  unfold validateHeaderCoreFrame
  repeat first
    | apply step2NoReg_bytesRegion
    | apply step2NoReg_pure
    | apply step2NoReg_sep

private theorem step2NoReg_corePre_fresh {r : Reg}
    (hr : r = .x16 ∨ r = .x17)
    {parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header}
    {spC raIn header headerLen : Word}
    {rawBytes parentRawBytes : List (BitVec 8)}
    {thisStruct parentStructPtr parentRlpPtr parentRlpLen : Word}
    {headerStruct parentStruct : List (BitVec 8)}
    {o8 o9 o18 o19 o20 o21 : Word} {G : Assertion}
    (hG : step2NoReg r G) :
    step2NoReg r (validateHeaderCorePre parentSpec headerSpec spC raIn header headerLen
      rawBytes parentRawBytes thisStruct parentStructPtr parentRlpPtr parentRlpLen
      headerStruct parentStruct o8 o9 o18 o19 o20 o21 G) := by
  rcases hr with rfl | rfl
  unfold validateHeaderCorePre
  repeat first
    | apply step2NoReg_regIs <;> decide
    | apply step2NoReg_memIs
    | exact hG
    | apply step2NoReg_coreFrame
    | apply step2NoReg_sep

private def step2ParentHashExtraRegs : PartialState :=
  (PartialState.singletonReg .x16 0).union (PartialState.singletonReg .x17 0)

/-- The core-safe carrier is jointly satisfiable with the concrete core-pre
    witness.  In particular, adding arbitrary ownership for x16/x17 does not
    collide with the core's x1..x15 `regIs` atoms.  This is only a pre-shape
    witness: it does not assert the status-0 producer contract (item 11). -/
theorem step2ParentHashAmbient_core_pre_inhabited :
    ∃ h : PartialState,
      validateHeaderCorePre hcoreWitnessParentSpec hcoreWitnessHeaderSpec
        hcoreWitnessSpC 0 hcoreWitnessHeader hcoreWitnessHeaderRlp.length
        hcoreWitnessHeaderRlp hcoreWitnessParentRlpBytes
        hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
        hcoreWitnessParentRlpBytes.length
        hcoreWitnessHeaderStruct hcoreWitnessParentStruct
        hcoreWitnessHeader hcoreWitnessHeaderRlp.length hcoreWitnessParent
        hcoreWitnessParent2 hcoreWitnessParentRlp hcoreWitnessParentRlpBytes.length
        (step2ParentHashAmbient hcoreWitnessSp0 [] [] []
          (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes)) h := by
  obtain ⟨h0, hpre0⟩ := validateHeaderCorePre_nonempty_G
  have hno16 : step2NoReg .x16
      (validateHeaderCorePre hcoreWitnessParentSpec hcoreWitnessHeaderSpec
        hcoreWitnessSpC 0 hcoreWitnessHeader hcoreWitnessHeaderRlp.length
        hcoreWitnessHeaderRlp hcoreWitnessParentRlpBytes
        hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
        hcoreWitnessParentRlpBytes.length
        hcoreWitnessHeaderStruct hcoreWitnessParentStruct
        hcoreWitnessHeader hcoreWitnessHeaderRlp.length hcoreWitnessParent
        hcoreWitnessParent2 hcoreWitnessParentRlp hcoreWitnessParentRlpBytes.length
        (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes)) := by
    apply step2NoReg_corePre_fresh
    · exact Or.inl rfl
    exact step2NoReg_bytesRegion
  have hno17 : step2NoReg .x17
      (validateHeaderCorePre hcoreWitnessParentSpec hcoreWitnessHeaderSpec
        hcoreWitnessSpC 0 hcoreWitnessHeader hcoreWitnessHeaderRlp.length
        hcoreWitnessHeaderRlp hcoreWitnessParentRlpBytes
        hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
        hcoreWitnessParentRlpBytes.length
        hcoreWitnessHeaderStruct hcoreWitnessParentStruct
        hcoreWitnessHeader hcoreWitnessHeaderRlp.length hcoreWitnessParent
        hcoreWitnessParent2 hcoreWitnessParentRlp hcoreWitnessParentRlpBytes.length
        (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes)) := by
    apply step2NoReg_corePre_fresh
    · exact Or.inr rfl
    exact step2NoReg_bytesRegion
  have h16 := hno16 h0 hpre0
  have h17 := hno17 h0 hpre0
  have hdisj : h0.Disjoint step2ParentHashExtraRegs := by
    unfold step2ParentHashExtraRegs
    refine ⟨?_, fun _ => Or.inr rfl, fun _ => Or.inr rfl,
      Or.inr rfl, Or.inr rfl, Or.inr rfl, Or.inr rfl⟩
    intro r
    by_cases hr16 : r = .x16
    · subst r
      exact Or.inl h16
    by_cases hr17 : r = .x17
    · subst r
      exact Or.inl h17
    · exact Or.inr (by simp [PartialState.union, PartialState.singletonReg, hr16, hr17])
  have hregs : regOwns [.x16, .x17] step2ParentHashExtraRegs := by
    simp only [regOwns, sepConj_emp_right']
    unfold step2ParentHashExtraRegs
    refine ⟨PartialState.singletonReg .x16 0,
      PartialState.singletonReg .x17 0, ?_, rfl, ?_, ?_⟩
    · exact EvmAsm.Codegen.ValidateHeaderCompose.routeInhabitantRegSingletonDisjoint (by decide)
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
  have hcomb :
      (validateHeaderCorePre hcoreWitnessParentSpec hcoreWitnessHeaderSpec
        hcoreWitnessSpC 0 hcoreWitnessHeader hcoreWitnessHeaderRlp.length
        hcoreWitnessHeaderRlp hcoreWitnessParentRlpBytes
        hcoreWitnessParent hcoreWitnessParent2 hcoreWitnessParentRlp
        hcoreWitnessParentRlpBytes.length
        hcoreWitnessHeaderStruct hcoreWitnessParentStruct
        hcoreWitnessHeader hcoreWitnessHeaderRlp.length hcoreWitnessParent
        hcoreWitnessParent2 hcoreWitnessParentRlp hcoreWitnessParentRlpBytes.length
        (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) ** regOwns [.x16, .x17])
      (h0.union step2ParentHashExtraRegs) := by
    exact ⟨h0, step2ParentHashExtraRegs, hdisj, rfl, hpre0, hregs⟩
  refine ⟨h0.union step2ParentHashExtraRegs, ?_⟩
  unfold step2ParentHashAmbient claimedOwn
  simp only [bytesRegion_nil, sepConj_emp_left']
  unfold validateHeaderCorePre validateHeaderCoreFrame at hcomb ⊢
  xperm_hyp hcomb

/-- Route-local resources established at the status-0 handoff.  This is the
    exact extra shape consumed by `hvphSuccKeccakTail`; it is *not* claimed
    by the all-exit core contract. -/
def step2ParentHashRouteLocal (sp0 : Word) : Assertion :=
  stackFree (step2ParentHashChildSp sp0) 4 ** regOwns [.x14, .x15]

def step2ParentHashRouteAmbient
    (sp0 : Word) (C0 os out0 : List (BitVec 8)) (F : Assertion) : Assertion :=
  claimedOwn C0 **
  stackFree (step2ParentHashChildSp sp0) 4 **
  regOwns [.x14, .x15, .x16, .x17] **
  bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
  bytesRegion Computed out0 ** F

theorem step2ParentHashAmbient_pcFree
    (_sp0 : Word) (C0 os out0 : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree) : (step2ParentHashAmbient _sp0 C0 os out0 F).pcFree := by
  unfold step2ParentHashAmbient claimedOwn
  pcf
  exact hF

theorem step2ParentHashChildSp_eq_post_prologue
    (sp0 spC : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12)) :
    step2ParentHashChildSp sp0 =
      spC + signExtend12 (BitVec.ofNat 12 4064) := by
  have h56 : signExtend12 (-56 : BitVec 12) =
      (0xFFFFFFFFFFFFFFC8 : Word) := by decide
  have h88 : signExtend12 (-88 : BitVec 12) =
      (0xFFFFFFFFFFFFFFA8 : Word) := by decide
  have h32 : signExtend12 (BitVec.ofNat 12 4064) =
      (0xFFFFFFFFFFFFFFE0 : Word) := by decide
  simp only [step2ParentHashChildSp]
  rw [hspC, h56, h88, h32]
  bv_omega

/-- The exact precondition handed to the first checker after threading the
    Step-2 ambient.  Keeping this as a named carrier makes the later hcore
    proof consume the same assertion that the prologue theorem preserves. -/
def step2ParentHashProloguePre
    (sp0 spC raIn a0 a1 a2 a3 a4 a5 o8 o9 o18 o19 o20 o21 : Word)
    (sp2 : Word) (C0 os out0 : List (BitVec 8)) (F : Assertion) : Assertion :=
  (regIs .x1 raIn) ** (regIs .x2 sp0) **
  (regIs .x8 o8) ** (regIs .x9 o9) ** (regIs .x18 o18) **
  (regIs .x19 o19) ** (regIs .x20 o20) ** (regIs .x21 o21) **
  (regIs .x10 a0) ** (regIs .x11 a1) ** (regIs .x12 a2) **
  (regIs .x13 a3) ** (regIs .x14 a4) ** (regIs .x15 a5) **
  memOwn spC ** memOwn (spC + 8) ** memOwn (spC + 16) **
  memOwn (spC + 24) ** memOwn (spC + 32) ** memOwn (spC + 40) **
  memOwn (spC + 48) ** step2ParentHashAmbient sp2 C0 os out0 F

def step2ParentHashProloguePost
    (_sp0 spC raIn a0 a1 a2 a3 a4 a5 o8 o9 o18 o19 o20 o21 : Word)
    (sp2 : Word) (C0 os out0 : List (BitVec 8)) (F : Assertion) : Assertion :=
  (regIs .x1 raIn) ** (regIs .x2 spC) **
  (regIs .x8 a0) ** (regIs .x9 a1) ** (regIs .x18 a2) **
  (regIs .x19 a3) ** (regIs .x20 a4) ** (regIs .x21 a5) **
  (regIs .x10 a0) ** (regIs .x11 a1) ** (regIs .x12 a2) **
  (regIs .x13 a3) ** (regIs .x14 a4) ** (regIs .x15 a5) **
  (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ o8) ** ((spC + 16) ↦ₘ o9) **
  ((spC + 24) ↦ₘ o18) ** ((spC + 32) ↦ₘ o19) **
  ((spC + 40) ↦ₘ o20) ** ((spC + 48) ↦ₘ o21) **
  step2ParentHashAmbient sp2 C0 os out0 F

/-! The ambient is carried unchanged by the actual 14-step prologue.  The
    theorem is intentionally stated at the same boundary as hcore (H+56),
    rather than claiming that x20 existed at the entry point. -/
theorem validate_header_prologue_preserves_step2_parent_hash_ambient
    (sp0 spC raIn a0 a1 a2 a3 a4 a5 o8 o9 o18 o19 o20 o21 : Word)
    (sp2 : Word) (C0 os out0 : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hsp2 : sp2 = sp0) :
    cpsTripleWithin 14 ValidateHeaderWhole.H (ValidateHeaderWhole.H + 56)
      ValidateHeaderWhole.callerCode
      (step2ParentHashProloguePre sp0 spC raIn a0 a1 a2 a3 a4 a5
        o8 o9 o18 o19 o20 o21 sp2 C0 os out0 F)
      (step2ParentHashProloguePost sp0 spC raIn a0 a1 a2 a3 a4 a5
        o8 o9 o18 o19 o20 o21 sp2 C0 os out0 F) := by
  subst sp2
  have hA := step2ParentHashAmbient_pcFree sp0 C0 os out0 F hF
  have hpro := validateHeader_prologue_spec
    sp0 spC raIn a0 a1 a2 a3 a4 a5 o8 o9 o18 o19 o20 o21
    (step2ParentHashAmbient sp0 C0 os out0 F) hA hspC
  simpa only [step2ParentHashProloguePre, step2ParentHashProloguePost] using hpro

/-- The status-0 handoff needs a stronger, *specific* post than the generic
    all-exit contract: the parent-hash route consumes x14/x15 scratch and the
    four child-stack cells.  This definition deliberately exposes that
    producer obligation instead of smuggling it into the generic `G`. -/
def validateHeaderCoreStatus0PostWithStep2ParentHashAmbient
    (sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen : Word)
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (rawBytes parentRawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (o1 o8 o9 o18 o19 o20 o21 : Word)
    (C0 os out0 : List (BitVec 8)) (F : Assertion) : Assertion :=
  validateHeaderCorePost parentSpec headerSpec 0 spC raIn header headerLen
    thisStruct parentStructPtr parentRlpPtr parentRlpLen rawBytes parentRawBytes
    headerStruct parentStruct o1 o8 o9 o18 o19 o20 o21
    (step2ParentHashAmbient sp0 C0 os out0 F) **
    (step2ParentHashRouteLocal sp0)

/-- This is the explicit item-4 adapter obligation.  It is intentionally not
    derived from `validateHeaderCoreContract`: that contract has thirteen
    exits and its status-0 post does not own the route-local scratch.  A future
    core proof must instantiate this adapter from the actual status-0 path. -/
abbrev validateHeaderCoreStatus0Adapter
    (nCore : Nat) (cr : CodeReq)
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen : Word)
    (rawBytes parentRawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (o1 o8 o9 o18 o19 o20 o21 : Word)
    (C0 os out0 : List (BitVec 8)) (F : Assertion) : Prop :=
  cpsTripleWithin nCore (ValidateHeaderWhole.H + 56) (ValidateHeaderWhole.H + 352) cr
    (validateHeaderCorePre parentSpec headerSpec spC raIn header headerLen
      rawBytes parentRawBytes thisStruct parentStructPtr parentRlpPtr parentRlpLen
      headerStruct parentStruct o8 o9 o18 o19 o20 o21
      (step2ParentHashAmbient sp0 C0 os out0 F))
    (validateHeaderCoreStatus0PostWithStep2ParentHashAmbient
      sp0 spC raIn header headerLen thisStruct parentStructPtr parentRlpPtr parentRlpLen
      parentSpec headerSpec rawBytes parentRawBytes headerStruct parentStruct
      o1 o8 o9 o18 o19 o20 o21 C0 os out0 F)

/-! ## Item 4: consuming the status-0 route at its real seam

`validateHeaderCoreStatus0ProducerContract` above ends at `H + 352`, while
the parent-hash call is entered at `H + 244` (after the status-0 setup that
starts at `H + 196`).  A thirteen-exit contract whose every exit is at
`H + 352` therefore cannot select this continuation without moving the call
obligation across already-executed code.  The seam contract below makes the
missing midpoint explicit: it ends at `H + 196` and produces exactly the
precondition consumed by the unified parent-hash route.

The theorem is the consuming adapter.  It sequences that seam premise with
the existing `postMerge_status0_to_parent_hash_unified_call` theorem, which
directly consumes `validate_header_parent_hash_unified_call_spec_within` at
the `H + 244` JAL.  The seam premise remains explicit because the current
`validateHeaderCoreContract` still has thirteen `H + 352` exits; this theorem
does not claim that hcore is discharged. -/

def validateHeaderCoreStatus0SeamPost
    (spC childSp header headerLen s4 s5 oldRa : Word)
    (vals : Reg → Word)
    (thisBytes parentBytes C0 : List (BitVec 8))
    (os : List (BitVec 8)) (G : Assertion) : Assertion :=
  ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x8 ↦ᵣ header) ** (.x9 ↦ᵣ headerLen) **
    (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
    (.x13 ↦ᵣ (0 : Word)) **
    parentHashRouteFrame spC oldRa header s4 vals thisBytes parentBytes **
    claimedOwn C0 **
    hvphSuccKeccakTail childSp os (List.replicate 32 0) G)

abbrev validateHeaderCoreStatus0SeamContract
    (nCore : Nat) (cr : CodeReq)
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (spC raIn header headerLen thisStruct parentStructPtr s4 s5 : Word)
    (rawBytes parentRawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (o8 o9 o18 o19 o20 o21 : Word)
    (childSp oldRa : Word) (vals : Reg → Word)
    (thisBytes parentBytes C0 : List (BitVec 8))
    (os : List (BitVec 8)) (G : Assertion) : Prop :=
  cpsTripleWithin nCore (ValidateHeaderWhole.H + 56) (ValidateHeaderWhole.H + 196) cr
    (validateHeaderCorePre parentSpec headerSpec spC raIn header headerLen
      rawBytes parentRawBytes thisStruct parentStructPtr s4 s5
      headerStruct parentStruct o8 o9 o18 o19 o20 o21
      (step2ParentHashAmbient spC C0 os (List.replicate 32 0) G))
    (validateHeaderCoreStatus0SeamPost spC childSp header headerLen s4 s5 oldRa vals
      thisBytes parentBytes C0 os G)

set_option maxRecDepth 8000 in
theorem validateHeaderCoreStatus0_consuming_adapter
    {cr calleeCode : CodeReq} {nCore n : Nat}
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (spC childSp header headerLen s4 s5 oldRa : Word)
    (raIn thisStruct parentStructPtr : Word)
    (rawBytes parentRawBytes : List (BitVec 8))
    (headerStruct parentStruct : List (BitVec 8))
    (o8 o9 o18 o19 o20 o21 : Word)
    (vals : Reg → Word)
    (thisBytes parentBytes C0 : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree)
    (hchild : childSp = spC + signExtend12 (-32 : BitVec 12))
    (hvals8 : vals .x8 = header)
    (hvals9 : vals .x9 = headerLen)
    (hvals18 : vals .x18 = s4)
    (hseam : validateHeaderCoreStatus0SeamContract nCore cr
      parentSpec headerSpec spC raIn header headerLen thisStruct parentStructPtr s4 s5
      rawBytes parentRawBytes headerStruct parentStruct o8 o9 o18 o19 o20 o21
      childSp oldRa vals thisBytes parentBytes C0 os G)
    (hdisj : (CodeReq.singleton
      ValidateHeaderParentHashCorrespondence.A
      (.JAL .x1 (jalOff GuestAddrs.header_validate_parent_hash
        (GuestAddrs.validate_header + 244)))).Disjoint calleeCode)
    (hcallerDisj : parentHashRouteFrameCaller.Disjoint calleeCode)
    (hcode : ∀ a i, (parentHashRouteFrameCaller.union calleeCode) a = some i →
      cr a = some i)
    (hcallee : cpsTripleWithin n
      ValidateHeaderParentHashCorrespondence.Callee
      ValidateHeaderParentHashCorrespondence.Ret calleeCode
      ((.x1 ↦ᵣ ValidateHeaderParentHashCorrespondence.Ret) **
        ValidateHeaderParentHashCorrespondence.hvphEntryRest
          spC header headerLen s4 s5 vals thisBytes parentBytes **
        claimedOwn C0 **
        hvphSuccKeccakAmb childSp s4 os (List.replicate 32 0) G)
      (hvphUnifiedPost spC childSp
        ValidateHeaderParentHashCorrespondence.Ret header s4 s5 vals s4
        thisBytes parentBytes C0 N rem os G)) :
    cpsTripleWithin (nCore + (5 + (1 + n)))
      (ValidateHeaderWhole.H + 56)
      ValidateHeaderParentHashCorrespondence.Ret cr
      (validateHeaderCorePre parentSpec headerSpec spC raIn header headerLen
        rawBytes parentRawBytes thisStruct parentStructPtr s4 s5
        headerStruct parentStruct o8 o9 o18 o19 o20 o21
        (step2ParentHashAmbient spC C0 os (List.replicate 32 0) G))
      ((.x21 ↦ᵣ s5) ** hvphUnifiedPost spC childSp
        ValidateHeaderParentHashCorrespondence.Ret header s4 s5 vals s4
        thisBytes parentBytes C0 N rem os G) := by
  have hroute := postMerge_status0_to_parent_hash_unified_call
    (cr := cr) (calleeCode := calleeCode) (n := n)
    spC childSp header headerLen s4 s5 oldRa vals thisBytes parentBytes C0 N rem os G
    hG hchild hvals8 hvals9 hvals18 hdisj hcallerDisj hcode hcallee
  have hseam' : cpsTripleWithin nCore (parentHashRouteFrameH + 56)
      (parentHashRouteFrameH + 196) cr
      (validateHeaderCorePre parentSpec headerSpec spC raIn header headerLen
        rawBytes parentRawBytes thisStruct parentStructPtr s4 s5
        headerStruct parentStruct o8 o9 o18 o19 o20 o21
        (step2ParentHashAmbient spC C0 os (List.replicate 32 0) G))
      (validateHeaderCoreStatus0SeamPost spC childSp header headerLen s4 s5 oldRa vals
        thisBytes parentBytes C0 os G) := by
    change cpsTripleWithin nCore (ValidateHeaderWhole.H + 56)
      (ValidateHeaderWhole.H + 196) cr _ _ at hseam
    simpa [parentHashRouteFrameH] using hseam
  have hseq := cpsTripleWithin_seq_same_cr hseam' hroute
  simpa [validateHeaderCoreStatus0SeamPost, parentHashRouteFrameH] using hseq

/-! The seam post is not left as an assertion that is only syntactically
available.  This concrete witness covers every atom in it at once: the
header/parent slices are four bytes each, `Claimed` and `Computed` are 32
bytes, `zk3_state` is the full 200-byte arena, and both the caller frame and
the four-cell child stack are present.  It is an assertion witness only; it
does not discharge the core execution premise above. -/

private inductive item4Atom where
  | regVal (r : Reg) (v : Word)
  | regOwn (r : Reg)
  | memVal (a v : Word) (hvalid : isValidDwordAccess a = true)
  | memOwn (a : Word) (hvalid : isValidDwordAccess a = true)

private inductive item4Resource where
  | reg (r : Reg)
  | mem (a : Word)
  deriving DecidableEq

private def item4AtomResource : item4Atom → item4Resource
  | .regVal r _ => .reg r
  | .regOwn r => .reg r
  | .memVal a _ _ => .mem a
  | .memOwn a _ => .mem a

private def item4AtomAssertion : item4Atom → Assertion
  | .regVal r v => r ↦ᵣ v
  | .regOwn r => regOwn r
  | .memVal a v _ => a ↦ₘ v
  | .memOwn a _ => memOwn a

private def item4AtomHeap : item4Atom → PartialState
  | .regVal r v => PartialState.singletonReg r v
  | .regOwn r => PartialState.singletonReg r 0
  | .memVal a v _ => PartialState.singletonMem a v
  | .memOwn a _ => PartialState.singletonMem a 0

private abbrev item4SpC : Word := 0xFE8
private abbrev item4ChildSp : Word := 0xFC8
private abbrev item4Header : Word := 0x2000
private abbrev item4HeaderLen : Word := 4
private abbrev item4S4 : Word := 0x3000
private abbrev item4S5 : Word := 4
private abbrev item4OldRa : Word := 0x1234
private abbrev item4ThisBytes : List (BitVec 8) := List.replicate 4 0
private abbrev item4ParentBytes : List (BitVec 8) := List.replicate 4 0
private abbrev item4C0 : List (BitVec 8) := List.replicate 32 0
private abbrev item4Os : List (BitVec 8) := List.replicate 200 0
private abbrev item4Out0 : List (BitVec 8) := List.replicate 32 0
private def item4Vals : Reg → Word
  | .x8 => item4Header
  | .x9 => item4HeaderLen
  | .x18 => item4S4
  | _ => 0

private def item4Atoms : List item4Atom :=
  [ .regVal .x10 0, .regVal .x0 0, .regVal .x8 item4Header,
    .regVal .x9 item4HeaderLen, .regVal .x20 item4S4,
    .regVal .x21 item4S5, .regVal .x11 0, .regVal .x12 0,
    .regVal .x13 0, .regVal .x1 item4OldRa, .regVal .x2 item4SpC,
    .regVal .x18 item4S4,
    .regOwn .x5, .regOwn .x6, .regOwn .x7,
    .regOwn .x14, .regOwn .x15, .regOwn .x16, .regOwn .x17,
    .regOwn .x28, .regOwn .x29, .regOwn .x30, .regOwn .x31,
    .memOwn (item4SpC + signExtend12 (4064 : BitVec 12) +
      signExtend12 (0 : BitVec 12)) (by decide),
    .memOwn (item4SpC + signExtend12 (4064 : BitVec 12) +
      signExtend12 (8 : BitVec 12)) (by decide),
    .memOwn (item4SpC + signExtend12 (4064 : BitVec 12) +
      signExtend12 (16 : BitVec 12)) (by decide),
    .memOwn (item4SpC + signExtend12 (4064 : BitVec 12) +
      signExtend12 (24 : BitVec 12)) (by decide),
    .memOwn (item4ChildSp - BitVec.ofNat 64 32) (by decide),
    .memOwn (item4ChildSp - BitVec.ofNat 64 24) (by decide),
    .memOwn (item4ChildSp - BitVec.ofNat 64 16) (by decide),
    .memOwn (item4ChildSp - BitVec.ofNat 64 8) (by decide),
    .memVal item4Header (packBytes [0, 0, 0, 0]) (by decide),
    .memVal item4S4 (packBytes [0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.hvph_claimed)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.hvph_claimed + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.hvph_claimed + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.hvph_claimed + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.hvph_computed)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.hvph_computed + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.hvph_computed + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide),
    .memVal (BitVec.ofNat 64 GuestAddrs.hvph_computed + 8 + 8 + 8)
      (packBytes [0, 0, 0, 0, 0, 0, 0, 0]) (by decide) ]

private def item4AtomsAssertion : Assertion :=
  item4Atoms.foldr (fun x acc => item4AtomAssertion x ** acc) empAssertion

private def item4AtomsHeap : PartialState :=
  item4Atoms.foldr (fun x acc => (item4AtomHeap x).union acc) PartialState.empty

private theorem item4RegRegDisjoint {r1 r2 : Reg} {v1 v2 : Word}
    (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint
      (PartialState.singletonReg r2 v2) := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r
  by_cases h : r = r1
  · subst r
    right
    simp [PartialState.singletonReg, hne]
  · left
    simp [PartialState.singletonReg, h]

private theorem item4MemMemDisjoint {a1 a2 v1 v2 : Word}
    (hne : a1 ≠ a2) :
    (PartialState.singletonMem a1 v1).Disjoint
      (PartialState.singletonMem a2 v2) := by
  refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro a
  by_cases h : a = a1
  · subst a
    right
    simp [PartialState.singletonMem, hne]
  · left
    simp [PartialState.singletonMem, h]

private theorem item4RegMemDisjoint {r : Reg} {a v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) :=
  ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem item4AtomHeapDisjoint_of_resource_ne {x y : item4Atom}
    (h : item4AtomResource x ≠ item4AtomResource y) :
    (item4AtomHeap x).Disjoint (item4AtomHeap y) := by
  cases x <;> cases y
  all_goals try exact item4RegMemDisjoint
  all_goals try exact item4RegMemDisjoint.symm
  all_goals try
    apply item4RegRegDisjoint
    simpa [item4AtomResource] using h
  all_goals try
    apply item4MemMemDisjoint
    simpa [item4AtomResource] using h

private theorem item4Atoms_sat : item4AtomsAssertion item4AtomsHeap := by
  apply sepConj_foldr_satisfiable item4AtomAssertion item4AtomHeap item4Atoms
  · intro x hx
    cases x with
    | regVal r v => rfl
    | regOwn r => exact ⟨0, rfl⟩
    | memVal a v hvalid => exact ⟨rfl, hvalid⟩
    | memOwn a hvalid => exact ⟨0, rfl, hvalid⟩
  · have hpair : item4Atoms.Pairwise
        (fun x y => item4AtomResource x ≠ item4AtomResource y) := by
      decide
    exact List.Pairwise.imp
      (fun {_ _} h => item4AtomHeapDisjoint_of_resource_ne h) hpair

set_option maxRecDepth 8000 in
private theorem item4Atoms_assertion_eq :
    item4AtomsAssertion =
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ item4Header) ** (.x9 ↦ᵣ item4HeaderLen) **
        (.x20 ↦ᵣ item4S4) ** (.x21 ↦ᵣ item4S5) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ (0 : Word)) **
        parentHashRouteFrame item4SpC item4OldRa item4Header item4S4 item4Vals
          item4ThisBytes item4ParentBytes **
        claimedOwn item4C0 **
        hvphSuccKeccakTail item4ChildSp item4Os item4Out0 empAssertion) := by
  funext h
  apply propext
  constructor <;> intro hp
  · simp [item4AtomsAssertion, item4Atoms, item4AtomAssertion,
      parentHashRouteFrame, hvphSuccKeccakTail, claimedOwn,
      item4HeaderLen, item4Vals, item4ThisBytes, item4ParentBytes,
      item4C0, item4Os, item4Out0, frameSlotsOwn, stackFree, regOwns,
      bytesRegion, bytesRegionAux,
      EvmAsm.Codegen.ValidateHeaderParentHashCorrespondence.hvphFrame,
      sepConj_emp_right', sepConj_assoc'] at hp ⊢
    xperm_hyp hp
  · simp [item4AtomsAssertion, item4Atoms, item4AtomAssertion,
      parentHashRouteFrame, hvphSuccKeccakTail, claimedOwn,
      item4HeaderLen, item4Vals, item4ThisBytes, item4ParentBytes,
      item4C0, item4Os, item4Out0, frameSlotsOwn, stackFree, regOwns,
      bytesRegion, bytesRegionAux,
      EvmAsm.Codegen.ValidateHeaderParentHashCorrespondence.hvphFrame,
      sepConj_emp_right', sepConj_assoc'] at hp ⊢
    xperm_hyp hp

theorem validateHeaderCoreStatus0SeamPost_inhabited :
    ∃ h : PartialState,
      validateHeaderCoreStatus0SeamPost item4SpC item4ChildSp item4Header
        item4HeaderLen item4S4 item4S5 item4OldRa item4Vals
        item4ThisBytes item4ParentBytes item4C0 item4Os empAssertion h := by
  refine ⟨item4AtomsHeap, ?_⟩
  have hs := item4Atoms_sat
  rw [item4Atoms_assertion_eq] at hs
  simpa [validateHeaderCoreStatus0SeamPost, item4Out0, item4Os, item4C0] using hs

/-! At the post-prologue seam the separately established `x20` cell and this
    carrier are exactly the ambient consumed by the stacked item-8 route.  The
    equality is intentionally stated as an assertion equality: it prevents a
    later caller from treating the two presentations as merely similar while
    silently dropping one of the physical regions. -/
theorem step2ParentHashRouteAmbient_as_unified_route_carrier
    (sp0 childSp v20 : Word)
    (C0 os out0 : List (BitVec 8)) (F : Assertion)
    (hchild : childSp = step2ParentHashChildSp sp0) :
    ((.x20 ↦ᵣ v20) ** step2ParentHashRouteAmbient sp0 C0 os out0 F) =
      (claimedOwn C0 ** hvphSuccKeccakAmb childSp v20 os out0 F) := by
  rw [hchild]
  funext h
  apply propext
  constructor <;> intro hp
  · simp only [step2ParentHashRouteAmbient, hvphSuccKeccakAmb] at hp ⊢
    xperm_hyp hp
  · simp only [step2ParentHashRouteAmbient, hvphSuccKeccakAmb] at hp ⊢
    xperm_hyp hp

/-! The side-condition envelope carried by the unified parent-hash adapter is
    independently inhabited on the same shape used by the hcore caller.  This
    is a named projection of the existing match cover, not a new decoder claim:
    it records that real lengths, alignment, byte validity and keccak bounds
    can all be supplied together. -/
def step2ParentHashEnvelope
    (sp0 spC : Word) (F : Assertion) (ret : Word)
    (thisPtr thisLen parentPtr parentLen : Word)
    (thisBytes parentBytes C0 : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8)) : Prop :=
  F.pcFree ∧
  ret &&& ~~~(1 : Word) = ret ∧
  spC = sp0 + signExtend12 (-32 : BitVec 12) ∧
  thisBytes.length = thisLen.toNat ∧
  3 ≤ thisBytes.length ∧ C0.length = 32 ∧
  thisPtr.toNat % 8 = 0 ∧ thisPtr.toNat + thisBytes.length ≤ 2 ^ 64 ∧
  (∀ k, k < thisBytes.length →
    isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true) ∧
  (headersParentHash_out thisBytes C0).length = 32 ∧
  parentLen = BitVec.ofNat 64
    (EvmAsm.Codegen.Proofs.keccakAbsorbStep * N + rem) ∧
  parentBytes.length = EvmAsm.Codegen.Proofs.keccakAbsorbStep * N + rem ∧ rem ≤ 135 ∧
  os.length = 200 ∧
  (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0 ∧
  (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64 ∧
  EvmAsm.Codegen.Proofs.keccakAbsorbStep * N + rem < 2 ^ 63 ∧ rem < 2 ^ 64 ∧
  (EvmAsm.Codegen.Proofs.keccakAbsorbCursor parentPtr N).toNat % 8 = 0 ∧
  (∀ n, n < rem →
    (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64) ∧
  (∀ n, n < rem →
    (EvmAsm.Codegen.Proofs.keccakAbsorbCursor parentPtr N).toNat +
      (rem - (n + 1)) < 2 ^ 64) ∧
  (∀ n, n < rem →
    isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true) ∧
  (∀ n, n < rem →
    isValidByteAccess
      (EvmAsm.Codegen.Proofs.keccakAbsorbCursor parentPtr N +
        BitVec.ofNat 64 (rem - (n + 1))) = true) ∧
  isValidByteAccess
    (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true ∧
  isValidByteAccess
    (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true ∧
  (∀ j, j < 200 →
    isValidMemAddr
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true) ∧
  headersParentHash_status thisBytes = 0 ∧
  (∀ q, q < 4 →
    dwordAt (headersParentHash_out thisBytes C0) q =
      dwordAt (keccakBodyDigest parentBytes N rem) q)

theorem step2ParentHashEnvelope_inhabited :
    ∃ (sp0 spC : Word) (ret thisPtr thisLen parentPtr parentLen : Word)
        (thisBytes parentBytes C0 : List (BitVec 8))
        (N rem : Nat) (os : List (BitVec 8)) (F : Assertion),
      step2ParentHashEnvelope sp0 spC F ret thisPtr thisLen parentPtr parentLen
        thisBytes parentBytes C0 N rem os := by
  rcases header_validate_parent_hash_match_cover with
    ⟨sp0, spC, ret, thisPtr, thisLen, parentPtr, parentLen, vals, v20,
      thisBytes, parentBytes, C0, N, rem, os, F, h⟩
  exact ⟨sp0, spC, ret, thisPtr, thisLen, parentPtr, parentLen, thisBytes,
    parentBytes, C0, N, rem, os, F, by
      simpa [step2ParentHashEnvelope] using h⟩

/-! A concrete, nonempty route-carrier witness.  The lengths are deliberately
    the real route lengths (Claimed 32 bytes, `zk3_state` 200 bytes, Computed
    32 bytes), and the frame is the same concrete frame used by the stacked
    route witness.  The existing route witness supplies the heap; the
    assertion equality above is what transports it to the Step-2 presentation.
    This witness includes the status-0 route-local stack/scratch, not the
    narrower all-exit core carrier. -/
theorem step2ParentHashAmbient_route_inhabited :
    ∃ h : PartialState,
      ((.x20 ↦ᵣ (0x3000 : Word)) **
        step2ParentHashRouteAmbient (0x1020 : Word)
          (List.replicate 32 0) (List.replicate 200 0)
          (List.replicate 32 0) empAssertion) h := by
  rcases parentHashUnifiedAmbient_inhabited with ⟨h, hh⟩
  refine ⟨h, ?_⟩
  have heq := step2ParentHashRouteAmbient_as_unified_route_carrier
    (0x1020 : Word) (0xFC8 : Word) (0x3000 : Word)
    (List.replicate 32 0) (List.replicate 200 0) (List.replicate 32 0)
    empAssertion (by decide)
  rw [heq]
  exact hh

end
end EvmAsm.Codegen.ValidateHeaderStep2ParentHashAmbient
