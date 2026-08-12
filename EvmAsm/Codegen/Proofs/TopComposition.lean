/-
  EvmAsm.Codegen.Proofs.TopComposition

  **The summit composition, stated under named phase hypotheses** (GH #12130,
  ledger row 12 / bead `evm-asm-4ch8f.64`).

  `runStatelessGuestSound cr fuel fr execute` (`Stateless/EntrySpec.lean:217`)
  is the theorem this project exists to prove, and until now nothing owned it:
  ledger row 12 was a bare `todo` and obligation 8 was pure indirection
  ("blocked on 4+5+6+7"). This module states the composition NOW, parameterized
  by six named `Prop`-valued phase hypotheses, so the sequencing + halt-wrap
  proof exists and typechecks from day one and each later PR discharges one
  hypothesis. The style is `MptWalkResiduals.lean`'s named-residual style.

  ## ⛔ Why this file spends most of its length on anti-vacuity apparatus

  The style is right; its flagship instance was NOT. PR #12141 kernel-checked
  that `MptWalkResiduals.wlCallWithinShape` is **unsatisfiable**, making the
  three call-site lemmas that consume it vacuous, via two independent defects:

  1. **Code-requirement coverage.** The residual fixes a `cr` that does not pin
     the callee it `jal`s into. `cpsTripleWithin` quantifies over EVERY state
     satisfying `cr`, so states whose memory decodes to anything at all at the
     callee are inside the claim — and the claim is then false, not weak.
  2. **Footprint.** The routine writes cells the pre/post never name. The frame
     `R` is universally quantified, so a frame OWNING one of those cells is
     admissible, and the routine's store to it falsifies the post.

  A top-level composition copying that naively would be vacuous at far greater
  scale, and it would look like the project's summit theorem. So the two defect
  classes are turned into kernel-checked *forcing lemmas* here (§1), the phase
  shapes are built so that the coverage defect cannot be expressed (§3: every
  phase carries the SAME top-level `cr` — a phase cannot silently shrink it),
  and the whole six-hypothesis family is shown JOINTLY SATISFIABLE by a
  concrete inhabitant (§5).

  ## What §1's forcing lemmas say (the footprint discipline, as theorems)

  * `cpsHaltTripleWithin_forces_regPreserved`: a register the precondition does
    not own must hold its ENTRY value at halt. So a phase that clobbers a
    register its pre does not name is not "under-specified" — its hypothesis is
    FALSE, and anything proved from it is vacuous.
  * `cpsHaltTripleWithin_forces_memPreserved`: the same for a memory dword.
  * `cpsTripleWithin_forces_regPreserved` / `_memPreserved`: the same two for a
    non-halting phase, since five of the six hypotheses are plain triples.
  * `cpsTripleWithin_needs_entry_code` (§2): a phase whose `cr` does not pin its
    own entry instruction is UNSATISFIABLE — defect class 1, generically.

  These are the generalization of MptWalk defect 2 to any triple in the tree.
  Applying them to the `.63` framing bundle led to the constructive repair in
  §6: `guestFraming` now owns the measured halt-boundary registers `x5`, `x10`
  and `x17` in BOTH `scratch` and `residue`.  The generic forcing lemmas still
  apply to any register omitted by a caller's framing.  The unconverted
  `_start` shell remains an inherited coverage residual (#12166), so this
  narrow boundary set is not presented as a complete whole-image clobber
  theorem.

  ## `fuel` (#10552) is UNDEFINED and is NOT invented here

  There is no gas-to-step constant `k` anywhere in the tree. This module does
  not create one. Instead `GuestPhaseLayout` carries a per-phase budget and
  `GuestPhaseLayout.fuel` is their SUM, so the top statement is instantiated at
  a `fuel` that is *derived* from the phase budgets rather than guessed. That is
  exactly the additive structure #10552 asks for: `k` still has to be measured,
  but its consumer now has a shape.

  ## What is NOT established here (read before quoting this file)

  * No phase hypothesis is discharged. Six named `Prop`s is what this is.
  * The satisfiability witness of §5 is a REAL but TRIVIAL guest (one `EBREAK`
    at the entry: it traps immediately, writes nothing, and the host-zeroed
    verdict byte is 0, so the accept clause is vacuous and soundness holds).
    It proves the six hypotheses are JOINTLY SATISFIABLE — i.e. the composition
    is not vacuous — and nothing more. It is not the guest.
  * `guestImageCodeReq` is NOT plugged in: it covers ~24.65% of `.text`
    (`scripts/guest_image_coverage.py`, ledger row 11), and by defect class 1
    an under-covering `cr` makes the phase hypotheses FALSE, not weak. The
    composition is therefore stated for an arbitrary `cr`, and instantiating it
    at the image `CodeReq` waits on full-image coverage (beads .63.2–.63.12).
-/

import EvmAsm.Codegen.Proofs.GuestImage
import EvmAsm.Rv64.SyscallSpecs

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm (anyBytes)
open EvmAsm.Stateless
open EvmAsm.Stateless.SpecRef

/-! ## §1. The footprint discipline, as forcing lemmas

    MptWalk defect 2 says: an assertion pair that does not NAME a written cell
    does not merely under-specify — the universally quantified frame turns the
    omission into a refutation. Stated positively, that is the following pair of
    theorems: whatever the precondition does not own is preserved to halt. Use
    them as a *checklist* on any new phase hypothesis — pick a register or dword
    the phase writes, and if the pre does not own it, the hypothesis is false. -/

/-- A register `r` that no `P`-heap owns. This is the checkable form of "the
    precondition names every register the code writes": if `RegFree P r` holds
    and the code writes `r` without restoring it, the triple below is false.
    (Deliberately not `Assertion.RegFree`: `Assertion` is a `def` for a function
    type, so dot-notation resolves into `Function`, not here.) -/
def RegFree (P : Assertion) (r : Reg) : Prop :=
  ∀ h, P h → h.regs r = none

/-- A memory dword `a` that no `P`-heap owns. -/
def MemFree (P : Assertion) (a : Word) : Prop :=
  ∀ h, P h → h.mem a = none

/-- Adjoining an unowned register to a satisfying heap keeps it satisfying
    (and compatible): the frame `r ↦ᵣ v` is admissible against any `RegFree r`
    precondition. -/
private theorem holdsFor_sepConj_regIs_of_regFree {P : Assertion} {r : Reg}
    {s : MachineState} (hfree : RegFree P r)
    (hp : PartialState) (hcompat : hp.CompatibleWith s) (hP : P hp) :
    (P ** (r ↦ᵣ s.getReg r)).holdsFor s := by
  refine ⟨hp.union (PartialState.singletonReg r (s.getReg r)), ?_, ?_⟩
  · refine (PartialState.CompatibleWith_union ?_).mpr
      ⟨hcompat, PartialState.CompatibleWith_singletonReg.mpr rfl⟩
    refine ⟨fun r' => ?_, fun _ => Or.inr rfl, fun _ => Or.inr rfl,
      Or.inr rfl, Or.inr rfl, Or.inr rfl, Or.inr rfl⟩
    by_cases hr : r' = r
    · exact Or.inl (hr ▸ hfree hp hP)
    · exact Or.inr (by simp [PartialState.singletonReg, hr])
  · refine ⟨hp, PartialState.singletonReg r (s.getReg r), ?_, rfl, hP, rfl⟩
    refine ⟨fun r' => ?_, fun _ => Or.inr rfl, fun _ => Or.inr rfl,
      Or.inr rfl, Or.inr rfl, Or.inr rfl, Or.inr rfl⟩
    by_cases hr : r' = r
    · exact Or.inl (hr ▸ hfree hp hP)
    · exact Or.inr (by simp [PartialState.singletonReg, hr])

/-- **Footprint forcing, register form.** If a halt triple's precondition does
    not own register `r`, then the triple CLAIMS that every run it covers leaves
    `r` at its entry value. Contrapositive (the way to use it): a phase that
    clobbers `r` and does not restore it needs `r` in its pre, or its hypothesis
    is unsatisfiable and everything downstream of it is vacuous.

    This is MptWalk defect 2 (PR #12141) stated once, generically. -/
theorem cpsHaltTripleWithin_forces_regPreserved
    {n : Nat} {e : Word} {cr : CodeReq} {P Q : Assertion}
    (h : cpsHaltTripleWithin n e cr P Q) (r : Reg) (hfree : RegFree P r)
    {s : MachineState} (hcr : cr.SatisfiedBy s) (hpc : s.pc = e)
    {hp : PartialState} (hcompat : hp.CompatibleWith s) (hP : P hp) :
    ∃ k, k ≤ n ∧ ∃ s', stepN k s = some s' ∧ isHalted s' = true ∧
      s'.getReg r = s.getReg r := by
  obtain ⟨k, hk, s', hstep, hhalt, hQR⟩ :=
    h (r ↦ᵣ s.getReg r) pcFree_regIs s hcr
      (holdsFor_sepConj_regIs_of_regFree hfree hp hcompat hP) hpc
  exact ⟨k, hk, s', hstep, hhalt, holdsFor_regIs.mp (holdsFor_sepConj_elim_right hQR)⟩

/-- Adjoining an unowned (valid) memory dword to a satisfying heap. -/
private theorem holdsFor_sepConj_memIs_of_memFree {P : Assertion} {a : Word}
    {s : MachineState} (hfree : MemFree P a) (hvalid : isValidDwordAccess a = true)
    (hp : PartialState) (hcompat : hp.CompatibleWith s) (hP : P hp) :
    (P ** (a ↦ₘ s.getMem a)).holdsFor s := by
  refine ⟨hp.union (PartialState.singletonMem a (s.getMem a)), ?_, ?_⟩
  · refine (PartialState.CompatibleWith_union ?_).mpr
      ⟨hcompat, PartialState.CompatibleWith_singletonMem.mpr rfl⟩
    refine ⟨fun _ => Or.inr rfl, fun a' => ?_, fun _ => Or.inr rfl,
      Or.inr rfl, Or.inr rfl, Or.inr rfl, Or.inr rfl⟩
    by_cases ha : a' = a
    · exact Or.inl (ha ▸ hfree hp hP)
    · exact Or.inr (by simp [PartialState.singletonMem, ha])
  · refine ⟨hp, PartialState.singletonMem a (s.getMem a), ?_, rfl, hP, ⟨rfl, hvalid⟩⟩
    refine ⟨fun _ => Or.inr rfl, fun a' => ?_, fun _ => Or.inr rfl,
      Or.inr rfl, Or.inr rfl, Or.inr rfl, Or.inr rfl⟩
    by_cases ha : a' = a
    · exact Or.inl (ha ▸ hfree hp hP)
    · exact Or.inr (by simp [PartialState.singletonMem, ha])

/-- **Footprint forcing, memory form.** A dword the precondition does not own
    must hold its entry value at halt. The MptWalk telemetry cells (six `sd`s to
    cells the residual never names) are exactly this failure. -/
theorem cpsHaltTripleWithin_forces_memPreserved
    {n : Nat} {e : Word} {cr : CodeReq} {P Q : Assertion}
    (h : cpsHaltTripleWithin n e cr P Q) (a : Word) (hfree : MemFree P a)
    (hvalid : isValidDwordAccess a = true)
    {s : MachineState} (hcr : cr.SatisfiedBy s) (hpc : s.pc = e)
    {hp : PartialState} (hcompat : hp.CompatibleWith s) (hP : P hp) :
    ∃ k, k ≤ n ∧ ∃ s', stepN k s = some s' ∧ isHalted s' = true ∧
      s'.getMem a = s.getMem a := by
  obtain ⟨k, hk, s', hstep, hhalt, hQR⟩ :=
    h (a ↦ₘ s.getMem a) pcFree_memIs s hcr
      (holdsFor_sepConj_memIs_of_memFree hfree hvalid hp hcompat hP) hpc
  exact ⟨k, hk, s', hstep, hhalt,
    holdsFor_memIs_getMem (holdsFor_sepConj_elim_right hQR)⟩

/-- **Footprint forcing, register form, for a non-halting phase.** The five
    intermediate phase hypotheses are `cpsTripleWithin`s, so they get their own
    copy of the checklist: a register the phase's pre does not own must carry its
    entry value all the way to the phase exit. -/
theorem cpsTripleWithin_forces_regPreserved
    {n : Nat} {entry exit_ : Word} {cr : CodeReq} {P Q : Assertion}
    (h : cpsTripleWithin n entry exit_ cr P Q) (r : Reg) (hfree : RegFree P r)
    {s : MachineState} (hcr : cr.SatisfiedBy s) (hpc : s.pc = entry)
    {hp : PartialState} (hcompat : hp.CompatibleWith s) (hP : P hp) :
    ∃ k, k ≤ n ∧ ∃ s', stepN k s = some s' ∧ s'.pc = exit_ ∧
      s'.getReg r = s.getReg r := by
  obtain ⟨k, hk, s', hstep, hpc', hQR⟩ :=
    h (r ↦ᵣ s.getReg r) pcFree_regIs s hcr
      (holdsFor_sepConj_regIs_of_regFree hfree hp hcompat hP) hpc
  exact ⟨k, hk, s', hstep, hpc',
    holdsFor_regIs.mp (holdsFor_sepConj_elim_right hQR)⟩

/-- **Footprint forcing, memory form, for a non-halting phase.** -/
theorem cpsTripleWithin_forces_memPreserved
    {n : Nat} {entry exit_ : Word} {cr : CodeReq} {P Q : Assertion}
    (h : cpsTripleWithin n entry exit_ cr P Q) (a : Word) (hfree : MemFree P a)
    (hvalid : isValidDwordAccess a = true)
    {s : MachineState} (hcr : cr.SatisfiedBy s) (hpc : s.pc = entry)
    {hp : PartialState} (hcompat : hp.CompatibleWith s) (hP : P hp) :
    ∃ k, k ≤ n ∧ ∃ s', stepN k s = some s' ∧ s'.pc = exit_ ∧
      s'.getMem a = s.getMem a := by
  obtain ⟨k, hk, s', hstep, hpc', hQR⟩ :=
    h (a ↦ₘ s.getMem a) pcFree_memIs s hcr
      (holdsFor_sepConj_memIs_of_memFree hfree hvalid hp hcompat hP) hpc
  exact ⟨k, hk, s', hstep, hpc',
    holdsFor_memIs_getMem (holdsFor_sepConj_elim_right hQR)⟩

/-! ## §2. Code-requirement coverage, as a forcing lemma

    MptWalk defect 1: a `cr` that does not pin an address the phase executes
    does not weaken the claim, it refutes it — `cpsTripleWithin` ranges over
    every state satisfying `cr`, including the one whose code memory is exactly
    `cr` and therefore `none` at the unpinned address, where the machine is
    already halted. The lemma below is the entry-address case, which is the one
    a composition can check mechanically. -/

/-- The canonical "adversarial" machine state for a heap: registers/memory read
    off `hp` (so `hp` is compatible with it), code EXACTLY `cr` (so `cr` is
    satisfied and nothing else is decodable), pc as requested. -/
private def adversarialState (cr : CodeReq) (hp : PartialState) (pc : Word) :
    MachineState where
  regs := fun r => (hp.regs r).getD 0
  mem := fun a => (hp.mem a).getD 0
  code := cr
  pc := pc
  publicValues := (hp.publicValues).getD []
  privateInput := (hp.privateInput).getD []
  inputBufBase := (hp.inputBufBase).getD defaultInputBufBase

private theorem adversarialState_getReg {cr : CodeReq} {hp : PartialState} {pc : Word}
    (r : Reg) (hr : r ≠ .x0) :
    (adversarialState cr hp pc).getReg r = (hp.regs r).getD 0 := by
  cases r <;> simp_all [MachineState.getReg, adversarialState]

private theorem adversarialState_compat {cr : CodeReq} {hp : PartialState} {pc : Word}
    (hpcNone : hp.pc = none) (hcodeNone : ∀ a, hp.code a = none)
    (hx0 : ∀ v, hp.regs .x0 = some v → v = 0) :
    hp.CompatibleWith (adversarialState cr hp pc) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r v hv
    by_cases hr : r = .x0
    · subst hr
      have hv0 : v = 0 := hx0 v hv
      subst hv0
      rfl
    · rw [adversarialState_getReg r hr, hv]; rfl
  · intro a v hv
    show (adversarialState cr hp pc).getMem a = v
    simp [MachineState.getMem, adversarialState, hv]
  · intro a i hi
    rw [hcodeNone a] at hi
    exact absurd hi (by nofun)
  · intro v hv
    rw [hpcNone] at hv
    exact absurd hv (by nofun)
  · intro v hv; simp [adversarialState, hv]
  · intro v hv; simp [adversarialState, hv]
  · intro v hv; simp [adversarialState, hv]

/-- **Coverage forcing (entry address).** A phase whose `CodeReq` does not pin
    its own entry instruction is UNSATISFIABLE as soon as the phase is supposed
    to make progress (`entry ≠ exit`) and its precondition is inhabited by a
    heap that owns neither the pc nor any code (the normal case: assertions are
    `pcFree`, and code ownership travels in `cr`, not in `P`).

    Checklist use: for every phase hypothesis, confirm `cr` pins entry — and, by
    the same argument applied at each fetch, every address the phase or its
    callees execute. This is MptWalk defect 1 (PR #12141) stated generically:
    the residual there `jal`s into a callee its `cr` leaves unpinned, so the
    same "already halted at the unpinned address" state refutes it. -/
theorem cpsTripleWithin_needs_entry_code
    {n : Nat} {entry exit_ : Word} {cr : CodeReq} {P Q : Assertion}
    (hne : entry ≠ exit_) (hnone : cr entry = none)
    {hp : PartialState} (hP : P hp) (hpcNone : hp.pc = none)
    (hcodeNone : ∀ a, hp.code a = none)
    (hx0 : ∀ v, hp.regs .x0 = some v → v = 0) :
    ¬ cpsTripleWithin n entry exit_ cr P Q := by
  intro htriple
  have hcompat : hp.CompatibleWith (adversarialState cr hp entry) :=
    adversarialState_compat hpcNone hcodeNone hx0
  have hcr : cr.SatisfiedBy (adversarialState cr hp entry) := fun _ _ hi => hi
  have hPR : (P ** empAssertion).holdsFor (adversarialState cr hp entry) :=
    ⟨hp, hcompat, ⟨hp, PartialState.empty, PartialState.Disjoint_empty_right,
      PartialState.union_empty_right, hP, rfl⟩⟩
  obtain ⟨k, _, s', hstep, hpc', _⟩ :=
    htriple empAssertion pcFree_emp (adversarialState cr hp entry) hcr hPR rfl
  have hstepnone : step (adversarialState cr hp entry) = none := by
    have hc : (adversarialState cr hp entry).code
        (adversarialState cr hp entry).pc = none := hnone
    simp [step, hc]
  cases k with
  | zero =>
    have heq : adversarialState cr hp entry = s' := by simpa using hstep
    exact hne (by rw [← hpc', ← heq]; rfl)
  | succ m => simp [stepN, hstepnone] at hstep

/-! ## §3. Phase vocabulary

    A phase is a contiguous run of the guest between two program points, with a
    step budget and an entry/exit assertion. Two structural decisions, both made
    to close MptWalk defect 1 by construction:

    * **Every phase carries the SAME `cr`** — the top statement's. There is no
      per-phase `CodeReq` to shrink, so a phase cannot quietly claim a triple
      over code it does not pin, and `cpsTripleWithin_seq_same_cr` composes them
      with no disjointness side-condition. What remains to check per phase is
      only whether that ONE `cr` covers the addresses the phase executes; §2
      says what happens if it does not.
    * **Assertions are input-indexed** (`Bytes → Assertion`): the top statement
      quantifies over the host input, so the intermediate states do too. -/

/-- Boundary program points, per-phase step budgets, and the input-indexed
    intermediate assertions the six phase hypotheses are stated over.

    The phase decomposition is the issue's (#12130): decode → witness DBs →
    header chain → execution → state root → verdict publish. It is a LAYOUT
    parameter, not a claim: today's `Entry.run_stateless_guest` is still the PR6
    stub (`read_chain_id ++ decode_validation_bit ++ decode_header_count ++
    serialize_stateless_output`), so nothing in the tree yet fixes these
    boundaries. Re-shaping is expected and cheap — every re-shape is then a
    recorded decision instead of an implicit one. -/
structure GuestPhaseLayout where
  /-- pc where input decode hands over to witness-DB construction. -/
  pcAfterDecode : Word
  /-- pc where witness-DB construction hands over to header validation. -/
  pcAfterWitness : Word
  /-- pc where header validation hands over to execution. -/
  pcAfterHeaders : Word
  /-- pc where execution hands over to state-root computation. -/
  pcAfterExec : Word
  /-- pc where state-root computation hands over to the verdict publish. -/
  pcAfterStateRoot : Word
  /-- Step budgets, one per phase. `fuel` is their sum — see #10552: the
      gas-derived constant `k` is still undefined, and this module does not
      invent one; it gives the top statement's `fuel` an additive shape so that
      whatever `k` turns out to be enters through the per-phase budgets. -/
  budgetDecode : Nat
  budgetWitness : Nat
  budgetHeaders : Nat
  budgetExec : Nat
  budgetStateRoot : Nat
  budgetPublish : Nat
  /-- State after input decode, as a function of the host input. -/
  afterDecode : Bytes → Assertion
  /-- State after witness-DB construction. -/
  afterWitness : Bytes → Assertion
  /-- State after header-chain validation. -/
  afterHeaders : Bytes → Assertion
  /-- State after execution. -/
  afterExec : Bytes → Assertion
  /-- State after state-root computation, i.e. the verdict publisher's input. -/
  afterStateRoot : Bytes → Assertion

/-- The top statement's `fuel`, DERIVED from the six budgets. The association
    is left-nested exactly as `cpsTripleWithin_seq_same_cr` nests it, so the
    composition below needs no arithmetic rewriting. -/
def GuestPhaseLayout.fuel (L : GuestPhaseLayout) : Nat :=
  L.budgetDecode + L.budgetWitness + L.budgetHeaders + L.budgetExec +
    L.budgetStateRoot + L.budgetPublish

/-- The admissible-input side-condition shared by every phase hypothesis: the
    size bound and the resource envelope from the top statement. A phase may
    use it; none is obliged to. -/
def AdmissibleInput (input : Bytes) : Prop :=
  input.length ≤ MAX_INPUT_BYTES ∧ inputWithinResourceEnvelope input

/-! ### The six named phase hypotheses

    Each is a `cpsTripleWithin` over the phase's entry/exit program points at
    the top-level `cr`, from the previous phase's exit assertion to its own.
    Satisfiability requirements that a discharging PR must meet, for EACH of
    them (this is the checklist; §1 and §2 are the theorems behind it):

    1. `cr` pins every address the phase fetches, INCLUDING every callee it
       `jal`s into (§2 — otherwise the hypothesis is false, not weak);
    2. the pre owns every register and every dword the phase writes (§1);
    3. the exit assertion is literally the next phase's entry assertion (that
       is forced here: they are the same `L.after*` field). -/

/-- **Rows 2–3 of the ledger.** Input decode: from the ELF entry with the host
    input framed and the work regions owned, to `pcAfterDecode` with the decoded
    payload in `afterDecode`. -/
def InputDecodePhaseShape (cr : CodeReq) (fr : GuestFraming)
    (L : GuestPhaseLayout) : Prop :=
  ∀ input : Bytes, AdmissibleInput input →
    cpsTripleWithin L.budgetDecode GUEST_ENTRY L.pcAfterDecode cr
      (guestInputAssertion input ** fr.scratch)
      (L.afterDecode input)

/-- **Rows 4–5, obligations 7/10.** Witness-DB construction (node DB + code DB
    build). -/
def WitnessDbPhaseShape (cr : CodeReq) (L : GuestPhaseLayout) : Prop :=
  ∀ input : Bytes, AdmissibleInput input →
    cpsTripleWithin L.budgetWitness L.pcAfterDecode L.pcAfterWitness cr
      (L.afterDecode input) (L.afterWitness input)

/-- **Row 3's header family.** Header-chain validation. -/
def HeaderChainPhaseShape (cr : CodeReq) (L : GuestPhaseLayout) : Prop :=
  ∀ input : Bytes, AdmissibleInput input →
    cpsTripleWithin L.budgetHeaders L.pcAfterWitness L.pcAfterHeaders cr
      (L.afterWitness input) (L.afterHeaders input)

/-- **Rows 8–10, the obligation-4 seam.** Block/transaction execution. -/
def ExecPhaseShape (cr : CodeReq) (L : GuestPhaseLayout) : Prop :=
  ∀ input : Bytes, AdmissibleInput input →
    cpsTripleWithin L.budgetExec L.pcAfterHeaders L.pcAfterExec cr
      (L.afterHeaders input) (L.afterExec input)

/-- **Row 9.** Post-state root computation. -/
def StateRootPhaseShape (cr : CodeReq) (L : GuestPhaseLayout) : Prop :=
  ∀ input : Bytes, AdmissibleInput input →
    cpsTripleWithin L.budgetStateRoot L.pcAfterExec L.pcAfterStateRoot cr
      (L.afterExec input) (L.afterStateRoot input)

/-- **Row 11 + the halt.** Verdict publish: serialize the result into the
    observation window and HALT. This is the only phase stated as a
    `cpsHaltTripleWithin`, so the halt-wrap obligation
    (`cpsTripleWithin_as_cpsHaltTripleWithin`, `CPSSpec.lean:897`) sits inside
    exactly one named hypothesis rather than being smeared across the
    composition.

    ⚠️ Discharging it requires the publisher's pre (`afterStateRoot`) to own the
    halt-stub instruction and whatever register the stub reads (`t0` for the
    ECALL convention), because `isHalted` has to be derivable at the halt state;
    and the post drops that ownership, which is sound because `holdsFor` is
    "∃ compatible sub-heap" (resources may be forgotten at the boundary, never
    conjured). -/
def VerdictPublishShape (cr : CodeReq) (fr : GuestFraming) (L : GuestPhaseLayout)
    (execute : ExecutionSeam) : Prop :=
  ∀ input : Bytes, AdmissibleInput input →
    cpsHaltTripleWithin L.budgetPublish L.pcAfterStateRoot cr
      (L.afterStateRoot input)
      (guestOutputSound execute input ** fr.residue)

/-! ## §4. The composition -/

/-- **THE SUMMIT, under named phase hypotheses.**

    Six named `Prop`s in, `runStatelessGuestSound` out, at `fuel` = the sum of
    the six phase budgets. The sequencing and the halt-wrap are done HERE, once,
    and do not wait on any phase: what remains for ledger row 12 is exactly the
    six hypotheses, each of which is now a checkable definition of done for its
    ledger rows.

    Vacuity status: the hypothesis family is JOINTLY SATISFIABLE — §5 exhibits a
    concrete `(cr, fr, execute, L)` and proves all six. So this theorem is not
    an implication out of nothing. What §5 does NOT show is that the family is
    satisfiable at the REAL guest image; §1/§2/§6 are the tools for checking
    that phase by phase, and §6 records one live obstruction already. -/
theorem runStatelessGuestSound_of_phases
    {cr : CodeReq} {fr : GuestFraming} {execute : ExecutionSeam}
    {L : GuestPhaseLayout}
    (hDecode : InputDecodePhaseShape cr fr L)
    (hWitness : WitnessDbPhaseShape cr L)
    (hHeaders : HeaderChainPhaseShape cr L)
    (hExec : ExecPhaseShape cr L)
    (hStateRoot : StateRootPhaseShape cr L)
    (hPublish : VerdictPublishShape cr fr L execute) :
    runStatelessGuestSound cr L.fuel fr execute := by
  intro input hlen henv
  have hadm : AdmissibleInput input := ⟨hlen, henv⟩
  exact cpsTripleWithin_seq_haltWithin_same_cr
    (cpsTripleWithin_seq_same_cr
      (cpsTripleWithin_seq_same_cr
        (cpsTripleWithin_seq_same_cr
          (cpsTripleWithin_seq_same_cr
            (hDecode input hadm) (hWitness input hadm))
          (hHeaders input hadm))
        (hExec input hadm))
      (hStateRoot input hadm))
    (hPublish input hadm)

/-! ## §5. Joint satisfiability of the six hypotheses (the anti-vacuity witness)

    A hypothesis nobody can satisfy makes a composition worthless, and that is
    precisely what happened to `wlCallWithinShape` (PR #12141). So the family
    above is discharged here for one concrete instance:

    * `demoCr` — a single `EBREAK` at `GUEST_ENTRY`. `step_ebreak` halts
      unconditionally, so no register ownership is needed to prove the halt, and
      the `cr` COVERS every address executed (there is exactly one, and it is
      pinned) — defect class 1 is discharged, not dodged.
    * `demoFraming.scratch` — the observation window, host-zeroed. Note this is
      NOT `.63`'s `guestScratch`, which havocs the window: with a havoc'd window
      an immediately-halting guest is genuinely UNSOUND (the host could hand it
      a window already claiming `valid = 1` with a bogus root), so the demo has
      to pin the contents. That asymmetry is a real property of the statement,
      not a convenience: at `.63`'s framing the guest MUST write the window.
    * The five non-publish phases are zero-length at `GUEST_ENTRY` — the
      witness shows the six hypotheses are jointly inhabited, not that the real
      guest decomposes this way.

    The guest it describes is honest and useless: it traps immediately and
    claims nothing. Soundness holds because the verdict byte is 0, so the accept
    clause is vacuous — false rejects are allowed by design
    (`runStatelessGuestSound` is one-sided). -/

/-- Host-zeroed observation window contents. -/
def demoOutputBytes : Bytes := List.replicate OUTPUT_CLAIM_BYTES (0 : BitVec 8)

@[simp] theorem demoOutputBytes_length : demoOutputBytes.length = OUTPUT_CLAIM_BYTES := by
  simp [demoOutputBytes]

/-- The demo image: one `EBREAK` at the ELF entry. -/
def demoCr : CodeReq := CodeReq.singleton GUEST_ENTRY .EBREAK

/-- The demo scratch: ownership of the host-zeroed observation window. -/
def demoScratch : Assertion := bytesRegion OUTPUT_ADDR demoOutputBytes

/-! ### The `scratch_sat` non-vacuity witness for the demo framing

    Mirrors `GuestImage.lean`'s `guestScratch_sat` chain (its two input lemmas
    are `private` there, so the technique is re-derived rather than reused). -/

private theorem demo_satWithin_inputLen (input : Bytes) :
    (bytesRegion (INPUT_ADDR + INPUT_LEN_OFFSET)
        (u64LEBytes input.length)).SatWithin 0x40000008 0x40000010 := by
  have h := satWithin_bytesRegion (INPUT_ADDR + INPUT_LEN_OFFSET)
    (u64LEBytes input.length) (fun k hk => by
      rw [u64LEBytes_length] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      decide)
  rw [u64LEBytes_length] at h
  exact h.congr_bounds (by decide) (by decide)

private theorem demo_satWithin_inputBody (input : Bytes)
    (hlen : input.length ≤ MAX_INPUT_BYTES) :
    (bytesRegion (INPUT_ADDR + INPUT_BODY_OFFSET) input).SatWithin
      0x40000010 (0x40000010 + 8 * ((input.length + 7) / 8)) := by
  have hmax : MAX_INPUT_BYTES = 0x37FFFFF8 := rfl
  have hbase : (INPUT_ADDR + INPUT_BODY_OFFSET).toNat = 0x40000010 := by decide
  have h := satWithin_bytesRegion (INPUT_ADDR + INPUT_BODY_OFFSET) input
    (fun k hk => by
      have hlt : (INPUT_ADDR + INPUT_BODY_OFFSET).toNat + 8 * k < 2 ^ 64 := by
        rw [hbase]; omega
      apply isValidDwordAccess_of_toNat
      · rw [toNat_add_ofNat_of_le hlt, hbase]; omega
      · rw [toNat_add_ofNat_of_le hlt, hbase]; left
        constructor
        · omega
        · omega)
  rw [hbase] at h
  exact h

private theorem demo_satWithin_window :
    demoScratch.SatWithin 0xa0010000 (0xa0010000 + 40) := by
  have hbase : OUTPUT_ADDR.toNat = 0xa0010000 := by decide
  have h := satWithin_bytesRegion OUTPUT_ADDR demoOutputBytes (fun k hk => by
    rw [demoOutputBytes_length] at hk
    have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
      simp only [OUTPUT_CLAIM_BYTES] at hk; omega
    rcases hk5 with rfl | rfl | rfl | rfl | rfl <;> decide)
  rw [demoOutputBytes_length, hbase] at h
  exact h.congr_bounds rfl (by simp [OUTPUT_CLAIM_BYTES])

/-- The demo precondition, with its footprint: everything it owns is a memory
    dword in `[0x40000008, 0xa0010028)` (input record, then window). -/
theorem demo_pre_satWithin (input : Bytes) (hlen : input.length ≤ MAX_INPUT_BYTES) :
    (guestInputAssertion input ** demoScratch).SatWithin 0x40000008 (0xa0010000 + 40) := by
  have hmax : MAX_INPUT_BYTES = 0x37FFFFF8 := rfl
  have hin : (guestInputAssertion input).SatWithin
      0x40000008 (0x40000010 + 8 * ((input.length + 7) / 8)) :=
    (demo_satWithin_inputLen input).sepConj
      (demo_satWithin_inputBody input hlen) (by omega) (by omega)
  exact (hin.mono (le_refl _) (show
      0x40000010 + 8 * ((input.length + 7) / 8) ≤ 0xa0010000 by omega)).sepConj
    demo_satWithin_window (by omega) (by omega)

theorem demoScratch_sat : ∀ input : Bytes, input.length ≤ MAX_INPUT_BYTES →
    ∃ h, (guestInputAssertion input ** demoScratch) h :=
  fun input hlen => (demo_pre_satWithin input hlen).sat

/-- **The demo precondition is inhabited at the MACHINE level too.** The
    `GuestFraming.scratch_sat` field only asks for a heap; a triple is still
    vacuous if no `MachineState` satisfies its antecedent (`cr` satisfied, pc at
    the entry, `(P ** R).holdsFor`). This exhibits one, so `demoPublish` — and
    with it the whole witness family of §5 — quantifies over a nonempty set of
    runs. -/
theorem demo_entryState_exists (input : Bytes) (hlen : input.length ≤ MAX_INPUT_BYTES) :
    ∃ s : MachineState, demoCr.SatisfiedBy s ∧ s.pc = GUEST_ENTRY ∧
      (guestInputAssertion input ** demoScratch).holdsFor s := by
  obtain ⟨hp, hP, hw⟩ := demo_pre_satWithin input hlen
  refine ⟨adversarialState demoCr hp GUEST_ENTRY, fun _ _ hi => hi, rfl,
    ⟨hp, adversarialState_compat hw.pc hw.code (fun v hv => by
      rw [hw.regs .x0] at hv; exact absurd hv (by nofun)), hP⟩⟩

/-- The demo framing bundle: the host-zeroed window at entry, nothing left over
    at halt (the window's ownership moves into `guestOutputSound`). -/
def demoFraming : GuestFraming where
  scratch := demoScratch
  residue := empAssertion
  scratch_sat := demoScratch_sat

/-- The demo layout: all five non-publish boundaries collapsed onto the entry,
    all budgets zero. -/
def demoLayout : GuestPhaseLayout where
  pcAfterDecode := GUEST_ENTRY
  pcAfterWitness := GUEST_ENTRY
  pcAfterHeaders := GUEST_ENTRY
  pcAfterExec := GUEST_ENTRY
  pcAfterStateRoot := GUEST_ENTRY
  budgetDecode := 0
  budgetWitness := 0
  budgetHeaders := 0
  budgetExec := 0
  budgetStateRoot := 0
  budgetPublish := 0
  afterDecode := fun input => guestInputAssertion input ** demoScratch
  afterWitness := fun input => guestInputAssertion input ** demoScratch
  afterHeaders := fun input => guestInputAssertion input ** demoScratch
  afterExec := fun input => guestInputAssertion input ** demoScratch
  afterStateRoot := fun input => guestInputAssertion input ** demoScratch

/-- The demo `fuel` is 0 — the guest halts at its first fetch. -/
theorem demoLayout_fuel : demoLayout.fuel = 0 := rfl

/-- The window contents pinned by `demoScratch` are a sound (rejecting) claim:
    byte 32 is 0, so the accept clause is vacuous. -/
private theorem demoScratch_outputSound (execute : ExecutionSeam) (input : Bytes) :
    ∀ h, demoScratch h → (guestOutputSound execute input ** empAssertion) h := by
  intro h hb
  refine ⟨h, PartialState.empty, PartialState.Disjoint_empty_right,
    PartialState.union_empty_right, ?_, rfl⟩
  exact ⟨demoOutputBytes, demoOutputBytes_length, hb, by
    intro hone; exact absurd hone (by decide)⟩

/-- The demo publish phase: `EBREAK` halts in zero steps, and the pre already
    pins a rejecting window, so the post holds. -/
theorem demoPublish (execute : ExecutionSeam) :
    VerdictPublishShape demoCr demoFraming demoLayout execute := by
  intro input _hadm R hR s hcr hPR hpc
  have hfetch : s.code s.pc = some .EBREAK := by
    rw [hpc]
    exact hcr GUEST_ENTRY .EBREAK (by simp [demoCr, CodeReq.singleton])
  refine ⟨0, Nat.le_refl 0, s, rfl, by simp [isHalted, step_ebreak hfetch], ?_⟩
  -- Drop the input framing (sound: `holdsFor` is "∃ compatible sub-heap"),
  -- then weaken the pinned window to the sound-claim assertion.
  have h2 : (demoScratch ** R).holdsFor s :=
    holdsFor_sepConj_elim_right (holdsFor_sepConj_assoc.mp hPR)
  obtain ⟨hp, hcompat, hpq⟩ := h2
  exact ⟨hp, hcompat,
    sepConj_mono_left (demoScratch_outputSound execute input) hp hpq⟩

/-- The five non-publish demo phases: zero-length, identity. -/
private theorem demoIdPhase (A : Assertion) :
    cpsTripleWithin 0 GUEST_ENTRY GUEST_ENTRY demoCr A A :=
  cpsTripleWithin_extend_code (by intro a i hi; exact absurd hi (by simp [CodeReq.empty]))
    (cpsTripleWithin_refl (fun _ hp => hp))

/-- **The six hypotheses are jointly satisfiable.** Every one of them is
    discharged here for `(demoCr, demoFraming, demoLayout)`. This is the artifact
    `wlCallWithinShape` lacked: it is a kernel-checked demonstration that
    `runStatelessGuestSound_of_phases` is not an implication out of an empty
    hypothesis family. -/
theorem demo_phases_satisfiable (execute : ExecutionSeam) :
    InputDecodePhaseShape demoCr demoFraming demoLayout ∧
    WitnessDbPhaseShape demoCr demoLayout ∧
    HeaderChainPhaseShape demoCr demoLayout ∧
    ExecPhaseShape demoCr demoLayout ∧
    StateRootPhaseShape demoCr demoLayout ∧
    VerdictPublishShape demoCr demoFraming demoLayout execute :=
  ⟨fun input _ => demoIdPhase (guestInputAssertion input ** demoScratch),
   fun input _ => demoIdPhase (guestInputAssertion input ** demoScratch),
   fun input _ => demoIdPhase (guestInputAssertion input ** demoScratch),
   fun input _ => demoIdPhase (guestInputAssertion input ** demoScratch),
   fun input _ => demoIdPhase (guestInputAssertion input ** demoScratch),
   demoPublish execute⟩

/-- **`runStatelessGuestSound` is inhabited.** The composition applied to the
    witness family: a guest that traps at its entry, over a host-zeroed window,
    satisfies the summit statement (soundly rejecting everything). Nothing about
    the real guest follows — this pins the STATEMENT down as satisfiable, which
    is the property `wlCallWithinShape` turned out to lack. -/
theorem runStatelessGuestSound_demo (execute : ExecutionSeam) :
    runStatelessGuestSound demoCr demoLayout.fuel demoFraming execute :=
  let ⟨h1, h2, h3, h4, h5, h6⟩ := demo_phases_satisfiable execute
  runStatelessGuestSound_of_phases h1 h2 h3 h4 h5 h6

/-! ## §6. The framing bundle names its boundary clobbers

    `guestFraming` now owns `x5`, `x10` and `x17` in BOTH `scratch` and
    `residue`.  Their provenance is deliberately explicit: `x5` is written by
    the measured `_start` body and by the `sp1` halt stub; the `linux93` halt
    stub writes `x17` as its syscall selector and `x10` as its result.  The
    verified halt predicate is `step = none`, and `step_ecall_halt` constrains
    only `x5`, so `x17` is not a special unowned syscall register in this
    framing.  The generic forcing lemmas above remain deliberately unchanged:
    any register omitted by a caller's framing is still forced to be preserved.

    The linked `guestImageCodeReq` still excludes the unconverted `_start`
    shell, so the complete image clobber set remains the inherited `.64` /
    #12166 residual.  The constructive repair here is therefore narrow and
    explicit about the three measured halt-boundary registers, rather than a
    claim that the unconverted shell has already been covered. -/

private theorem bytesRegionAux_regFree (r : Reg) :
    ∀ (n : Nat) (base : Word) (bs : List (BitVec 8)),
      RegFree (bytesRegionAux base n bs) r := by
  intro n
  induction n with
  | zero => intro base bs h hh; rw [hh]; rfl
  | succ m ih =>
    intro base bs h hh
    obtain ⟨h1, h2, _, hunion, hp1, hp2⟩ := hh
    have e1 : h1.regs r = none := by rw [hp1.1]; rfl
    have e2 : h2.regs r = none := ih (base + 8) (bs.drop 8) h2 hp2
    rw [← hunion]
    simp [PartialState.union, e1, e2]

private theorem bytesRegion_regFree (r : Reg) (base : Word) (bs : List (BitVec 8)) :
    RegFree (bytesRegion base bs) r :=
  bytesRegionAux_regFree r _ base bs

private theorem anyBytes_regFree (r : Reg) (base : Word) (n : Nat) :
    RegFree (anyBytes base n) r := by
  rintro h ⟨bs, _, hb⟩
  exact bytesRegion_regFree r base bs h hb

private theorem sepConj_regFree {P Q : Assertion} {r : Reg}
    (hP : RegFree P r) (hQ : RegFree Q r) : RegFree (P ** Q) r := by
  rintro h ⟨h1, h2, _, hunion, hp1, hp2⟩
  rw [← hunion]
  simp [PartialState.union, hP h1 hp1, hQ h2 hp2]

/-- The `.63` entry framing owns no register. -/
theorem guestScratch_regFree (r : Reg) : RegFree guestScratch r := by
  unfold guestScratch regionScratch
  exact sepConj_regFree (anyBytes_regFree _ _ _)
    (sepConj_regFree (anyBytes_regFree _ _ _)
      (sepConj_regFree (anyBytes_regFree _ _ _)
        (sepConj_regFree (anyBytes_regFree _ _ _)
          (sepConj_regFree (anyBytes_regFree _ _ _)
            (sepConj_regFree (anyBytes_regFree _ _ _)
              (sepConj_regFree (anyBytes_regFree _ _ _)
                (anyBytes_regFree _ _ _)))))))

private theorem regOwn_regFree_ne {r1 r2 : Reg} (hne : r2 ≠ r1) :
    RegFree (regOwn r1) r2 := by
  intro h ⟨v, hv⟩
  rw [hv]
  simp [PartialState.singletonReg, hne]

/- Registers outside the measured boundary clobber set remain free in the
    repaired framing, so the generic forcing lemma can still be applied to
    such a register without pretending that `x5`/`x10`/`x17` are free. -/
private theorem guestFraming_pre_regFree_outside_clobbers
    (r : Reg) (input : Bytes) (hr5 : r ≠ .x5) (hr10 : r ≠ .x10)
    (hr17 : r ≠ .x17) :
    RegFree (guestInputAssertion input ** guestFraming.scratch) r := by
  change RegFree
    (guestInputAssertion input **
      (regOwn .x5 ** (regOwn .x10 ** (regOwn .x17 ** guestScratch)))) r
  exact sepConj_regFree
    (sepConj_regFree (bytesRegion_regFree _ _ _) (bytesRegion_regFree _ _ _))
    (sepConj_regFree (regOwn_regFree_ne hr5)
      (sepConj_regFree (regOwn_regFree_ne hr10)
        (sepConj_regFree (regOwn_regFree_ne hr17) (guestScratch_regFree r))))

/-! ## §7. A concrete machine witness for the framing defect

    The preceding forcing lemma is deliberately generic.  This smaller
    witness makes the counterexample executable in the machine model: a
    three-instruction entry/exit fragment writes `x11`, restores it for the
    clean halt ECALL, and therefore cannot satisfy a frame that omits an
    actually clobbered register when the caller owns its entry value.  It is the Lean-side witness for the
    emitted `_start` shape; it does not claim to reproduce the inherited
    3896-instruction image count. -/

private def CodeFree (P : Assertion) : Prop :=
  ∀ h, P h → ∀ a, h.code a = none

private theorem bytesRegionAux_codeFree (n : Nat) (base : Word)
    (bs : List (BitVec 8)) : CodeFree (bytesRegionAux base n bs) := by
  induction n generalizing base bs with
  | zero =>
    intro h hh a
    change h = PartialState.empty at hh
    subst h
    rfl
  | succ n ih =>
    intro h hh a
    obtain ⟨h1, h2, _, hunion, h1p, h2p⟩ := hh
    have h1none : h1.code a = none := by
      obtain ⟨h1eq, _⟩ := h1p
      rw [h1eq]
      rfl
    have h2none : h2.code a = none := ih _ _ h2 h2p a
    rw [← hunion]
    simp [PartialState.union, h1none, h2none]

private theorem bytesRegion_codeFree (base : Word) (bs : List (BitVec 8)) :
    CodeFree (bytesRegion base bs) := by
  exact bytesRegionAux_codeFree _ base bs

private theorem anyBytes_codeFree (base : Word) (n : Nat) :
    CodeFree (anyBytes base n) := by
  intro h ⟨bs, _, hbs⟩ a
  exact bytesRegion_codeFree _ _ h hbs a

private theorem sepConj_codeFree {P Q : Assertion}
    (hP : CodeFree P) (hQ : CodeFree Q) : CodeFree (P ** Q) := by
  intro h ⟨h1, h2, _, hunion, h1p, h2p⟩ a
  rw [← hunion]
  simp [PartialState.union, hP h1 h1p a, hQ h2 h2p a]

private theorem regOwn_codeFree (r : Reg) : CodeFree (regOwn r) := by
  intro h ⟨v, hv⟩ a
  rw [hv]
  rfl

private theorem guestScratch_codeFree : CodeFree guestScratch := by
  unfold guestScratch regionScratch
  exact sepConj_codeFree (anyBytes_codeFree _ _)
    (sepConj_codeFree (anyBytes_codeFree _ _)
      (sepConj_codeFree (anyBytes_codeFree _ _)
        (sepConj_codeFree (anyBytes_codeFree _ _)
          (sepConj_codeFree (anyBytes_codeFree _ _)
            (sepConj_codeFree (anyBytes_codeFree _ _)
              (sepConj_codeFree (anyBytes_codeFree _ _)
                (anyBytes_codeFree _ _)))))))

private theorem guestScratch_pcFree : guestScratch.pcFree := by
  unfold guestScratch regionScratch
  exact pcFree_sepConj (EvmAsm.Rv64.SAsm.pcFree_anyBytes _ _)
    (pcFree_sepConj (EvmAsm.Rv64.SAsm.pcFree_anyBytes _ _)
      (pcFree_sepConj (EvmAsm.Rv64.SAsm.pcFree_anyBytes _ _)
        (pcFree_sepConj (EvmAsm.Rv64.SAsm.pcFree_anyBytes _ _)
          (pcFree_sepConj (EvmAsm.Rv64.SAsm.pcFree_anyBytes _ _)
            (pcFree_sepConj (EvmAsm.Rv64.SAsm.pcFree_anyBytes _ _)
              (pcFree_sepConj (EvmAsm.Rv64.SAsm.pcFree_anyBytes _ _)
                (EvmAsm.Rv64.SAsm.pcFree_anyBytes _ _)))))))

private theorem guestFraming_pre_codeFree :
    CodeFree (guestInputAssertion [] ** guestFraming.scratch) := by
  apply sepConj_codeFree
  · unfold guestInputAssertion
    exact sepConj_codeFree (bytesRegion_codeFree _ _) (bytesRegion_codeFree _ _)
  · change CodeFree (regOwn .x5 ** (regOwn .x10 ** (regOwn .x17 ** guestScratch)))
    exact sepConj_codeFree (regOwn_codeFree .x5)
      (sepConj_codeFree (regOwn_codeFree .x10)
        (sepConj_codeFree (regOwn_codeFree .x17) guestScratch_codeFree))

def guestFraming_clobberCode : CodeReq :=
  fun a =>
    if a == GUEST_ENTRY then some (.LI .x11 256)
    else if a == GUEST_ENTRY + 4 then some (.LI .x11 0)
    else if a == GUEST_ENTRY + 8 then some .ECALL
    else none

theorem guestFraming_clobberCode_not_sound
    {execute : ExecutionSeam} :
    ¬ runStatelessGuestSound guestFraming_clobberCode 2 guestFraming execute := by
  intro h
  have henv : inputWithinResourceEnvelope [] := by
    intro si hsi
    have hdecode : deserialize_stateless_input [] = .error .missingSchemaId := by
      rfl
    rw [hdecode] at hsi
    cases hsi
  obtain ⟨hp, hP⟩ := guestFraming.scratch_sat [] (by decide)
  have hx11none : hp.regs .x11 = none :=
    guestFraming_pre_regFree_outside_clobbers .x11 [] (by decide) (by decide)
      (by decide) hp hP
  have hx0none : hp.regs .x0 = none :=
    guestFraming_pre_regFree_outside_clobbers .x0 [] (by decide) (by decide)
      (by decide) hp hP
  have hsPc : guestFraming.scratch.pcFree := by
    change (regOwn .x5 ** (regOwn .x10 ** (regOwn .x17 ** guestScratch))).pcFree
    exact pcFree_sepConj pcFree_regOwn
      (pcFree_sepConj pcFree_regOwn
        (pcFree_sepConj pcFree_regOwn guestScratch_pcFree))
  have hpcNone : hp.pc = none :=
    (pcFree_sepConj (pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _)) hsPc)
      hp hP
  have hcodeNone : ∀ a, hp.code a = none := guestFraming_pre_codeFree hp hP
  let s0 := adversarialState guestFraming_clobberCode hp GUEST_ENTRY
  let s := s0.setReg .x11 256
  have hcompat0 : hp.CompatibleWith s0 :=
    adversarialState_compat hpcNone hcodeNone (by
      intro v hv
      rw [hx0none] at hv
      cases hv)
  have hcompat : hp.CompatibleWith s := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r v hv
      by_cases hr : r = .x11
      · subst r
        rw [hx11none] at hv
        cases hv
      · change (s0.setReg .x11 256).getReg r = v
        rw [MachineState.getReg_setReg_ne s0 .x11 r 256 (Ne.symm hr)]
        exact hcompat0.1 r v hv
    · intro a v hv
      rw [MachineState.getMem_setReg]
      exact hcompat0.2.1 a v hv
    · intro a i hv
      rw [MachineState.code_setReg]
      exact hcompat0.2.2.1 a i hv
    · intro v hv
      rw [MachineState.pc_setReg]
      exact hcompat0.2.2.2.1 v hv
    · intro v hv
      rw [MachineState.publicValues_setReg]
      exact hcompat0.2.2.2.2.1 v hv
    · intro v hv
      rw [MachineState.privateInput_setReg]
      exact hcompat0.2.2.2.2.2.1 v hv
    · intro v hv
      rw [MachineState.inputBufBase_setReg]
      exact hcompat0.2.2.2.2.2.2 v hv
  have hcr : guestFraming_clobberCode.SatisfiedBy s := by
    intro a i hi
    exact hi
  have hsx11 : s.getReg .x11 = 256 := by
    exact MachineState.getReg_setReg_eq (s := s0) (r := .x11) (v := 256) (by decide)
  have hPR :
      ((guestInputAssertion [] ** guestFraming.scratch) ** (.x11 ↦ᵣ 256)).holdsFor s := by
    simpa [hsx11] using
      (holdsFor_sepConj_regIs_of_regFree
        (guestFraming_pre_regFree_outside_clobbers .x11 [] (by decide) (by decide)
          (by decide))
        hp hcompat hP)
  obtain ⟨k, hk, s', hstep, hhalt, hQR⟩ :=
    (h [] (by decide) henv) (.x11 ↦ᵣ 256) pcFree_regIs s hcr hPR rfl
  have hstep0 : step s = some ((s.setReg .x11 256).setPC (s.pc + 4)) := by
    simp [step, s, s0, adversarialState, guestFraming_clobberCode, execInstrBr]
  let s1 := (s.setReg .x11 256).setPC (s.pc + 4)
  have hstep1 : step s1 = some ((s1.setReg .x11 0).setPC (s1.pc + 4)) := by
    simp [step, s1, s, s0, adversarialState, guestFraming_clobberCode,
      MachineState.setPC, execInstrBr]
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk' with rfl | rfl | rfl
  · have hs' : s' = s := by simpa using hstep.symm
    rw [hs'] at hhalt
    simp [isHalted, hstep0] at hhalt
  · have hs' : s' = s1 := by
      have hstep' := hstep
      simp only [stepN, Option.bind] at hstep'
      rw [hstep0] at hstep'
      simpa [s1] using hstep'.symm
    rw [hs'] at hhalt
    simp [isHalted, hstep1] at hhalt
  · have hs' : s' = (s1.setReg .x11 0).setPC (s1.pc + 4) := by
      have hstep' := hstep
      simp only [stepN, Option.bind] at hstep'
      rw [hstep0] at hstep'
      simp only at hstep'
      rw [hstep1] at hstep'
      simpa using hstep'.symm
    have hsx11' : s'.getReg .x11 = 256 :=
      holdsFor_regIs.mp (holdsFor_sepConj_elim_right hQR)
    rw [hs'] at hsx11'
    simp only [MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (s := s1) (r := .x11) (v := 0) (by decide)] at hsx11'
    exact (by decide : (0 : Word) ≠ 256) hsx11'

end EvmAsm.Codegen.Proofs
